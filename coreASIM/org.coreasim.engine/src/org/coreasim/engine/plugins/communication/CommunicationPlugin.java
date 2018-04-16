/*	
 * CommunicationPlugin.java 	1.0
 * 
 * Copyright (C) 2016 Eric Rothstein, Daniel Schreckling
 *
 * Licensed under the Academic Free License version 3.0
 *   http://www.opensource.org/licenses/afl-3.0.php
 *   http://www.coreasm.org/afl-3.0.php
 *
 */
 
package org.coreasim.engine.plugins.communication;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.codehaus.jparsec.Parser;
import org.codehaus.jparsec.Parsers;
import org.coreasim.engine.CoreASIMError;
import org.coreasim.engine.VersionInfo;
import org.coreasim.engine.CoreASIMEngine.EngineMode;
import org.coreasim.engine.Specification.PolicyInfo;
import org.coreasim.engine.Specification.RuleInfo;
import org.coreasim.engine.absstorage.AgentCreationElement;
import org.coreasim.engine.absstorage.BackgroundElement;
import org.coreasim.engine.absstorage.Element;
import org.coreasim.engine.absstorage.ElementList;
import org.coreasim.engine.absstorage.FunctionElement;
import org.coreasim.engine.absstorage.Location;
import org.coreasim.engine.absstorage.MessageElement;
import org.coreasim.engine.absstorage.PluginAggregationAPI;
import org.coreasim.engine.absstorage.PluginCompositionAPI;
import org.coreasim.engine.absstorage.PolicyElement;
import org.coreasim.engine.absstorage.RuleElement;
import org.coreasim.engine.absstorage.TriggerMultiset;
import org.coreasim.engine.absstorage.UniverseElement;
import org.coreasim.engine.absstorage.UnmodifiableFunctionException;
import org.coreasim.engine.absstorage.Update;
import org.coreasim.engine.absstorage.UpdateMultiset;
import org.coreasim.engine.absstorage.PluginAggregationAPI.Flag;
import org.coreasim.engine.interpreter.ASTNode;
import org.coreasim.engine.interpreter.Interpreter;
import org.coreasim.engine.interpreter.InterpreterException;
import org.coreasim.engine.interpreter.Node;
import org.coreasim.engine.interpreter.ScannerInfo;
import org.coreasim.engine.kernel.KernelServices;
import org.coreasim.engine.parser.GrammarRule;
import org.coreasim.engine.parser.ParserTools;
import org.coreasim.engine.plugin.Aggregator;
import org.coreasim.engine.plugin.ExtensionPointPlugin;
import org.coreasim.engine.plugin.InterpreterPlugin;
import org.coreasim.engine.plugin.ParserPlugin;
import org.coreasim.engine.plugin.Plugin;
import org.coreasim.engine.plugin.PluginServiceInterface;
import org.coreasim.engine.plugin.VocabularyExtender;
import org.coreasim.engine.plugins.set.SetElement;
import org.coreasim.engine.plugins.signature.SignaturePlugin;
import org.coreasim.engine.plugins.signature.SignaturePlugin.SignaturePluginPSI;
import org.coreasim.engine.plugins.string.StringElement;

/** 
 * A plugin that extends the Input/Output plugin using communication services 
 *   
 * @author Eric Rothstein
 * 
 */
public class CommunicationPlugin extends Plugin implements 
		ParserPlugin, InterpreterPlugin, VocabularyExtender, ExtensionPointPlugin, Aggregator {

	public static final VersionInfo VERSION_INFO = new VersionInfo(0, 3, 2, "");

	public static final String PLUGIN_NAME = CommunicationPlugin.class.getSimpleName();

	/** The send rule */
	public static final String SEND_KEYWORD = "send";
	public static final String WITH_KEYWORD = "with";
	public static final String SUBJECT_KEYWORD = "subject";
	public static final String TO_KEYWORD = "to";
	public static final String MAIL_TO_ACTION = "mailToAction";
	public static final String MAIL_FROM_ACTION = "mailFromAction";
	
	/**Create agent**/
	public static final String CREATE_KEYWORD = "createASIM";
	public static final String INITIALIZED_KEYWORD = "initializedBy";
	public static final String ID_KEYWORD = "id";
	public static final String IN_KEYWORD = "in";
	public static final String PROGRAM_KEYWORD = "withProgram";
	public static final String POLICY_KEYWORD = "andPolicy";
	
	/**Destroy agent**/
	public static final String DESTROY_KEYWORD = "destroyASIM";
	
	/**Inbox and outbox**/
	public static final String OUTBOX_FUNC_NAME = "outboxOf";
	public static final Location OUTBOX_FUNC_LOC = new Location(CommunicationPlugin.OUTBOX_FUNC_NAME,
			ElementList.NO_ARGUMENT);
	public static final String[] UPDATE_ACTIONS = { MAIL_TO_ACTION, MAIL_FROM_ACTION};
	
	/** The input function */
	public static final String INBOX_FUNC_NAME = "inboxOf";
	public static final Location INBOX_FUNC_LOC = new Location(CommunicationPlugin.INBOX_FUNC_NAME, ElementList.NO_ARGUMENT);
	
	/** The getMessageValue functions */
	public static final String GET_MESSAGE_CONTENT_FUNC_NAME = "getMessageContent";
	public static final String GET_MESSAGE_SUBJECT_FUNC_NAME = "getMessageSubject";
	public static final String GET_MESSAGE_SENDER_FUNC_NAME = "getMessageSender";
	public static final String GET_MESSAGE_RECEIVER_FUNC_NAME = "getMessageReceiver";
	public static final String GET_MESSAGE_STEP_FUNC_NAME = "getMessageStep";
	private final Set<String> dependencyList;
	
	/** 
	 * List of all the messages generated in the current run. 
	 * This list will be empty if an output stream is set (i.e., {@link #outputStream} is not null). 
	 */
	public List<MessageElement> allMessages;
	
	private Map<EngineMode, Integer> sourceModes;
	private Map<EngineMode, Integer> targetModes;
	private HashSet<String> functionNames;
	private Map<String,FunctionElement> functions = null;
	
	protected Map<String, GrammarRule> parsers = null;
	protected CommunicationPSI pluginPSI;
	protected InboxFunctionElement inboxFunction;
	protected OutboxFunctionElement outboxFunction;



	private final String[] keywords = { SEND_KEYWORD, TO_KEYWORD, WITH_KEYWORD, SUBJECT_KEYWORD, CREATE_KEYWORD, INITIALIZED_KEYWORD, PROGRAM_KEYWORD, POLICY_KEYWORD, DESTROY_KEYWORD};
	private final String[] operators = { };

	private String signature;
	
	/**
	 * 
	 */
	public CommunicationPlugin() {
		super();
		dependencyList = new HashSet<String>();
		dependencyList.add("StringPlugin");
		dependencyList.add("IOPlugin");
		pluginPSI = new CommunicationPSI();

		functionNames = new HashSet<String>();
		functionNames.add(INBOX_FUNC_NAME);
		functionNames.add(OUTBOX_FUNC_NAME);
		functionNames.add(GET_MESSAGE_CONTENT_FUNC_NAME);
		functionNames.add(GET_MESSAGE_SENDER_FUNC_NAME);
		functionNames.add(GET_MESSAGE_RECEIVER_FUNC_NAME);
		functionNames.add(GET_MESSAGE_SUBJECT_FUNC_NAME);
		functionNames.add(GET_MESSAGE_STEP_FUNC_NAME);
	}


	public String[] getKeywords() {
		return keywords;
	}

	public String[] getOperators() {
		return operators;
	}

	/* (non-Javadoc)
	 * @see org.coreasm.engine.plugin.Plugin#initialize()
	 */
	@Override
	public void initialize() {
		inboxFunction = new InboxFunctionElement(capi);
		outboxFunction = new OutboxFunctionElement();
		allMessages = new ArrayList<MessageElement>();
		pluginPSI = new CommunicationPSI();
		sourceModes = new HashMap<EngineMode, Integer>();
		sourceModes.put(EngineMode.emAggregation, ExtensionPointPlugin.DEFAULT_PRIORITY);
		targetModes = new HashMap<EngineMode, Integer>();
		targetModes.put(EngineMode.emStepSucceeded, ExtensionPointPlugin.DEFAULT_PRIORITY);
		targetModes.put(EngineMode.emInitializingState, ExtensionPointPlugin.DEFAULT_PRIORITY);
	}

	public Set<Parser<? extends Object>> getLexers() {
		return Collections.emptySet();
	}

	/**
	 * @return <code>null</code>
	 */
	public Parser<Node> getParser(String nonterminal) {
		return null;
	}

	public Map<String, GrammarRule> getParsers() {
		if (parsers == null) {
			parsers = new HashMap<String, GrammarRule>();
			KernelServices kernel = (KernelServices)capi.getPlugin("Kernel").getPluginInterface();
			
			Parser<Node> termParser = kernel.getTermParser();
			
			ParserTools parserTools = ParserTools.getInstance(capi);

			Parser<Node> sendToParser = Parsers.array(
					new Parser[] {
							parserTools.getKeywParser(SEND_KEYWORD, PLUGIN_NAME),
							termParser,
							parserTools.getKeywParser(TO_KEYWORD, PLUGIN_NAME),
							termParser,
							parserTools.getKeywParser(WITH_KEYWORD, PLUGIN_NAME),
							parserTools.getKeywParser(SUBJECT_KEYWORD, PLUGIN_NAME),
							termParser
					}).map(
							//This should be the parser of the SendTo rule
							new org.codehaus.jparsec.functors.Map<Object[], Node>() {
						public Node map(Object[] vals) {	
							
							Node node = new SendToRuleNode(((Node) vals[0]).getScannerInfo());
							node.addChild((Node) vals[0]);
							node.addChild("alpha", (Node) vals[1]);
							node.addChild((Node) vals[2]);
							node.addChild("beta", (Node) vals[3]);	
							node.addChild((Node) vals[4]);
							node.addChild((Node) vals[5]);
							node.addChild("gamma", (Node) vals[6]);	
							return node;
						}
					});


			parsers.put("SendToRule",
					new GrammarRule("SendToRule", "'send' Term 'to' Term 'with' 'subject' Term", sendToParser, PLUGIN_NAME));
			
			Parser<Node> createAgentParser = Parsers.array(
					new Parser[] {
							parserTools.getKeywParser(CREATE_KEYWORD, PLUGIN_NAME),
							termParser.optional(),
							parserTools.getKeywParser(INITIALIZED_KEYWORD, PLUGIN_NAME),
							termParser,
							parserTools.getKeywParser(PROGRAM_KEYWORD, PLUGIN_NAME),
							termParser,
							parserTools.getKeywParser(POLICY_KEYWORD, PLUGIN_NAME),
							termParser,	
							parserTools.getKeywParser(IN_KEYWORD, PLUGIN_NAME),
							termParser
					}).map(
							//This should be the parser of the SendTo rule
							new CreateAgentParseMap()); 

			parsers.put("CreateAgentRule",
					new GrammarRule("CreateAgentRule", "'createASIM' (Term)? 'initializedBy' Term 'withProgram' Term 'andPolicy' Term 'in' Location", createAgentParser, PLUGIN_NAME));
			
			Parser<Node> destroyAgentParser = Parsers.array(
					new Parser[] {
							parserTools.getKeywParser(DESTROY_KEYWORD, PLUGIN_NAME),
							termParser
					}).map(
							//This should be the parser of the SendTo rule
							new DestroyAgentParseMap()); 

			parsers.put("DestroyAgentRule",
					new GrammarRule("DestroyAgentRule", "'destroyASIM' Term", destroyAgentParser, PLUGIN_NAME));
			
			
			Parser<Node> communicationRuleParser = Parsers.or(sendToParser,createAgentParser, destroyAgentParser);
			parsers.put("Rule",new GrammarRule("CommunicationRule", "SendToRule | CreateAgentRule | DestroyAgentRule", communicationRuleParser, PLUGIN_NAME));
		}

		return parsers;
	}

	public ASTNode interpret(Interpreter interpreter, ASTNode pos) throws InterpreterException {
		// SendTo Rule
		if (pos instanceof SendToRuleNode) {
			return interpretSendTo(interpreter, (SendToRuleNode)pos); 
		}
		// CreateAgent Rule
		if (pos instanceof CreateAgentRuleNode) {
			return interpretCreateAgent(interpreter, (CreateAgentRuleNode)pos); 
		}
		// DestroyAgent Rule
				if (pos instanceof DestroyAgentRuleNode) {
					return interpretDestroyAgent(interpreter, (DestroyAgentRuleNode)pos); 
				}
		return pos;
	}
	
	/*
	 * Interprets the create agent rule.
	 */
	private ASTNode interpretCreateAgent(Interpreter interpreter, CreateAgentRuleNode pos) {
		if( pos.getAgentName()!= null)
		{
			if (!pos.getAgentName().isEvaluated()) {
				return pos.getAgentName();
			}
		}
		if (!pos.getAgentInit().isEvaluated()) {
			return pos.getAgentInit();
		} 
		if (!pos.getAgentProgram().isEvaluated()) {
			return pos.getAgentProgram();
		} 
		if (!pos.getAgentPolicy().isEvaluated()) {
			return pos.getAgentPolicy();
		} 
		if (!pos.getAgentLocation().isEvaluated()) {
			return pos.getAgentLocation();
		} 
		else{
			
			try {
				//System.out.println("Signaturessss!!! "+extractSignature());
				
				AgentCreationElement ace = new AgentCreationElement(new StringElement((pos.getAgentName()!= null)?pos.getAgentName().toString():""),pos.getAgentInit().getValue(),pos.getAgentProgram().getValue(), pos.getAgentPolicy().getValue(), extractSignature() ,pos.getAgentLocation().getLocation(),pos.getScannerInfo());
				capi.getAgentsToCreate().put(pos.getAgentLocation().getLocation().toString(), ace);
				pos.setNode(
						null, 
						new UpdateMultiset(), 
						new TriggerMultiset(),
						null);
				return pos;
			} catch (Throwable e) {
				capi.error(e);
			}
		}
		return pos;
	}


	private String extractSignature() {
	if (signature == null) 
	{
		StringBuilder sb = new StringBuilder();
		sb.append(((SignaturePluginPSI)capi.getPluginInterface(SignaturePlugin.PLUGIN_NAME)).getDerivedFunctionsDefinitions());
		//sb.append("\n");
		Set<RuleInfo> definedRules = capi.getSpec().getDefinedRules();
		
		for (RuleInfo ruleInfo : definedRules)
		{
			sb.append(" rule ");
			sb.append(ruleInfo.ruleElement.getName());
			if (ruleInfo.ruleElement.getParam().size() > 0) {
				sb.append("(");
				int i = 0;
				for (; i < ruleInfo.ruleElement.getParam().size() - 1; i++) {
					sb.append(ruleInfo.ruleElement.getParam().get(i));
					sb.append(",");
				}
				sb.append(ruleInfo.ruleElement.getParam().get(i));
				sb.append(")");
			}
			sb.append(" = ");
			sb.append(ruleInfo.ruleElement.getBody().unparseTree());
			//sb.append("\n");
			
		}
		
		Set<PolicyInfo> definedPolicies = capi.getSpec().getDefinedPolicies();
		
		for (PolicyInfo policyInfo : definedPolicies)
		{
			sb.append(" policy ");
			sb.append(policyInfo.policyElement.getName());
			if (policyInfo.policyElement.getParam().size() > 0) {
				sb.append("(");
				int i = 0;
				for (; i < policyInfo.policyElement.getParam().size() - 1; i++) {
					sb.append(policyInfo.policyElement.getParam().get(i));
					sb.append(",");
				}
				sb.append(policyInfo.policyElement.getParam().get(i));
				sb.append(")");
			}
			sb.append(" = ");
			sb.append(policyInfo.policyElement.getBody().unparseTree());
			//sb.append("\n");
			signature = sb.toString();
		}
	}
		return signature;
	}
	
	private ASTNode interpretDestroyAgent(Interpreter interpreter, DestroyAgentRuleNode pos) {
		if (!pos.getAgentName().isEvaluated()) {
				return pos.getAgentName();
		}
		else{
				capi.getAgentsToDestroy().add(pos.getAgentName().getValue().toString());
				pos.setNode(
						null, 
						new UpdateMultiset(), 
						new TriggerMultiset(),
						null);
				return pos;
		}
	}


	/*
	 * Interprets the Send to rule.
	 */
	private ASTNode interpretSendTo(Interpreter interpreter, SendToRuleNode pos) throws InterpreterException {
		if (!pos.getMessage().isEvaluated()) {
			return pos.getMessage();
		} 
		if (!pos.getAddress().isEvaluated()) {
			return pos.getAddress();
		} 
		if (!pos.getSubject().isEvaluated()) {
			return pos.getSubject();
		} 
		else {
			//This thing is creating two updates: one for the outbox and one for the inbox. It is not 
			// pretty, but it should work.
			pos.setNode(
					null, 
					new UpdateMultiset(
							new Update(
									OUTBOX_FUNC_LOC,
									new MessageElement(interpreter.getSelf().toString(), pos.getMessage().getValue(), pos.getAddress().getValue().toString(), pos.getSubject().getValue().toString(),capi.getStepCount(), pos.getMessage().getValue().getClass().getSimpleName()),
									MAIL_TO_ACTION,
									interpreter.getSelf(),
									pos.getScannerInfo()
									)), 
					null,
					null);
		}
		return pos;
	}
	
	/**
	 * Returns a set containing the following functions:
	 * <ul>
	 * <li><i>output</i></li>
	 * </ul>
	 */
	public Map<String,FunctionElement> getFunctions() {
		if (functions == null) {
			functions = new HashMap<String,FunctionElement>();
			if(inboxFunction == null)
				inboxFunction = new InboxFunctionElement(capi);
			if(outboxFunction == null)
				outboxFunction = new OutboxFunctionElement();
			functions.put(OUTBOX_FUNC_NAME, outboxFunction);
			functions.put(INBOX_FUNC_NAME, inboxFunction);
			functions.put(GET_MESSAGE_CONTENT_FUNC_NAME, new GetMessageContentFunctionElement());
			functions.put(GET_MESSAGE_SUBJECT_FUNC_NAME, new GetMessageSubjectFunctionElement());
			functions.put(GET_MESSAGE_SENDER_FUNC_NAME, new GetMessageSenderFunctionElement());
			functions.put(GET_MESSAGE_RECEIVER_FUNC_NAME, new GetMessageReceiverFunctionElement());
			functions.put(GET_MESSAGE_STEP_FUNC_NAME, new GetMessageStepFunctionElement());
		}
		return functions;
	}

	public Map<String,UniverseElement> getUniverses() {
		return Collections.emptyMap();
	}

	public Map<String,BackgroundElement> getBackgrounds() {
		return Collections.emptyMap();
	}

	/* (non-Javadoc)
	 * @see org.coreasm.engine.plugin.Plugin#getPluginInterface()
	 */
	@Override
	public PluginServiceInterface getPluginInterface() {
		return pluginPSI;
	}

	/* (non-Javadoc)
	 * @see org.coreasm.engine.plugin.Plugin#getDependencyNames()
	 */
	@Override
	public Set<String> getDependencyNames() {
		return this.dependencyList;
	}

	/**
	 * Write updates to files and print updates on the console.
	 * 
	 * @param source
	 * @param target
	 * @throws UnmodifiableFunctionException
	 */
	public void fireOnModeTransition(EngineMode source, EngineMode target) throws UnmodifiableFunctionException {
		//on initialization clear output messages
		if (EngineMode.emInitializingState.equals(target))
			allMessages.clear();
		//aggregate and compose updates for print to console and print (in)to file
		if (source.equals(EngineMode.emAggregation) && target.equals(EngineMode.emStepSucceeded)) {
		//	outboxManagement();
		//	inboxManagement();
			//FIXME Hook left here because we may want to do things inbetween steps
		}
	}

	/**
	 * Print the value of the print location to the outputSteam which depends on the user interface of CoreASM, i.e. EngineDriver
	 */
	private void outboxManagement() {
		try {
			FunctionElement outboxFunction = capi.getStorage().getFunction(CommunicationPlugin.OUTBOX_FUNC_NAME);
			Element value =  outboxFunction.getValue(OUTBOX_FUNC_LOC.args);
			SetElement msgs;
			if (value instanceof SetElement)
			{	
				msgs = (SetElement) value;
				for(Element e:  msgs.getSet())
				{	if(e instanceof MessageElement)
						allMessages.add((MessageElement) e);
				}
				outboxFunction.setValue(OUTBOX_FUNC_LOC.args, msgs);
			}
			
		}
		catch (UnmodifiableFunctionException e) {
			// Should not happen
			throw new CoreASIMError("Outbox function is unmodifiable.");
		}
	}
	
	/**
	 * Print the value of the print location to the outputSteam which depends on the user interface of CoreASM, i.e. EngineDriver
	 */
	private void inboxManagement() {
		try {
			FunctionElement inboxFunction = capi.getStorage().getFunction(CommunicationPlugin.INBOX_FUNC_NAME);
			Element value =  inboxFunction.getValue(INBOX_FUNC_LOC.args);
			//TODO BSL here is where we can connect the commlibrary to provide some set of updates...
//			if (outputStream == null)
//				for(Element e: msgs.getSet())
//					if(e instanceof MessageElement)
//						allMessages.add((MessageElement) e);
//			outputStream.print(msgs);
			//TODO BSL Here is where we determine whether we want to reset the outbox or not, or if we want to distribute 
			//the outbox the different agents.... maybe it is better than filtering the global outbox
			if (value instanceof SetElement)
				inboxFunction.setValue(INBOX_FUNC_LOC.args, value);
		}
		catch (UnmodifiableFunctionException e) {
			// Should not happen
			throw new CoreASIMError("inbox function is unmodifiable.");
		}
	}

	public Map<EngineMode, Integer> getSourceModes() {
		return sourceModes;
	}

	public Map<EngineMode, Integer> getTargetModes() {
		return targetModes;
	}

	public Set<String> getBackgroundNames() {
		return Collections.emptySet();
	}

	public Set<String> getFunctionNames() {
		return functionNames;
	}

	public Set<String> getUniverseNames() {
		return Collections.emptySet();
	}

	public VersionInfo getVersionInfo() {
		return VERSION_INFO;
	}

	public void aggregateUpdates(PluginAggregationAPI pluginAgg) {
		synchronized (pluginAgg) 
		{
			aggregateOutbox(pluginAgg);
		}
	}



	/**
	 * Aggregate updates for the outbox location.
	 * @param pluginAgg
	 */
	public void aggregateOutbox(PluginAggregationAPI pluginAgg) {
        // System.out.println("[Thread "+Thread.currentThread().getName()+"]: >> aggregateOutbox()");
        
        // all locations on which contain print actions
        Set<Location> locsToAggregate = pluginAgg.getLocsWithAnyAction(MAIL_TO_ACTION);
        Set<Element> contributingAgents = new HashSet<Element>();
        Set<ScannerInfo> contributingNodes = new HashSet<ScannerInfo>();
        
        // for all locations to aggregate
        for (Location l : locsToAggregate) {
            if (l.equals(OUTBOX_FUNC_LOC)) {
                Set<MessageElement> aggregatedOutbox = new HashSet<MessageElement>();
                //Regular updates should NOT affect this location!
                // if regular update affects this location
                if (pluginAgg.regularUpdatesAffectsLoc(l)) {
                    pluginAgg.handleInconsistentAggregationOnLocation(l, this);
                }
                else {
                    for (Update update : pluginAgg.getLocUpdates(l)) {
                        if (update.action.equals(MAIL_TO_ACTION)) {
                            aggregatedOutbox.add((MessageElement) update.value);
                            // flag update aggregation as successful for this update
                            pluginAgg.flagUpdate(update, Flag.SUCCESSFUL, this);
                            contributingAgents.addAll(update.agents);
                            contributingNodes.addAll(update.sources);
                        }
                    }
                }
                
                /* for(MessageElement me : aggregatedOutbox)
                   System.out.println("AGG> "+me); */
                
                outboxFunction.setValue(OUTBOX_FUNC_LOC.args, new SetElement(aggregatedOutbox));
                break;
            }
        }
        // System.out.println("[Thread "+Thread.currentThread().getName()+"]: aggregateOutbox() >>>");
	}
	
	/**
	 * Aggregate updates for the inbox location.
	 * @param pluginAgg
	 */
	public synchronized void aggregateInbox(PluginAggregationAPI pluginAgg) {
		// all locations on which contain print actions
		Set<Location> locsToAggregate = pluginAgg.getLocsWithAnyAction(MAIL_FROM_ACTION);
		Set<Element> contributingAgents = new HashSet<Element>();
		Set<ScannerInfo> contributingNodes = new HashSet<ScannerInfo>();

		// for all locations to aggregate
		for (Location l : locsToAggregate) {
			if (l.equals(INBOX_FUNC_LOC)) {
				Set<MessageElement> aggregatedInbox = new HashSet<MessageElement>();
				//Regular updates should NOT affect this location!
				// if regular update affects this location
				if (pluginAgg.regularUpdatesAffectsLoc(l)) {
					pluginAgg.handleInconsistentAggregationOnLocation(l, this);
				}
				else {
					for (Update update : pluginAgg.getLocUpdates(l)) {
						if (update.action.equals(MAIL_FROM_ACTION)) {
							aggregatedInbox.add((MessageElement) update.value);
							// flag update aggregation as successful for this update
							pluginAgg.flagUpdate(update, Flag.SUCCESSFUL, this);
							contributingAgents.addAll(update.agents);
							contributingNodes.addAll(update.sources);
						}
					}
				}
				inboxFunction.setValue(INBOX_FUNC_LOC.args, new SetElement(aggregatedInbox));
			}
		}
	}

	@Override
	public String[] getUpdateActions() {
		return UPDATE_ACTIONS;
	}

	public Set<String> getRuleNames() {
		return Collections.emptySet();
	}

	public Map<String, RuleElement> getRules() {
		return null;
	}

	@Override
	public Map<String, PolicyElement> getPolicies() {
		return Collections.emptyMap();
	}

	@Override
	public Set<String> getPolicyNames() {
		return Collections.emptySet();
	}


	@Override
	public void compose(PluginCompositionAPI compAPI) {
		// TODO Auto-generated method stub
		
	}
	
	public class CommunicationPSI implements PluginServiceInterface {
		
		public void updateInboxLocation(Set<MessageElement> inbox)
		{
			synchronized(pluginPSI)
			{
				inboxFunction.setValue(INBOX_FUNC_LOC.args, new SetElement(inbox));
			}
		}
		
		public Set<MessageElement> collectOutgoingMessages() 
		{
			synchronized(outboxFunction)
			{
                // System.out.println("[Thread "+Thread.currentThread().getName()+"]: >> collectOutgoingMessages()");
            
                Set<MessageElement> msgs = outboxFunction.getMessages();

                outboxFunction.setValue(OUTBOX_FUNC_LOC.args, new SetElement());

                /* for(MessageElement m : msgs) 
                    System.out.println("OUTBOX m2> "+m);
                    System.out.println("[Thread "+Thread.currentThread().getName()+"]: collectOutgoingMessages() >>");*/
                return msgs;
			}
		}

		public void clearOutboxLocation() 
		{
			synchronized(outboxFunction)
			{
                outboxFunction.setValue(OUTBOX_FUNC_LOC.args, new SetElement());
            }
		}
		
	}
	/*
	 * TODO BSL: 
	 * 1) Describe functions get sender, get receiver, get message
	 * 2) Enrich message format? What can we send over the communication plugin?
	 */
	public static class CreateAgentParseMap //extends ParseMapN<Node> {
	extends ParserTools.ArrayParseMap {

		String nextChildName = "alpha";
		
		public CreateAgentParseMap() {
			super(PLUGIN_NAME);
		}

		public Node map(Object[] vals) {
			nextChildName = "alpha";
            Node node = new CreateAgentRuleNode(((Node)vals[0]).getScannerInfo());
            addChildren(node, vals);
			return node;
		}

		@Override
		public void addChild(Node parent, Node child) {
			if (child instanceof ASTNode)
				parent.addChild(nextChildName, child);
			else {
				String token = child.getToken();
		        if (token.equals(CREATE_KEYWORD))
		        	nextChildName = "id";
		        else if (token.equals(INITIALIZED_KEYWORD))
	        		nextChildName = "init";
		        else if (token.equals(PROGRAM_KEYWORD))
		        	nextChildName = "program";
		        else if (token.equals("in"))
		        	nextChildName = "location";
		        else if (token.equals(POLICY_KEYWORD))
		        	nextChildName = "policy";
				super.addChild(parent, child);
			}
		}
		
	}
	
	public static class DestroyAgentParseMap //extends ParseMapN<Node> {
	extends ParserTools.ArrayParseMap {

		String nextChildName = "alpha";
		
		public DestroyAgentParseMap() {
			super(PLUGIN_NAME);
		}

		public Node map(Object[] vals) {
			nextChildName = "alpha";
            Node node = new DestroyAgentRuleNode(((Node)vals[0]).getScannerInfo());
            addChildren(node, vals);
			return node;
		}

		@Override
		public void addChild(Node parent, Node child) {
			if (child instanceof ASTNode)
				parent.addChild(nextChildName, child);
			else {
				String token = child.getToken();
		        if (token.equals(DESTROY_KEYWORD))
		        	nextChildName = "id";
				super.addChild(parent, child);
			}
		}
		
	}
}
