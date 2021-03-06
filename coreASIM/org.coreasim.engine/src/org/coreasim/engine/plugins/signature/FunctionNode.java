/*  
 * FunctionNode.java    1.0     04-Apr-2006
 * 
 *
 * Copyright (C) 2006 George Ma
 *
 * Licensed under the Academic Free License version 3.0 
 *   http://www.opensource.org/licenses/afl-3.0.php
 *   http://www.coreasm.org/afl-3.0.php
 *
 * This file contains source code contributed by the European FP7 research project BIOMICS (Grant no. 318202)
 * Copyright (C) 2016 Daniel Schreckling, Eric Rothstein (BIOMICS) 
 *
 * Licensed under the Academic Free License version 3.0 
 *   http://www.opensource.org/licenses/afl-3.0.php
 *
 */
 
package org.coreasim.engine.plugins.signature;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.coreasim.engine.CoreASIMError;
import org.coreasim.engine.absstorage.FunctionElement.FunctionClass;
import org.coreasim.engine.interpreter.ASTNode;
import org.coreasim.engine.interpreter.FunctionRulePolicyTermNode;
import org.coreasim.engine.interpreter.ScannerInfo;
import org.coreasim.engine.plugins.chooserule.ChooseRulePlugin;
import org.coreasim.engine.plugins.number.NumberRangeNode;

// TODO There is a lot of dirt in this class! :)
/** 
 *	Node for function definitions
 *   
 *  @author  George Ma
 *  
 */
public class FunctionNode extends ASTNode {
    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    
    /**
     * Creates a new FunctionNode with the given
     * scanner information.
     */
    public FunctionNode(ScannerInfo info) {
        super(
        		SignaturePlugin.PLUGIN_NAME,
        		ASTNode.DECLARATION_CLASS,
        		"FunctionSignature",
        		null,
        		info);
    }

    public FunctionNode(FunctionNode node) {
    	super(node);
    }
    
    
    /**
     * Returns the name of the function
     * @return the name of the function
     */
    public String getName() {
        return getNameNode().getToken();
    }
    
    /**
     * Returns the node containing the name of the function
     * @return the node containing the name of the function
     */
    private ASTNode getNameNode() {
    //	System.out.println("Get Name Node: "+((ASTNode)getChildNode(SignaturePlugin.FUNCTION_CLASS)).getToken());
  		   return (ASTNode)getChildNode(SignaturePlugin.FUNCTION_ID);
    }
    
//    private ASTNode getNameNode() {
//        if (getFunctionClassHelper() != null) {
//            return getFirst().getNext();
//        }
//        
//        return getFirst();
//    }
        
    /**
     * Returns the class of the function
     * @return the class of the function
     */
    public FunctionClass getFunctionClass() {
        FunctionClass functionClass = getFunctionClassHelper();
        
        // the function class is controlled by default
        if (functionClass == null) {
            return FunctionClass.fcControlled;
        }
        return functionClass;
    }
    
    /**
     * Returns the function class if it has been specified, null
     * otherwise.
     * @return
     */
    private FunctionClass getFunctionClassHelper() {
        if (getFirst().getToken().equals("static")) {
            return FunctionClass.fcStatic;
        }
        if (getFirst().getToken().equals("monitored")) {
            return FunctionClass.fcMonitored;
        }
        if (getFirst().getToken().equals("out")) {
            return FunctionClass.fcOut;
        }
        if (getFirst().getToken().equals("derived")) {
            return FunctionClass.fcDerived;
        }
        if (getFirst().getToken().equals("controlled")) {
            return FunctionClass.fcControlled;
        }
        
        return null;
    }
         
//    /**
//     * Returns the node representing the domain
//     */
//    public ASTNode getDomainNode() {
//        return (ASTNode)getChildNode(SignaturePlugin.DOMAIN);
//    }
    
    /**
     * Returns the node representing the function domain.
     * Returns null if the function has no domain.
     */
    
    	public ASTNode getDomainNode() {
    	if (getChildNode(SignaturePlugin.FUNCTION_RANGE)!=null)
    	{
    		//System.out.println("Get Domain Node with domain "+((ASTNode)getChildNode(SignaturePlugin.FUNCTION_DOMAIN)).getToken());
    		return (ASTNode)getChildNode(SignaturePlugin.FUNCTION_DOMAIN);
    	}
    	else{
    		//System.out.println("Get Domain Node with no domain "+((ASTNode)getChildNode(SignaturePlugin.FUNCTION_RANGE)).getToken());
    		return null;
    	}
    		
    }
	//public ASTNode getDomainNode() {
	//    
	//    if ((getNameNode().getNext().getGrammarClass() != null) && 
	//        (getNameNode().getNext().getGrammarClass().equals(ASTNode.ID_CLASS)||getNameNode().getNext().getGrammarClass().equals(ASTNode.EXPRESSION_CLASS))) {
	//        return null;
	//    }
	//    
	//    return getNameNode().getNext();
	//}
    
    
    /**
     * Returns the domain of the function as a list of strings.
     * Returns null if the function has no domain.
     */
    public List<String> getDomain() {
        
        if (getDomainNode() == null) {
            return Collections.emptyList();
        }
        
        List<String> domainList = new ArrayList<String>();
        ASTNode domainElement = getDomainNode().getFirst();
        
        while (domainElement != null) {
            domainList.add(getTypeString(domainElement));
            domainElement = domainElement.getNext();
        }
        
        return domainList;
    }
        
    /**
     * Returns the range of the function (as a string).
     * @return the range of the function
     */
    public String getRange() {
        if (getDomainNode() != null) {
            return getTypeString(getDomainNode().getNext());
        }
        
        return getTypeString(getNameNode().getNext());
    }
    
    
    /**
     * Returns the node representing the condition ('with' part) of the choose rule.
     * null is returned if the choose rule has no condition.
     */

    
    /**
    * Returns the range of the function (as a string).
    * @return the range of the function
    */
   public ASTNode getRangeNode() {
	   if (getChildNode(SignaturePlugin.FUNCTION_RANGE)!=null)
	   {
		   //System.out.println("Get Range Node with domain "+((ASTNode)getChildNode(SignaturePlugin.FUNCTION_RANGE)).getToken());
		   
		   return (ASTNode)getChildNode(SignaturePlugin.FUNCTION_RANGE);
	   }
	   else
	   {
		   //System.out.println("Get Range Node without domain "+((ASTNode)getChildNode(SignaturePlugin.FUNCTION_DOMAIN)).getToken());
		   
		   return (ASTNode)getChildNode(SignaturePlugin.FUNCTION_DOMAIN);
	   }
   }
   
//   public ASTNode getRangeNode() {
//       if (getDomainNode() != null) {
//           return getDomainNode().getNext();
//       }
//       
//       return getNameNode().getNext();
//   }
   
   public ASTNode getInitNode() {
       return getRangeNode().getNext();
   }
   
   public boolean hasInitializer() {
	   return getRangeNode().
			   getNextCSTNode() != null 
			   && !"initially".
			   equals(getRangeNode().
					   getNextCSTNode().
					   getToken());
   }
   
   public List<String> getInitializerParams() {
	   if (!hasInitializer() || !(getInitNode() instanceof FunctionRulePolicyTermNode))
		   return Collections.<String>emptyList();
	   FunctionRulePolicyTermNode frNode = (FunctionRulePolicyTermNode)getInitNode();
	   List<String> params = new ArrayList<String>();
	   for (ASTNode argNode : frNode.getArguments()) {
		   if (argNode instanceof FunctionRulePolicyTermNode) {
			   FunctionRulePolicyTermNode arg = (FunctionRulePolicyTermNode)argNode;
			   params.add(arg.getName());
		   }
		   else
			   throw new CoreASIMError("Parameter must be an identifier.", argNode);
	   }
	   return params;
   }
   
   private String getTypeString(ASTNode n) {
       String ret = null;
       if (n.
    		   getGrammarClass().
    		   equals(ASTNode.ID_CLASS)) {
           ret = n.getToken();
       }
       else if (n.getGrammarClass().equals(ASTNode.EXPRESSION_CLASS)) {
           if (n instanceof NumberRangeNode) {
               NumberRangeNode nrNode = (NumberRangeNode) n;               
               ret = "NUMBER_RANGE["+getIntegerLiteral(nrNode.getStart())+":"+getIntegerLiteral(nrNode.getEnd())+"]";
           }
       }
       return ret;
   }
   
   private String getIntegerLiteral(ASTNode n) {
       String ret = "";
       if (n.getGrammarClass().equals(ASTNode.UNARY_OPERATOR_CLASS)) {
           ret = n.getToken() + n.getFirst().getToken();
       }
       else if (n.getGrammarClass().equals(ASTNode.EXPRESSION_CLASS)){
           ret = n.getToken();
       }
       return ret;
   }
}