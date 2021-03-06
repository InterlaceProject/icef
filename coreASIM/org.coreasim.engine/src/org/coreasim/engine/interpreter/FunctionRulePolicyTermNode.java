/*	
 * FunctionRulePolicyTermNode.java 	1.1 	
 *
 * Copyright (C) 2006-2007 Roozbeh Farahbod
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
 *
 */
 
package org.coreasim.engine.interpreter;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.coreasim.engine.kernel.Kernel;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/** 
 * Wrapper around a <code>Node</code> object, to see the node as a 
 * function/rule term node.
 *   
 *  @author  Roozbeh Farahbod, Eric Rothstein
 *  
 */
public class FunctionRulePolicyTermNode extends ASTNode {

    private static final long serialVersionUID = 1L;

    private static final Logger logger = LoggerFactory.getLogger(FunctionRulePolicyTermNode.class);
    
    private ASTNode actualNode = null;

	private List<ASTNode> argsList = null;

	public FunctionRulePolicyTermNode(ScannerInfo info) {
		super(Kernel.PLUGIN_NAME,
				ASTNode.FUNCTION_RULE_POLICY_CLASS,
				Kernel.GR_FUNCTION_RULE_POLICY_TERM,
				null,
				info);
	}

    public FunctionRulePolicyTermNode(FunctionRulePolicyTermNode node) {
    	super((ASTNode)node);
   }

    protected void checkNodeValidity() {
		if (!this.getGrammarClass().equals(ASTNode.FUNCTION_RULE_POLICY_CLASS))
			throw new IllegalArgumentException("Expecting a FunctionRulePolicyTerm node.");
	}

    /**
	 * Returns <code>true</code> if this node has a list of arguments.
	 */
	public boolean hasArguments() {
		// return actualNode.getFirst().getNext() != null;
		// The above line changed to the following, which
		// is more robust and also is consistent with the spec -- Roozbeh Farahbod
		return getActualFunctionRuleNode().getChildNode("lambda") != null;
	}
	
	/**
	 * Returns the list of arguments in a <code>List</code> object.
	 * This method caches the result of its first call, assuming that
	 * the node structure does not change.
	 */
	public List<ASTNode> getArguments() {
		if (argsList == null) {
			List<Node> args = getActualFunctionRuleNode().getChildNodes("lambda");
			if (args.size() == 0)
				argsList = Collections.emptyList();
			else {
				argsList = new ArrayList<ASTNode>();
			
				for (Node n: args) 
					if (n instanceof ASTNode)
						argsList.add((ASTNode)n);
					else
						logger.warn("Bad argument node in a FunctionRulePolicyTerm!");
			}
		}

		return argsList;
	}
	
	/**
	 * Returns <code>true</code> if this function/rule term starts with a name (id).
	 */
	public boolean hasName() {
		Node name = getActualFunctionRuleNode().getChildNode("alpha");
		if (name instanceof ASTNode) 
			return ((ASTNode)name).getGrammarClass().equals(ASTNode.ID_CLASS);
		else
			return false;
	}

	/**
	 * If this function/rule term has a name, returns the name. Otherwise, returns
	 * <code>null</code>.
	 */
	public String getName() {
		if (hasName()) { 
			return getActualFunctionRuleNode().getChildNode("alpha").getToken();
		} else
			return null;
	}

	public ASTNode getActualFunctionRuleNode() {
		if (actualNode == null) {
			ASTNode cNode = this;
			while (cNode.getFirst().getGrammarClass().equals(ASTNode.FUNCTION_RULE_POLICY_CLASS)) 
				cNode = cNode.getFirst();
			actualNode = cNode; 
		}
		return actualNode;
	}
		
}
