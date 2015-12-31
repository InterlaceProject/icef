/*	
 * SchedulePrimitive.java 	1.0 	$Revision: 243 $
 * 
 * Copyright (C) 2006-2007 Roozbeh Farahbod
 *
 * Last modified by $Author: rfarahbod $ on $Date: 2011-03-29 02:05:21 +0200 (Di, 29 Mrz 2011) $.
 *
 * Licensed under the Academic Free License version 3.0
 *   http://www.opensource.org/licenses/afl-3.0.php
 *   http://www.coreasm.org/afl-3.0.php
 *
 */
 
package org.coreasm.engine.kernel;

import org.coreasm.engine.interpreter.ASTNode;
import org.coreasm.engine.interpreter.Node;
import org.coreasm.engine.interpreter.ScannerInfo;

/** 
 * Update rule node.
 *   
 * @author  Roozbeh Farahbod
 * 
 */
public class SchedulePrimitiveNode extends ASTNode {

	private static final long serialVersionUID = 1L;

	public SchedulePrimitiveNode(SchedulePrimitiveNode node) {
		super(node);
	}
	
	public SchedulePrimitiveNode(ScannerInfo info) {
		super(null,
				ASTNode.POLICY_CLASS,
				"SchedulePrimitive",
				null,
				info
				);
	}
	
	/**
	 * @return the LHS node of the assignment
	 */
	public Node getAgent() {
		return this.getChildNode("alpha");
	}

}
