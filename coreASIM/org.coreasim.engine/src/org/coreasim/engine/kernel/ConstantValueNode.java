/*
 * ConstantValueNode	1.0
 *  
 * Copyright (C) 2006-2016 The CoreASM Team
 * Licensed under the Academic Free License version 3.0
 *   http://www.opensource.org/licenses/afl-3.0.php
 *   http://www.coreasm.org/afl-3.0.php
 * 
 * This file contains source code developed by the European FP7 research project BIOMICS (Grant no. 318202)
 * Copyright (C) 2016 Daniel Schreckling, Eric Rothstein (BIOMICS)
 * Licensed under the Academic Free License version 3.0 
 *   http://www.opensource.org/licenses/afl-3.0.php
 *
 */
package org.coreasim.engine.kernel;

import org.coreasim.engine.CoreASIMError;
import org.coreasim.engine.absstorage.Element;
import org.coreasim.engine.absstorage.Location;
import org.coreasim.engine.absstorage.TriggerMultiset;
import org.coreasim.engine.absstorage.UpdateMultiset;
import org.coreasim.engine.interpreter.ASTNode;
import org.coreasim.engine.interpreter.ScannerInfo;

/**
 * A node holding a constant value that can be used to replace ASTNodes with constant values.
 * @author Michael Stegmaier
 *
 */
public class ConstantValueNode extends ASTNode {
	private static final long serialVersionUID = 1L;

	public ConstantValueNode(ConstantValueNode node) {
		super(node);
		setValue(node.getValue());
	}
	
	public ConstantValueNode(ScannerInfo info, Element value) {
		super(Kernel.PLUGIN_NAME, ASTNode.EXPRESSION_CLASS, "", null, info);
		setValue(value);
	}
	
	public void setValue(Element value) {
		if (value == null)
			throw new CoreASIMError("Constant value must not be null", this);
		super.setNode(null, new UpdateMultiset(), new TriggerMultiset(), value);
	}
	
	@Override
	public void setNode(Location loc, UpdateMultiset updates, TriggerMultiset triggers, Element value) {
	}
}
