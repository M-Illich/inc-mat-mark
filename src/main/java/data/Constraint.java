package data;

import java.util.LinkedList;

/**
 * Class for constraints of Datalog rules, e.g., comparison between values etc.
 */
public class Constraint {
	
	String stringForm;
	
	public Constraint(String constraint) {
		this.stringForm = constraint;
	}
	
	// TODO
	
	
	public String toString() {
		return stringForm;
	}

}
