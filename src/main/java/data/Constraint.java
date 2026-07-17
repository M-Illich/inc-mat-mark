package data;


/**
 * Class for constraints of Datalog rules, e.g., comparison between values etc.
 * 	
 */
public class Constraint {
	
	String stringForm;
	
	public Constraint(String constraint) {
		this.stringForm = constraint;
	}
	
	
	public String toString() {
		return stringForm;
	}

}
