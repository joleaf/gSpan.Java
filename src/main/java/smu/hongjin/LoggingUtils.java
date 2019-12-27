package smu.hongjin;

import java.util.HashSet;
import java.util.Set;

public class LoggingUtils {

	public static Set<String> logged = new HashSet<>();
	
	public static void logOnce(String log) {
		
		if (!logged.contains(log)) {
			System.out.println(log);
			logged.add(log);
		}
	}
	
}
