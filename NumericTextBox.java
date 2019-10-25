/**
 * This class represents a text box for numeric values.
 * Its content is represented as an array of single digits.
 *
 * Your task is to add JML contracts for each method in this class
 * that reflect the informal descriptions in the Javadoc comments.
 *
 * Also add JML invariants for the fields "cursorPosition" and "content" that make sure that
 *
 *  - the cursorPosition is always a valid value (see comment for cursorPosition).
 *  - the content before the cursor contains only single digits
 *  - the content after the cursor is EMPTY
 *
 * Furthermore, think about which methods are pure and use the appropriate annotation.
 *
 * Hint: If you use variables for array indices in an assignable-clause,
 *       their values are evaluated in the pre-state.
 */
public class NumericTextBox
{
	public final int EMPTY = -1;

	/**
	 * The current cursor position, i.e. the position after the previously entered digit.
	 * If this is 0, then the cursor is placed at the very beginning of the text box.
	 * Note that the number of possible cursor positions is greater by one than
	 * the length of the text box.
	 */
	private /*@ spec_public @*/ int cursorPosition;

	/**
	 * This array stores the contents of the text box. At every position
	 * before the cursor, there is a valid value (i.e. a single digit).
	 * Positions after the cursor must be EMPTY.
	 */
	private /*@ spec_public @*/ int[] content;

	/**
	 * Holds the current TextBoxRenderer. This can be null, which means that there
	 * is no renderer assigned.
	 */
	private /*@ spec_public @*/ TextBoxRenderer textBoxRenderer;

	/*@ 
      private invariant 
         cursorPosition >= 0 && cursorPosition <= content.length + 1;
	@*/   

	/*@ 
      private invariant 
         \forall int i; i >= 0 && i < cursorPosition ; (\exists int n; content[i] == n);
	@*/ 

	/*@ 
      private invariant 
         \forall int i; i < content.length && i > cursorPosition ; content[i] == EMPTY;
	@*/ 

	/**
	 * Gets the currently assigned TextBoxRenderer.
	 */

	/*@ public normal_behavior
	@ ensures \result == textBoxRenderer;
	@ assignable \nothing;
	@*/
	public /*@ spec_public strictly_pure @*/ TextBoxRenderer getRenderer()
	{
		// ...
	}

	/**
	 * Sets the TextBoxRenderer used for rendering this text box.
	 * It can also be set to null, if the text box is not rendered.
	 */

	/*@ public normal_behavior
	@ ensures (textBoxRenderer == renderer || textBoxRenderer == null);
	@ assignable textBoxRenderer;
	@*/
	public void setRenderer(TextBoxRenderer renderer)
	{
		// ...
	}

	/**
	 * Checks whether a given input is a single digit (i.e. between 0 and 9).
	 *
	 * @param input The input character.
	 * @return true if the input is a single digit, false otherwise.
	 */

	/*@ public normal_behavior
	@ requires (\exist int n; n >= 0 && n < 10; n == input);
	@ ensures \result == true;
	@ assignable \nothing;
	@
	@ also
	@
	@ public normal_behaviour
	@ requires !(\exist int n; n >= 0 && n < 10; n == input);
	@ ensures \result == false;
	@ assignable \nothing;
	@*/
	/*@ spec_public strictly_pure @*/
	public /*@ spec_public strictly_pure @*/ boolean isSingleDigit(int input)
	{
		// ...
	}

	/**
	 * Clears the text box and resets the cursor to the start.
	 * Also sets the contentChanged flag of the current TextBoxRenderer, if any.
	 */

	/*@ public normal_behavior
	@ ensures cursorPosition == 0;
	@ ensures (\forall int i; i >= 0 &6 i < content.length; content[i] == EMPTY);
	@ assignable content, cursorPosition;
	@
	@ also
	@
	@ public normal_behaviour
	@ requires textBoxRenderer != null;
	@ ensures textBoxRenderer.contentChanged == true;
	@ assignable textBoxRenderer.contentChanged;
	@*/
	public void clear()
	{
		// ...
	}

	/**
	 * Enters a given input character into the text box and moves the cursor forward.
	 * If the input can be processed, the contentChanged flag of the current TextBoxRenderer (if any) is set.
	 * If an exception occurs, the TextBoxRenderer's showError flag is set instead.
	 *
	 * @param input the input character.
	 *
	 * @throws IllegalArgumentException if the input was not a single digit.
	 *
	 * @throws RuntimeException if the input was valid, but the cursor is at the end
	 *                          of the text box and no further input can be accepted.
	 */

	/*@ public normal_behavior
	@ requires isSingleDigit(input) == true;
	@ requires cursorPosition < content.length;
	@ ensures content[\old(cursorPosition)] == input:
	@ ensures cursorPosition == \old(cursorPosition) +1;
	@ ensures textBoxRenderer.contentChanged == true;
	@ assignable content[\old(cursorPosition)], cursorPosition, textBoxRenderer.contentChanged;
	@ 
	@ also
	@ 
	@ public exceptional_behaviour
	@ requires isSingleDigit(input) == false;
	@ signals_only IllegalArgumentException;
	@ signals (IllegalArgumentException) cursorPosition == \old(cursorPosition);
	@ signals (IllegalArgumentException) content[\old(cursorPosition)] == content[cursorPosition];
	@ signals (IllegalArgumentException) textBoxRenderer.contentChanged == false;
	@ signals (IllegalArgumentException) textBoxRenderer.showError = true;
	@ assignable textBoxRenderer.showError;
	@
	@ also
	@ 
	@ public exceptional_behaviour
	@ requires cursorPosition == content.length;
	@ signals_only RuntimeException;
	@ signals (RuntimeException) cursorPosition == \old(cursorPosition);
	@ signals (RuntimeException) textBoxRenderer.contentChanged == false;
	@ signals (RuntimeException) textBoxRenderer.showError = true;
	@ assignable textBoxRenderer.showError;
	@
	@*/
	public void enterCharacter(int input)
	{
		// ...
	}

	/**
	 * Deletes the most recently entered character and moves the cursor back one position.
	 * Also sets the current TextBoxRenderer's contentChanged flag (if any).
	 *
	 * @throws RuntimeException if the cursor is at the very beginning. In this case
	 *                          the showError flag of the TextBoxRenderer is set
	 *                          before the exception is thrown.
	 */

	/*@ public normal_behavior
	@ requires cursorPosition != 0;
	@ ensures content[\old(cursorPosition)] == EMPTY:
	@ ensures cursorPosition == \old(cursorPosition) - 1;
	@ ensures textBoxRenderer.contentChanged == true;
	@ assignable content[\old(cursorPosition)], cursorPosition, textBoxRenderer.contentChanged;
	@ 
	@ also
	@ 
	@ public exceptional_behaviour
	@ requires cursorPosition == 0;
	@ requires textBoxRenderer.showError = true;
	@ signals_only RuntimeException;
	@ signals (RuntimeException) cursorPosition == \old(cursorPosition);
	@ signals (RuntimeException) content[\old(cursorPosition)] == content[cursorPosition];
	@ signals (RuntimeException) textBoxRenderer.contentChanged == false;
	@ signals (RuntimeException) textBoxRenderer.showError = true;
	@
	@*/
	public void backspace()
	{
		// ...
	}
}

/**
 * This class represents a renderer that is responsible for displaying the
 * text box to the user in some way.
 */
class TextBoxRenderer
{
	/**
	 * Whether the content was changed (so the rendered text box needs a refresh).
	 */
	public boolean contentChanged = false;

	/**
	 * Whether an exception occured (which should be represented in the rendered text box).
	 */
	public boolean showError = false;
}
