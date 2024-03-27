import re

def eliminate_implication(expression):
    # Replace implications
    expression = re.sub(
        r"([^()\s]+)\s*->\s*([^()\s]+)", r"(not \1) or (\2)", expression
    )
    return expression.strip()

def list_text_format(lst):
    '''
    remove extra spaces and remove braces
    '''
    formatted_list = []
    for item in lst:
        # Extract the desired characters using regex, remove leading/trailing spaces
        formatted_item = re.sub(r'[^\w\s]', '', item.strip())
        formatted_list.append(formatted_item)
    return formatted_list

def demorgans_law(expression):
    """
    Applies De Morgan's Law to a logical expression.

    Args:
        expression (str): The logical expression to transform.

    Returns:
        str: The transformed expression after applying De Morgan's Law.
    """

    expression = expression.lower()  # Convert to lowercase for case-insensitive handling

    # Replace logical symbols with natural language equivalents
    expression = expression.replace("¬", "not ")
    expression = expression.replace("∧", "and")

    while "not not" in expression:  # Remove double negation
        expression = expression.replace("not not", "")

    if expression.startswith("not "):  # Handle negation of a compound expression
        inner_expression = expression[4:].strip()  # Extract inner expression and remove spaces

        if "and" in inner_expression:
            # Apply De Morgan's Law for AND
            parts = list_text_format(inner_expression.split("and"))
            return f"not ({parts[0]}) or not ({parts[1]})"
        elif "or" in inner_expression:
            # Apply De Morgan's Law for OR (fix the operator)
            parts = list_text_format(inner_expression.split("or"))
            return f"not ({parts[0]}) and not ({parts[1]})"  # Use AND for OR's De Morgan's Law

    return expression  # Return original expression if not a negation

def move_negation_inwards(expression):
    while "not not" in expression:
        expression = expression.replace("¬¬", "")
    return expression

def standardize_scope(expression):
    parts = expression.split("∧")
    standardized = []
    current_var = "x"
    q = [] # quantifiers
    v = [] # variables
    for part in parts:
        if "∀" in part:
            variable = current_var
            q.append(f"∀{variable}")
            v.append(f"p({variable})")
        elif "∃" in part:
            variable = current_var
            current_var = chr(ord(current_var) + 1)
            standardized.append(f"∃{current_var}p({current_var})")
            q.append(f"∃{variable}")
            v.append(f"p({current_var})")

    total1 = " ∧ ".join(v)
    total = " ".join(q) + total1
    return total

def resolution_procedure(expression):
    expression = eliminate_implication(expression)
    expression = demorgans_law(expression)
    expression = move_negation_inwards(expression)
    expression = standardize_scope(expression)
    return expression


# Test the resolution_procedure function
expression = "∀x (p(x) ∧ q(x)) ∧ ∃y (r(y) ∧ s(y))"
result = resolution_procedure(expression)
print(result)