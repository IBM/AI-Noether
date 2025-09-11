import subprocess
import os

def abductive_inference(variables, measured_variables, non_measured_variables, remaining_axioms, q, filename, removed_axioms):
    # Macaulay2 executable path
    macaulay2_path = "/opt/homebrew/bin/M2"

    # Construct the Macaulay2 script
    macaulay2_script = f"""
    needsPackage("PrimaryDecomposition", Reload => true)

    -- Define the ring
    R = QQ[{','.join(variables)}, MonomialOrder => Lex];
    print ("Ring defined: " | toString R);

    -- Target polynomial
    q = {q};
    print ("Target polynomial defined: " | toString q);

    -- Remaining axioms (renamed)
    remainingAxioms = toList([{','.join(remaining_axioms)}]);
    print ("Remaining axioms defined: " | toString remainingAxioms);

    -- Removed axioms
    removedAxioms = toList([{','.join(removed_axioms)}]);
    print ("Removed axioms defined: " | toString removedAxioms);

    -- Measured and non-measured vars
    measuredVariables = toList([{','.join(measured_variables)}]);
    nonMeasuredVariables = toList([{','.join(non_measured_variables)}]);

    -- Ideal from remaining axioms and q
    I = ideal(append(remainingAxioms, q));
    print ("Ideal defined: " | toString I);

    PD = primaryDecomposition I;
    print ("Primary decomposition computed");

    -- Checks
    isInIdeal = (poly, base) -> (
        M = ideal(base);
        G = gens gb M;
        return poly % ideal(G) == 0;
    );

    isInGB = (q, combo) -> (
        M = ideal(join(remainingAxioms, combo));
        eliminatedIdeal = eliminate(nonMeasuredVariables, M);
        GBproj = gens gb eliminatedIdeal;
        result = toList apply(flatten entries GBproj, g -> g == q);
        return member(true, result);
    );

    f = openOut "decomposition_analysis.txt"
    f << "Removed Axioms:" << endl;
    scan(removedAxioms, a -> f << toString a << endl);
    f << "Remaining Axioms:" << endl;
    scan(remainingAxioms, a -> f << toString a << endl);
    f << "Target Polynomial q:" << endl;
    f << toString q << endl << endl;
    f << "Primary Decomposition:" << endl;
    scan(PD, J -> f << toString J << endl << endl);

    savedCombos = {{}};
    strongCandidates = {{}};
    n = #removedAxioms;

    scan(PD, J -> (
        f << "Ideal: " << toString J << endl;
        idealGens = flatten entries gens J;
        idealGensList = toList idealGens;
        f << "  Found " << toString(#idealGensList) << " generators in ideal" << endl;

        combos = flatten for i from 1 to n list subsets(idealGensList, i);
        f << "  Testing " << toString(#combos) << " combinations" << endl;
        scan(combos, combo -> (
            f << "  Trying combination: " << toString combo << endl;

            -- Filter out polynomials already implied by remaining axioms
            filteredCombo = select(combo, p -> not isInIdeal(p, remainingAxioms));
            f << "    Filtered combo: " << toString filteredCombo << endl;

            if #filteredCombo == 0 then (
                f << "    Skipping: All combo elements already implied" << endl;
            ) else if isInIdeal(q, join(remainingAxioms, filteredCombo)) then (
                f << "    Filtered combo implies q" << endl;
                if not member(filteredCombo, savedCombos) then (
                    filteredCombo = sort filteredCombo;
                    savedCombos = append(savedCombos, filteredCombo);
                );
                if isInGB(q, filteredCombo) then (
                    f << "    Filtered combo is a strong candidate" << endl;
                    if not member(filteredCombo, strongCandidates) then (
                        strongCandidates = append(strongCandidates, filteredCombo);
                    );
                );
            ) else (
                f << "    Filtered combo does not imply q" << endl;
            );
        ));

    ));

    f << "Saved Polynomials:" << endl;
    scan(savedCombos, g -> f << toString g << endl);
    f << "Strong Candidates:" << endl;
    scan(strongCandidates, g -> f << toString g << endl);
    close f;
    """


    # Write the Macaulay2 script to a temporary file
    script_path = "temp_script.m2"
    with open(script_path, "w") as file:
        file.write(macaulay2_script)

    # Call Macaulay2 with the script
    result = subprocess.run([macaulay2_path, "--script", script_path], capture_output=False, text=True)

    # Remove the temporary script file
    os.remove(script_path)

    # Print the output from Macaulay2
    print("Output from Macaulay2:")
    print(result.stdout)

    # Print any errors
    if result.stderr:
        print("Errors:")
        print(result.stderr)

    # Read and return the contents of the saved file
    try:
        with open("decomposition_analysis.txt", "r") as file:
            os.rename("decomposition_analysis.txt", filename)
            return file.read()
    except FileNotFoundError:
        return "Error: The file 'decomposition_analysis.txt' was not found."
    except IOError as e:
        return f"Error reading the file: {e}"

def projection(variables, axioms, measured_variables, non_measured_variables, filename):
    # Macaulay2 executable path
    macaulay2_path = "/opt/homebrew/bin/M2"

    # Construct the Macaulay2 script
    macaulay2_script = f"""
    -- Define the ring and ideal
    R = QQ[{','.join(variables)}, MonomialOrder => Lex];
    print("Ring defined: " | toString R);

    -- Defining the axioms
    axioms = toList([{','.join(axioms)}]);
    print("Axioms defined: " | toString axioms);

    -- Defining the measured variables
    measuredVariables = toList([{','.join(measured_variables)}]);
    print("Measured variables defined: " | toString measuredVariables);

    -- Defining the non-measured variables
    nonMeasuredVariables = toList([{','.join(non_measured_variables)}]);
    print("Non-measured variables defined: " | toString nonMeasuredVariables);

    -- Define the ideal
    I = ideal(axioms);
    print("Ideal defined: " | toString I);

    -- Compute the Gröbner basis of the ideal
    GB = gens gb I;
    print("Gröbner basis: " | toString GB);

    -- Define the Ring of Measured Variables
    Rproj = QQ[measuredVariables, MonomialOrder => Lex];
    print("Ring of Measured Variables defined: " | toString Rproj);

    -- Define the projection map
    eliminatedIdeal = eliminate(nonMeasuredVariables, I);
    print("Eliminated Ideal: " | toString eliminatedIdeal);

    -- Compute the Gröbner basis of the eliminated ideal
    GBproj = gens gb eliminatedIdeal;
    print("Gröbner basis of the eliminated ideal: " | toString GBproj);

    -- Write the results to a file
    f = openOut "projection_analysis.txt";
    f << "Gröbner basis of the ideal:" << endl;
    f << toString GB << endl << endl;
    f << "Gröbner basis of the eliminated ideal:" << endl;
    f << toString GBproj << endl;
    f << endl;

    -- Save the polynomials of the Gröbner basis of the eliminated ideal
    f << "Polynomials of the Gröbner basis of the eliminated ideal:" << endl;
    scan(flatten entries GBproj, g -> f << toString g << endl);

    close f;

    """

    # Write the Macaulay2 script to a temporary file
    script_path = "temp_script.m2"
    with open(script_path, "w") as file:
        file.write(macaulay2_script)

    # Call Macaulay2 with the script
    result = subprocess.run([macaulay2_path, "--script", script_path], capture_output=True, text=True)

    # Remove the temporary script file
    os.remove(script_path)

    # Print the output from Macaulay2
    print("Output from Macaulay2:")
    print(result.stdout)

    # Print any errors
    if result.stderr:
        print("Errors:")
        print(result.stderr)

    # Read and return the contents of the saved file
    try:
        with open("projection_analysis.txt", "r") as file:
            os.rename("projection_analysis.txt", filename)
            return file.read()
    except FileNotFoundError:
        return "Error: The file 'projection_analysis.txt' was not found."
    except IOError as e:
        return f"Error reading the file: {e}"

import subprocess
import os

def check_axiom_dimensions(variables, all_axioms, target, removed_axioms, filename="axiom_dimensions.txt"):
    """
    Compares dimensions of ideal generated by all_axioms vs all_axioms - removed_axioms,
    and also with the remaining axioms + target (discovered dimension).
    
    Args:
        variables: List of variable names
        all_axioms: List of all axiom strings
        target: Axiom string to test after removal (i.e., the discovered axiom)
        removed_axioms: List of axioms to remove (subset of all_axioms)
        filename: Output file for storing dimension results
    """
    macaulay2_path = "/opt/homebrew/bin/M2" 

    def format_axiom(axiom):
        return axiom.replace('^', '^')

    formatted_all_axioms = [format_axiom(ax) for ax in all_axioms]
    formatted_removed_axioms = [format_axiom(ax) for ax in removed_axioms]
    formatted_target = format_axiom(target)

    # Build the Macaulay2 script
    macaulay2_script = f"""
    needsPackage("PrimaryDecomposition");

    R = QQ[{','.join(variables)}, MonomialOrder => Lex];

    allAxioms = {{{','.join(formatted_all_axioms)}}};

    I = ideal(allAxioms);
    originalDim = dim I;

    remainingAxioms = allAxioms;
    {''.join([f'remainingAxioms = delete({ax}, remainingAxioms);' for ax in formatted_removed_axioms])}

    Ireduced = ideal(remainingAxioms);
    reducedDim = dim Ireduced;

    remainingWithTarget = append(remainingAxioms, {formatted_target});
    Idiscovered = ideal(remainingWithTarget);
    discoveredDim = dim Idiscovered;

    f = openOut "temp.txt";
    f << "Original dimension: " << originalDim << endl;
    f << "Reduced dimension: " << reducedDim << endl;
    f << "Discovered dimension: " << discoveredDim << endl;
    f << "Removed axioms: " << toString({{{', '.join(formatted_removed_axioms)}}}) << endl;
    f << "Remaining axioms: " << toString(remainingAxioms) << endl;
    f << "Target axiom: " << {formatted_target} << endl;
    close f;
    """

    script_path = "temp_dimension_script.m2"
    with open(script_path, "w") as file:
        file.write(macaulay2_script)

    result = subprocess.run([macaulay2_path, "--script", script_path], capture_output=False, text=True)
    os.remove(script_path)

    try:
        with open("temp.txt", "r") as f:
            temp_content = f.read()

        original_dim = reduced_dim = discovered_dim = None
        removed_axioms_list = []
        remaining_axioms_list = []

        for line in temp_content.split('\n'):
            if line.startswith("Original dimension:"):
                original_dim = int(line.split(':')[1].strip())
            elif line.startswith("Reduced dimension:"):
                reduced_dim = int(line.split(':')[1].strip())
            elif line.startswith("Discovered dimension:"):
                discovered_dim = int(line.split(':')[1].strip())
            elif line.startswith("Removed axioms:"):
                removed_axioms_str = line.split(':', 1)[1].strip()
                removed_axioms_list = [a.strip().strip('"') for a in removed_axioms_str[1:-1].split(',')]
            elif line.startswith("Remaining axioms:"):
                remaining_axioms_str = line.split(':', 1)[1].strip()
                remaining_axioms_list = [a.strip().strip('"') for a in remaining_axioms_str[1:-1].split(',')]

        dimensions_equal = (original_dim == discovered_dim)

        with open(filename, "a") as f:
            f.write("\n=== Dimension Analysis ===\n")
            f.write(f"Original dimension: {original_dim}\n")
            f.write(f"Removed axioms: {removed_axioms_list}\n")
            f.write(f"Remaining axioms: {remaining_axioms_list}\n")
            f.write(f"Reduced dimension: {reduced_dim}\n")
            f.write(f"Target axiom: {target}\n")
            f.write(f"Discovered dimension: {discovered_dim}\n")
            f.write(f"Original == Discovered: {original_dim == discovered_dim}\n")

        os.remove("temp.txt")

        return {
            "original_dimension": original_dim,
            "reduced_dimension": reduced_dim,
            "discovered_dimension": discovered_dim,
            "removed_axioms": removed_axioms_list,
            "remaining_axioms": remaining_axioms_list,
            "dimensions_equal": dimensions_equal
        }

    except FileNotFoundError:
        print("Error: temp.txt not found")
        return None
    except Exception as e:
        print(f"Error processing results: {e}")
        return None

