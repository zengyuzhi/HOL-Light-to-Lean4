# LEAN4_DEFAULT_HEADER = """import Mathlib
# import Aesop

# set_option maxHeartbeats 0

# open BigOperators Real Nat Topology Rat
# """
LEAN4_DEFAULT_HEADER = """import Mathlib
import Aesop"""

SYSTEM_PROMPT = "You are a helpful assistant."

USER_PROMPT_FOR_SKETCH = """
You are an expert in formal logic and theorem proving in Lean 4, with extensive experience porting theorems from other systems (such as HOL Light). You are given a natural language excerpt of HOL Light documentation and your task is to produce a Lean 4 scaffold file that includes only the formal *statements* of relevant definitions, lemmas, and theorems.

Your Objective:
Given:
- A default Lean 4 imports
- Natural language documentation adapted from HOL Light
You must:
- Write a Lean 4 code block that:
  - Use Lean 4 syntax and conventions
  - Includes the formal *statements* of theorems, lemmas, and definitions
  - Leaves every proof body as `sorry`

Guidlines:
1. Imports:
   - Use only the provided default Lean 4 import in [Lean 4 Default Imports].
   - If necessary, include `open` to import relevant namespaces and define necessary variables and types in the beginning of the file.
2. Formal Item:
   - For each item (definition, lemma, or theorem) described in the natural language documentation, write the corresponding Lean 4 formal statement. 
   - Begin with a comment of the form `-- <HOL Light Name>` matching the label from the documentation (e.g., `-- Theorem 1`)
   - Write the corresponding `def`, `lemma`, or `theorem` header and statement
   - End the proof with `:= by sorry` indicate that the proof is incomplete.
3. Scoping and Purpose:
   - This is a **proof scaffold** meant to help Lean 4 porters complete the proofs later.
   - You are not expected to write proofs.
4. Output Format:
   - Do not include any text, explanation, or commentary outside of the code block.
   - Respond with the entire Lean 4 file wrapped in Lean 4 code block as shown below:
```lean
<Lean 4 code>
```

---
Here is the Lean 4 default imports and the documentation:

[Lean 4 Default Imports]
{imports}

[HOL-Light Documentation]
{doc}
"""

USER_PROMPT_FOR_SKETCH_REFINEMENT = """
You are an expert in formal logic and Lean 4, with extensive experience porting theorems from HOL Light into Lean 4. You are given:
- A **partial Lean 4 file** (sketch)
- Natural language documentation from HOL Light
- Lean 4 error messages produced from the current sketch

Your Task:
You must refine and correct the Lean 4 sketch by resolving any syntax or structural issues based on the Lean 4 error messages, while maintaining the intended logical structure of the sketch.

Guidlines:
1. **Error Correction**:
   - Carefully use the provided error messages to fix any syntactic, structural, or type-related issues.
   - The corrected file must parse and compile (except for the `sorry` placeholders).
2. **Preserve Existing Content**:
   - Do **not** change any theorem or definition names, types, or comments unless absolutely required to resolve the error.
   - Proof bodies must remain with comments and `sorry`.
3. **Output Formatting**:
   - Do not include any additional text, explanations, or clarifications outside of the code block.
   - Output only the **entire corrected Lean 4 file**, wrapped in a Lean code block:
 - Respond with the entire Lean 4 file wrapped in Lean 4 code block as shown below:
```lean
<Lean 4 code>
```

---
Here is the documentation, the Lean 4 sketch and error messages: 
[Documentation of HOL-Light]
{doc}

[Lean 4 Sketch (with errors)]
{sketch}

[Lean 4 Error Messages]
{errors}
"""

USER_PROMPT_FOR_FORMALIZATION = """
You are an expert in theorem proving using Lean 4, with extensive experience porting theorems from HOL Light. You are provided with:
- A Lean 4 formal statement (possibly incomplete)
- Natural language documentation adapted from HOL Light
- A list of dependencies (possibly empty)

Your Task:
Complete the **formalization** in Lean 4 using the provided documentation and dependencies, producing a valid, idiomatic Lean 4 proof or definition.

Guidlines:
1. Follow informal proof:
 - Use the HOL Light natural language documentation and its proof sketch to guide your formalization.
 - Add comments to indicate the purpose of proofs.
2. Output Formatting:
 - Do not include any additional text, explanations, or clarifications outside of the code block.
 - Respond with the entire Lean 4 wrapped in Lean 4 code block as shown below but **exclude** any lean4 import:
```lean
<Lean 4 code>
```

---
[HOL-Light Documentation]
{doc}

[Lean 4 formal statement]
{sketch}

[Dependency List]
{deps}
"""

USER_PROMPT_FOR_FORMALIZATION_REFINEMENT = """
You are an expert in theorem proving using Lean 4. Your task to correct the Lean 4 code by fixing the parts that cause errors, using the provided error messages as your guide.

Guidlines:
1. Correct All Errors
2. Output Formatting:
 - Do not include any additional text, explanations, or clarifications outside of the code block.
 - Respond with the entire Lean 4 code wrapped in Lean 4 code block as shown below but **exclude** any lean4 import:
```lean
<Lean 4 code>
```

---
Here is the Lean 4 and error messages:
[Lean 4 codes]
{codes}

[Lean 4 Error Messages]
{errors}
"""

USER_PROMPT_FOR_DEPS_EXT = """
You will be given Lean 4 codes. Your task is to extract every **definition** and **theorem/lemma** declaration from the code and return them in a structured JSON list.

Guidelines:
- Ignore any non-definition/theorem content such as `import`, `open`, `namespace`, `section`.
- For each Lean 4 `def`, `theorem`, or `lemma`, locate the corresponding HOL Light name that appears immediately above it as a comment: "-- HOL Light Name". 
- If there is no corresponding no comment showing HOL Light name above the formal item, use the name in the formal statement as HOL Light Name.
- Use this HOL Light name as the key for the key `"HOL_Light_Name"`.
- The value  `"Lean4_Content"` should include the entire Lean 4 declaration from `def`, `theorem`, or `lemma` down to the `sorry` or proof block (including comments, if any).

Output Format:
- Return a JSON array where each element is a dictionary with exactly **one key-value pair**:
  - The key is the HOL Light name (e.g., "Theorem 1", "lemma2", "Definition 3")
  - The value is the Lean 4 content as a string

Example:
```json
[
  {"Theorem 1": "theorem Theorem1 : ∀ x, x > 0 → x < 1 ..."},
  {"lemma 2": "lemma Lemma2 : ∀ x, x > 0 ..."},
  {"Definition 2": "def Definition2 : ∀ x, x > 0 ..."}
]
---
Here is the Lean 4 code:
[Lean4 Code]
"""

USER_PROMPT_FOR_SORRY = """
You are an expert in formal logic and theorem proving using Lean 4. You will be given a Lean 4 code block along with its error messages. Your task is to correct the Lean 4 code by replacing only the proof blocks that cause errors with `sorry` and insert natural languages comment.

Guidelines:
- Identify each error reported in the [Lean4 Error Messages] section.
- Replace the proof line or block of the corresponding lemma, or theorem with `sorry`.
  - If the error occurs inside a `have` block  replace the entire `have` block with `sorry`.
  - If the error is within a lemma or theorem that does not contain any `have` section, replace the entire proof body with `sorry`.
- Do not modify any code that is not directly associated with an error.
- Preserve all existing comments and insert additional natural languages comments to indicate the purpose of the proof by using the [Informal Proof] section.
- Do not add any additional text or explanations.
- Output only with the modified Lean 4 code, wrapped in Lean 4 code block as shown below:
```lean
<Lean 4 code>
```
---
Here is the Lean 4 code and error messages:
[Lean4 Code]
{codes}

[Lean4 Error Messages]
{errors}

[Informal Proof]
{informal_proof}
"""

USER_PROMPT_FOR_HEADER = """
You are an expert in formal logic and theorem proving using Lean 4. You are given a Lean 4 codes. Your task is to extract the header of the Lean 4 code. 

Guildlines:
- The header is defined as the first part of the code that includes all `import`, `open`, `variable` and any other relevant information before the first definition, lemma, or theorem.
- Reserve the structure and formatting of the header, i.e linespaces.
- Respond with the header only, without any additional text or explanations, in a Lean 4 code block as shown below:
```lean
<Lean 4 code header>
```
---
Here is the Lean 4 code:
{codes}
"""