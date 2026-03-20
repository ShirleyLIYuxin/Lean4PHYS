import Mathlib.Tactic
import PhysLib.Foundations.SI

namespace SI
open UnitsSystem
unseal Rat.add Rat.mul Rat.sub Rat.inv

/-! # Newton's Second Law
`F = m * a` can be made both as a computational function and as a rewriting lemma.
-/

/-- Computational version: obtain force from mass and acceleration. -/
@[simp] def secondLaw (m : Mass) (a : Acceleration) : Force := m * a

/-- Convenient alias: `F_of` looks more "function-like." -/
@[simp] abbrev F_of (m : Mass) (a : Acceleration) : Force := secondLaw m a

/-- Rewriting version (law equation): rewrite `F` into `m * a`.
Useful when the problem states Newton's second law. -/
@[simp] lemma newton_second_law (m : Mass) (a : Acceleration) :
    F_of m a = m * a := rfl

/-
## Usage examples
Consistent with your workflow of units, `Scalar.val_inj`, `simp`, and `norm_num`.
-/

variable (m:Mass) (a:Acceleration) (F:Force) (v:Speed) (p:Momentum) (E:Energy) (h:Length) (t:Time)

-- 1) Directly compute the force: given m and a, obtain F, and evaluate in newtons.
example (hm : m = 2 • kilogram) (ha : a = 3 • meter / second**2) :
    newton.in (F_of m a) = 6 := by
  -- `F_of m a` is just `m * a`
  simp [← Scalar.val_inj, F_of, hm, ha, kilogram, meter, second, newton]
  norm_num

-- 2) Problem states "Newton's Second Law holds," rewrite unknown F and compute the value.
example (first_law : F = m * a)
        (hm : m = 2 • kilogram) (ha : a = 3 • meter / second**2) :
    F = 6 • newton := by
  simp [← Scalar.val_inj, first_law, hm, ha, kilogram, meter, second, newton]
  norm_num

/-
## Suggested usage habits

- The "function API" (`F_of`, `a_of`, `m_of`) is for **numerical evaluation**
  (together with `... .in`, `simp`, `norm_num`), just like your numerical examples.
- The "law equation/lemma" (`newton_second_law`) is for **rewriting**:
  when the problem states Newton's second law, you can directly use
  `simp [first_law]` or `simp [newton_second_law]` to reduce expressions into units and scalars.
- Define all such physical laws with a **two-layer API** (computational function + rewriting lemma).
  This keeps consistent style for momentum theorem, Hooke's law, work–energy theorem, etc.
- Prepare convenient aliases for common derived quantities
  (like `F_of`/`a_of`/`m_of`) to reduce boilerplate (`rfl`, `simp`).
- If you want "whenever the dimensional relation matches, automatically apply the law,"
  mark the lemma with `@[simp]` (already done above),
  then simply run `simp`/`simp_all` at the beginning of the proof to bring in `F_of ...`, `a_of ...`, etc.
-/

end SI
