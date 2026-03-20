import Mathlib.Tactic
import PhysLib.Foundations.SI
import Mathlib.Algebra.Group.MinimalAxioms

namespace SI.Waves
open UnitsSystem SI
unseal Rat.add Rat.mul Rat.sub Rat.inv

abbrev Wavelength := Length
-- @[simp] def wavelength (v : Speed) (f : Frequency) : Wavelength := v/f

-- @[simp] abbrev F_of (m : Mass) (a : Acceleration) : Force := secondLaw m a

-- @[simp] lemma newton_second_law (m : Mass) (a : Acceleration) :
--     F_of m a = m * a := rfl


end SI.Waves
