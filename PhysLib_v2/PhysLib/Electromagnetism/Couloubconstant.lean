import PhysLib.Foundations.SI
import Mathlib

namespace SI.Electromagnetism
open UnitsSystem SI
unseal Rat.add Rat.mul Rat.sub Rat.inv

noncomputable abbrev K:Scalar (force_unit + (2 • length_unit) - 2•charge_unit) :=
    ((9:ℝ) * (10:ℝ)^(-9:ℤ)) • StandardUnit _

end SI.Electromagnetism
