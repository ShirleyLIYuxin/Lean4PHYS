import Mathlib.Tactic
import PHYSlib.Foundations.SI


namespace SI
open UnitsSystem
unseal Rat.add Rat.mul Rat.sub Rat.inv

@[simp] theorem speed_add_time_eq_accel_two_time :
  speed_unit + time_unit = acceleration_unit + (2 • time_unit) := by
  -- Expand to dimension expressions
  unfold speed_unit acceleration_unit length_unit time_unit
  -- Rewrite `x - y` as `x + (-y)`, rewrite `2 • y` as `y + y`,
  -- then normalize with commutativity/associativity of addition
  simp [sub_eq_add_neg, two_smul, smul_add, add_smul,
        add_comm, add_left_comm, add_assoc]

@[simp] theorem accel_two_time_eq_length :
  acceleration_unit + (2 • time_unit) = length_unit := by
  unfold acceleration_unit length_unit time_unit
  -- Simplify using negation, distributivity, and additive laws
  simp [sub_eq_add_neg, two_smul, smul_add, add_smul,
        add_comm, add_left_comm, add_assoc]

end SI
