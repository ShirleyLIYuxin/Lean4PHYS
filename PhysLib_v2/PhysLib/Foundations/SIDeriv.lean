import Mathlib
import Aesop
import Mathlib.Tactic
import PhysLib.Foundations.SI
open BigOperators Real Nat Topology Filter Rat UnitsSystem SI
unseal Rat.add Rat.mul Rat.sub Rat.inv

-- Construct NormedAddCommGroup instance for Scalar d
-- This defines the metric space structure (norm and distance) for physical quantities
instance{d:Dimensions}:NormedAddCommGroup (Scalar d):={
  norm:=fun t=>abs t.val -- Norm is defined as the absolute value of the scalar's magnitude
  dist_self:=by simp
  dist_comm:=by
    simp
    exact fun x y => abs_sub_comm x.val y.val
  dist_triangle:=by
    simp
    exact fun x y z => abs_sub_le x.val y.val z.val
  eq_of_dist_eq_zero:=by
    intro x y hxy
    simp at hxy
    refine Scalar.ext_iff.mpr ?_
    contrapose! hxy;
    exact sub_ne_zero_of_ne hxy
}

-- Theorem: Distance between two scalars is the absolute difference of their values
theorem dist_def{d:Dimensions}(a1 a2:Scalar d):Dist.dist a1 a2=|a1.val-a2.val|:=rfl

-- Theorem: Norm of a scalar is the absolute value of its magnitude
theorem norm_def{d:Dimensions}(t:(Scalar d)):‖t‖=abs t.val:=rfl

-- Construct NormedSpace instance over ℝ for Scalar d
-- This allows for scaling physical quantities by real numbers
instance{d:Dimensions}:NormedSpace ℝ (Scalar d):={
  norm_smul_le:=by
    intro a b
    rw[norm_def,norm_def];simp
  smul_zero:=fun a => MulActionWithZero.smul_zero a
  smul_add:=fun a x y => DistribSMul.smul_add a x y
  add_smul:=fun r s x => Module.add_smul r s x
  zero_smul:=fun x => zero_smul ℝ x
}

-- Theorem: Equivalence of open sets between Scalar d and the underlying Real space
theorem open_set_iff{d:Dimensions}(S:Set (Scalar d)):IsOpen S↔ IsOpen {x:ℝ|⟨x⟩ ∈ S}:=by
  constructor
  intro h
  apply Metric.isOpen_iff.mp at h
  refine Metric.isOpen_iff.mpr ?_
  intro x hx
  simp at hx
  have hoe:=h (⟨x⟩:Scalar d) hx
  obtain ⟨e,he1,he2⟩:=hoe
  use e
  split_ands
  exact he1
  rw[Set.subset_def]
  intro x1 hx1
  simp
  exact he2 hx1

  intro h
  apply Metric.isOpen_iff.mp at h
  refine Metric.isOpen_iff.mpr ?_
  intro x hx
  have hoe:=h (x.val) hx
  obtain ⟨e,he1,he2⟩:=hoe
  use e
  split_ands
  exact he1
  rw[Set.subset_def]
  intro x1 hx1
  suffices x1.val∈ {(x:ℝ)|(⟨x⟩:Scalar d)∈ S} by
    simp at this
    exact this
  simp at hx1
  exact he2 hx1

-- Theorem: The mapping from Scalar d to its Real value is differentiable over ℝ
theorem differentiable_real_cast{d:Dimensions}:Differentiable ℝ (fun (t:(Scalar d))=>t.val):=by
  rw[Differentiable]
  intro x
  rw[DifferentiableAt]

  -- Define the derivative as a bounded linear map f
  let f: (Scalar d) →L[ℝ] ℝ:={
    toFun:=(fun t=>t.val)
    map_add':=by
      intro x y
      exact rfl
    map_smul':=by
      intro m x
      simp
    cont:={
      isOpen_preimage:=by
        intro s hs
        refine (open_set_iff ((fun t => t.val) ⁻¹' s)).mpr ?_
        simp
        exact hs
    }
  }

  have hf:∀x:(Scalar d) , f x=x.val:=by
    intro x;exact rfl

  use f
  rw[HasFDerivAt]
  refine { isLittleOTVS := ?_ }
  -- Prove the remainder term is zero
  have hsimp:(fun x' => x'.val - x.val - f (x' - x))=0:=by
    refine funext ?_
    intro x'
    rw[hf]
    simp
  rw[hsimp]
  exact Asymptotics.IsLittleOTVS.zero (fun x' => x' - x) (𝓝 x)

-- Theorem: The physical lifting (wrapping ℝ into Scalar d) is differentiable
theorem isdifferentiable_phys_lift{d:Dimensions}:
  Differentiable ℝ (fun (t:ℝ)=>(⟨t⟩:(Scalar d))):=by
  rw[Differentiable]
  intro x
  rw[DifferentiableAt]

  let f: ℝ →L[ℝ] (Scalar d) :={
    toFun:=(fun t=>(⟨t⟩:(Scalar d)))
    map_add':=by
      intro x y
      exact rfl
    map_smul':=by
      intro m x1
      simp
      exact rfl
    cont:={
      isOpen_preimage:=by
        intro s hs
        apply (open_set_iff s).mp at hs
        exact hs
    }
  }

  have hf:∀x:ℝ , f x=(⟨x⟩:(Scalar d)):=by
    intro x;exact rfl

  use f
  rw[HasFDerivAt]
  refine { isLittleOTVS := ?_ }

  have hsimp:(fun (x':ℝ) => ((⟨x'⟩:(Scalar d)) - (⟨x⟩:(Scalar d)) - f (x' - x)))=0:=by
    refine funext ?_
    intro x'
    rw[hf]
    simp
    exact sub_self ((⟨x'⟩:(Scalar d)) - (⟨x⟩:(Scalar d)))

  rw[hsimp]
  exact Asymptotics.IsLittleOTVS.zero (fun x' => x' - x) (𝓝 x)

variable (K:Type*)[NormedAddCommGroup K][NormedSpace ℝ K]

-- Theorem: Composition of two differentiable functions is differentiable
theorem differ3(f:ℝ → ℝ)(g:ℝ → K)(h1:Differentiable ℝ f)(h2:Differentiable ℝ g):
  Differentiable ℝ (g∘ f):=by
  exact Differentiable.comp h2 h1

-- Definition: Lift a real function f to a mapping between physical scalars
def physlift(d1 d2:Dimensions)(f:ℝ→ ℝ):Scalar d1→ Scalar d2:=(fun t => ⟨f t.val⟩)

-- Definition: Cast a physical mapping to a real function
def mathcast{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2):ℝ → ℝ:= (fun t=> (f ⟨t⟩).val)

-- Definitional lemmas for physlift and mathcast
theorem physlift_def(d1 d2:Dimensions)(f:ℝ→ ℝ):
  physlift d1 d2 f=(fun t => ⟨f t.val⟩):=rfl

theorem mathcast_def{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2):
  mathcast f=(fun t=> (f ⟨t⟩).val):=rfl

-- Theorem: Two physical functions are equal if and only if their mathcasts are equal
theorem physfunc_eq_iff{d1 d2:Dimensions}(f1 f2:Scalar d1→ Scalar d2):f1=f2 ↔ mathcast f1=mathcast f2:=by
  constructor
  intro h
  exact congrArg mathcast h
  intro h
  refine funext ?_
  intro x
  refine Scalar.ext_iff.mpr ?_
  have h1:(f1 x).val=(mathcast f1) x.val:=rfl
  have h2:(f2 x).val=(mathcast f2) x.val:=rfl
  rw[h1,h2,h]

-- Theorem: mathcast and physlift are inverses (1)
theorem lift_cast_inverse(d1 d2:Dimensions)(f:ℝ→ ℝ):
  mathcast (physlift d1 d2 f)=f:=by
  refine funext ?_
  intro x
  rw[physlift_def,mathcast_def]

-- Theorem: mathcast and physlift are inverses (2)
theorem cast_lift_inverse{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2):
  physlift d1 d2 (mathcast f)=f:=by
  refine funext ?_
  intro x
  rw[physlift_def,mathcast_def]

-- Theorem: Differentiability of a lifted physical function
theorem physlift_dif(f:ℝ → ℝ)(d1 d2:Dimensions)(h:Differentiable ℝ f):
  Differentiable ℝ (physlift d1 d2 f):=by
  have hcomp:(physlift d1 d2 f)=(fun (t:ℝ)=>(⟨t⟩:Scalar d2))∘ f ∘ (fun t=>t.val):=by
    rw[physlift_def]
    refine funext ?_
    intro x
    simp

  rw[hcomp]
  refine Differentiable.comp ?_ ?_
  exact isdifferentiable_phys_lift
  refine Differentiable.comp h ?_
  exact differentiable_real_cast

-- Theorem: Differentiability of a casted math function
theorem mathcast_dif{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2)(h:Differentiable ℝ f):
  Differentiable ℝ (mathcast f):=by
  have hcomp:(mathcast f)=(fun t=>t.val)∘ f ∘ (fun t=>(⟨t⟩:(Scalar d1))):=by
    rw[mathcast_def]
    refine funext ?_
    intro x
    simp

  rw[hcomp]
  refine Differentiable.comp ?_ ?_
  exact differentiable_real_cast
  refine Differentiable.comp h ?_
  exact isdifferentiable_phys_lift

-- Definition: Physical derivative.
-- The output dimension is the difference between the codomain and domain dimensions.
noncomputable def physderiv{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2):Scalar d1→ Scalar (d2-d1):=
  (fun x=>⟨deriv (mathcast f) x.val⟩)

theorem physderiv_def{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2):
  physderiv f=(fun x=>⟨deriv (mathcast f) x.val⟩):=rfl

-- Theorem: Casting a physical derivative yields the math derivative of the casted function
theorem deriv_mathphys{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2):
  mathcast (physderiv f)=deriv (mathcast f):=rfl

-- Definition: Pointwise multiplication of two physical mappings (Dimensions add up)
def physmapmul{d1 d2 d3:Dimensions}(f1:Scalar d1→ Scalar d2)(f2:Scalar d1→ Scalar d3):Scalar d1→ Scalar (d2+d3):=
  fun x=>(f1 x)*(f2 x)

theorem phymapmul_def{d1 d2 d3:Dimensions}(f1:Scalar d1→ Scalar d2)(f2:Scalar d1→ Scalar d3):
  physmapmul f1 f2=fun x=>(f1 x)*(f2 x):=rfl

-- Definition: Pointwise division of two physical mappings (Dimensions subtract)
noncomputable def physmapdiv{d1 d2 d3:Dimensions}(f1:Scalar d1→ Scalar d2)(f2:Scalar d1→ Scalar d3):Scalar d1→ Scalar (d2-d3):=
  fun x=>((f1 x)/(f2 x))

theorem phymapmdiv_def{d1 d2 d3:Dimensions}(f1:Scalar d1→ Scalar d2)(f2:Scalar d1→ Scalar d3):
  physmapdiv f1 f2=fun x=>((f1 x)/(f2 x)):=rfl

-- Definition: Multiplication of a physical mapping by a constant scalar
def physmapsmul{d1 d2 d3:Dimensions}(f:Scalar d1→ Scalar d3)(a: Scalar d2):Scalar d1→ Scalar (d2+d3):=
  fun x=>a*(f x)

theorem phymapsmul_def{d1 d2 d3:Dimensions}(f:Scalar d1→ Scalar d2)(a: Scalar d3):
  physmapsmul f a=fun x=>a*(f x):=rfl

-- Theorem: Mathcast of a scalar-multiplied map matches the scalar action on the math function
theorem smul_cast{d1 d2 d3:Dimensions}(f:Scalar d1→ Scalar d3)(a: Scalar d2):
  mathcast (physmapsmul f a)=a.val • (mathcast f):=rfl

-- Definition: Change the dimension labels of a physical mapping if the dimensions are equal
def physmapcast{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2)(d3 d4:Dimensions)(h1:d1=d3)(h2:d2=d4):Scalar d3→ Scalar d4:=
  fun a=>((f (a.cast h1)).cast h2.symm)

theorem phymapcast_def{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2)(d3 d4:Dimensions)(h1:d1=d3)(h2:d2=d4):
  physmapcast f d3 d4 h1 h2=fun (a:(Scalar d3))=> ((f (a.cast h1)).cast h2.symm):=rfl

-- Theorem: Dimension casting does not change the underlying mathematical function
theorem map_cast_matheq{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2)(d3 d4:Dimensions)(h1:d1=d3)(h2:d2=d4):
  mathcast f=mathcast (physmapcast f d3 d4 h1 h2):=rfl
-- Definition: Physical lifting function that "elevates" a real function f to map from ℝ to a Scalar d1
-- Purpose: Takes a real number, applies f, and wraps the result as a physical scalar with dimension d1
def physlift'(d1:Dimensions)(f:ℝ→ ℝ):ℝ→ Scalar d1:=(fun t => ⟨f t⟩)

-- Definition: Mathematical cast function that converts a physical mapping f back to a real function
-- Purpose: Extracts the underlying numerical value from a physical scalar result
def mathcast'{d1:Dimensions}(f:ℝ→ Scalar d1):ℝ → ℝ:= (fun t=> (f t).val)

-- Theorem: Definitional equality for physlift'
theorem physlift_def'(d1:Dimensions)(f:ℝ→ ℝ):
  physlift' d1 f=(fun t => ⟨f t⟩):=rfl

-- Theorem: Definitional equality for mathcast'
theorem mathcast_def'{d1:Dimensions}(f:ℝ→ Scalar d1):
  mathcast' f=(fun t=> (f t).val):=rfl

-- Theorem: Two physical functions are equal if and only if their mathematical casts are equal
theorem physfunc_eq_iff'{d1:Dimensions}(f1 f2:ℝ → Scalar d1):f1=f2 ↔ mathcast' f1=mathcast' f2:=by
  constructor
  intro h
  exact congrArg mathcast' h
  intro h
  refine funext ?_
  intro x
  refine Scalar.ext_iff.mpr ?_
  have h1:(f1 x).val=(mathcast' f1) x:=rfl
  have h2:(f2 x).val=(mathcast' f2) x:=rfl
  rw[h1,h2,h]

-- Theorem: Inverse property 1 - Casting a lifted function returns the original real function
theorem lift_cast_inverse'{d1:Dimensions}(f:ℝ→ ℝ):
  mathcast' (physlift' d1 f)=f:=by
  refine funext ?_
  intro x
  rw[physlift_def', mathcast_def']

-- Theorem: Inverse property 2 - Lifting a casted function returns the original physical mapping
theorem cast_lift_inverse'{d1:Dimensions}(f:ℝ → Scalar d1):
  physlift' d1 (mathcast' f)=f:=by
  refine funext ?_
  intro x
  rw[physlift_def', mathcast_def']

-- Theorem: Differentiability of the physical lift
-- If the underlying real function f is differentiable, then its physical lift is also differentiable
theorem physlift_dif'(f:ℝ → ℝ)(d1:Dimensions)(h:Differentiable ℝ f):
  Differentiable ℝ (physlift' d1 f):=by
  -- Express physlift' as a composition of the wrapping function and f
  have hcomp:(physlift' d1 f)=(fun (t:ℝ)=>(⟨t⟩:Scalar d1))∘ f :=by
    rw[physlift_def']
    refine funext ?_
    intro x
    simp

  rw[hcomp]
  refine Differentiable.comp ?_ ?_
  exact isdifferentiable_phys_lift -- The outer wrapping (ℝ → Scalar) is differentiable
  exact h

-- Theorem: Differentiability of the mathematical cast
-- If the physical mapping f is differentiable, then its numerical extraction is also differentiable
theorem mathcast_dif'{d1 :Dimensions}(f:ℝ→ Scalar d1)(h:Differentiable ℝ f):
  Differentiable ℝ (mathcast' f):=by
  -- Express mathcast' as a composition of the extraction (val) and f
  have hcomp:(mathcast' f)=(fun t=>t.val)∘ f :=by
    rw[mathcast_def']
    refine funext ?_
    intro x
    simp

  rw[hcomp]
  refine Differentiable.comp ?_ ?_
  exact differentiable_real_cast -- The outer extraction (Scalar → ℝ) is differentiable
  exact h

-- Definition: Physical derivative for functions mapping ℝ to a Scalar d1
-- Implemented by casting to math, deriving in ℝ, and wrapping the result back into a Scalar
noncomputable def physderiv'{d1:Dimensions}(f:ℝ → Scalar d1):ℝ → Scalar d1:=
  (fun x=>⟨deriv (mathcast' f) x⟩)

-- Theorem: Definitional lemma for physderiv'
theorem physderiv_def'{d1:Dimensions}(f:ℝ → Scalar d1):
  physderiv' f=(fun x=>⟨deriv (mathcast' f) x⟩):=rfl

-- Theorem: Relationship between physical and mathematical derivatives
theorem deriv_mathphys'{d1:Dimensions}(f:ℝ → Scalar d1):
  mathcast' (physderiv' f)=deriv (mathcast' f):=rfl

-- Definition: Pointwise multiplication of two physical scalar functions (Dimensions are added)
def physmapmul'{d1 d2:Dimensions}(f1:ℝ → Scalar d1)(f2:ℝ → Scalar d2):ℝ→ Scalar (d1+d2):=
  fun x=>(f1 x)*(f2 x)

-- Theorem: Definitional lemma for physmapmul'
theorem physmapmul_def'{d1 d2:Dimensions}(f1:ℝ → Scalar d1)(f2:ℝ → Scalar d2):
  physmapmul' f1 f2=fun x=>(f1 x)*(f2 x):=rfl

-- Definition: Pointwise division of two physical scalar functions (Dimensions are subtracted)
noncomputable def physmapdiv'{d1 d2:Dimensions}(f1:ℝ → Scalar d1)(f2:ℝ → Scalar d2):ℝ→ Scalar (d1-d2):=
  fun x=>((f1 x)/(f2 x))

-- Theorem: Definitional lemma for physmapdiv'
theorem phymapmdiv_def'{d1 d2:Dimensions}(f1:ℝ → Scalar d1)(f2:ℝ → Scalar d2):
  physmapdiv' f1 f2=fun x=>((f1 x)/(f2 x)):=rfl

-- Definition: Multiplication of a physical function by a constant scalar
def physmapsmul'{d1 d2:Dimensions}(f:ℝ → Scalar d1)(a: Scalar d2):ℝ→ Scalar (d1+d2):=
  fun x=>(f x)*a

-- Theorem: Definitional lemma for physmapsmul'
theorem phymapsmul_def'{d1 d2:Dimensions}(f:ℝ → Scalar d1)(a: Scalar d2):
  physmapsmul' f a=fun x=>(f x)*a:=rfl

-- Theorem: The mathcast of a scalar multiplication equals the scalar value times the function's mathcast
theorem smul_cast'{d1 d2:Dimensions}(f:ℝ→ Scalar d1)(a: Scalar d2):
  mathcast' (physmapsmul' f a)=a.val • (mathcast' f):=by
  rw[phymapsmul_def', mathcast_def', mathcast_def']
  refine Eq.symm (funext ?_)
  intro x
  simp
  rw[mul_comm]

-- Definition: Physical dimension cast for functions mapping ℝ to Scalars
-- Allows changing the dimension label d1 to d2 given a proof h that d1 = d2
def physmapcast'{d1 d2:Dimensions}(f:ℝ→ Scalar d1)(h:d1=d2):ℝ→ Scalar d2:=
  fun a=>((f a).cast h.symm)

-- Theorem: Definitional lemma for physmapcast'
theorem phymapcast_def'{d1 d2:Dimensions}(f:ℝ→ Scalar d1)(h:d1=d2):
  physmapcast' f h = fun a => ((f a).cast h.symm):=rfl

-- Theorem: Dimension casting does not change the underlying mathematical values
theorem map_cast_matheq'{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2)(d3 d4:Dimensions)(h1:d1=d3)(h2:d2=d4):
  mathcast f = mathcast (physmapcast f d3 d4 h1 h2):=rfl
-- Definition: Physical lifting function for mapping from a physical Scalar d1 to ℝ
-- Purpose: Takes a scalar, extracts its real value, and applies the real function f
def physlift''(d1:Dimensions)(f:ℝ→ ℝ):Scalar d1 → ℝ :=(fun t => f t.val)

-- Definition: Mathematical cast function for mappings from Scalar d1 to ℝ
-- Purpose: Converts the domain from Scalar d1 to ℝ by wrapping the input t as ⟨t⟩
def mathcast''{d1:Dimensions}(f:Scalar d1 → ℝ):ℝ → ℝ:= (fun t=> (f ⟨t⟩))

-- Theorem: Definitional equality for physlift''
theorem physlift_def''(d1:Dimensions)(f:ℝ→ ℝ):
  physlift'' d1 f=(fun t => f t.val):=rfl

-- Theorem: Definitional equality for mathcast''
theorem mathcast_def''{d1:Dimensions}(f:Scalar d1→ ℝ):
  mathcast'' f=(fun t=> (f ⟨t⟩)):=rfl

-- Theorem: Equality of two physical-to-real functions based on their mathematical casts
theorem physfunc_eq_iff''{d1:Dimensions}(f1 f2:Scalar d1 → ℝ ):f1=f2 ↔ mathcast'' f1=mathcast'' f2:=by
  constructor
  intro h
  exact congrArg mathcast'' h
  intro h
  refine funext ?_
  intro x
  have h1:(f1 x)=(mathcast'' f1) x.val:=rfl
  have h2:(f2 x)=(mathcast'' f2) x.val:=rfl
  rw[h1,h2,h]

-- Theorem: Inverse property 1 - Casting a lifted function returns the original real function
theorem lift_cast_inverse''(d1:Dimensions)(f:ℝ→ ℝ):
  mathcast'' (physlift'' d1 f)=f:=by
  refine funext ?_
  intro x
  rw[physlift_def'', mathcast_def'']

-- Theorem: Inverse property 2 - Lifting a casted function returns the original physical mapping
theorem cast_lift_inverse''{d1:Dimensions}(f:Scalar d1→ ℝ):
  physlift'' d1 (mathcast'' f)=f:=by
  refine funext ?_
  intro x
  rw[physlift_def'', mathcast_def'']

-- Theorem: Differentiability of the physical lift (Scalar d1 → ℝ)
-- If f is differentiable, then its lift from a physical domain is differentiable
theorem physlift_dif''(f:ℝ → ℝ)(d1:Dimensions)(h:Differentiable ℝ f):
  Differentiable ℝ (physlift'' d1 f):=by
  -- Express physlift'' as a composition of f and the extraction function (val)
  have hcomp:(physlift'' d1 f)=f ∘ (fun t => t.val):=by
    rw[physlift_def'']
    refine funext ?_
    intro x
    simp

  rw[hcomp]
  refine Differentiable.comp ?_ ?_
  exact h
  exact differentiable_real_cast -- The extraction (Scalar → ℝ) is differentiable

-- Theorem: Differentiability of the mathematical cast
-- If the physical-to-real mapping f is differentiable, its cast is differentiable
theorem mathcast_dif''{d1 :Dimensions}(f:Scalar d1 → ℝ)(h:Differentiable ℝ f):
  Differentiable ℝ (mathcast'' f):=by
  -- Express mathcast'' as a composition of f and the wrapping function (⟨t⟩)
  have hcomp:(mathcast'' f)= f ∘ (fun t=>⟨t⟩):=by
    rw[mathcast_def'']
    refine funext ?_
    intro x
    simp

  rw[hcomp]
  refine Differentiable.comp ?_ ?_
  exact h
  exact isdifferentiable_phys_lift -- The wrapping (ℝ → Scalar) is differentiable

-- Definition: Physical derivative for functions mapping Scalar d1 to ℝ
-- The output dimension is -d1 (the "per-unit" dimension)
noncomputable def physderiv''{d1:Dimensions}(f:Scalar d1 → ℝ):Scalar d1 → Scalar (-d1):=
  (fun x=>⟨deriv (mathcast'' f) x.val⟩)

-- Theorem: Definitional lemma for physderiv''
theorem physderiv_def''{d1:Dimensions}(f:Scalar d1 → ℝ):
  physderiv'' f=(fun x=>⟨deriv (mathcast'' f) x.val⟩):=rfl

-- Theorem: Relationship between physical and mathematical derivatives for Scalar-to-ℝ functions
theorem deriv_mathphys''{d1:Dimensions}(f:Scalar d1→ ℝ):
  mathcast (physderiv'' f)=deriv (mathcast'' f):=rfl

-- Definition: Multiplication of two functions mapping ℝ to Scalar d1
-- Resulting dimension is 2 • d1
def physmapmul''{d1:Dimensions}(f1:ℝ → Scalar d1)(f2:ℝ → Scalar d1):ℝ→ Scalar (2 • d1):=
  fun x=>(((f1 x)*(f2 x)).cast (by module))

-- Theorem: Definitional lemma for physmapmul''
theorem physmapmul_def''{d1:Dimensions}(f1:ℝ → Scalar d1 )(f2:ℝ → Scalar d1):
  physmapmul'' f1 f2=(fun x=>(((f1 x)*(f2 x)).cast (by module))):=rfl

-- Definition: Division of two functions mapping Scalar d1 to ℝ (Dimensionality cancels to ℝ)
noncomputable def physmapdiv''{d1:Dimensions}(f1:Scalar d1 → ℝ)(f2:Scalar d1 → ℝ):ℝ→ ℝ:=
  fun x=>((f1 ⟨x⟩)/(f2 ⟨x⟩))

-- Theorem: Definitional lemma for physmapdiv''
theorem phymapmdiv_def''{d1:Dimensions}(f1:Scalar d1 → ℝ)(f2:Scalar d1 → ℝ):
  physmapdiv'' f1 f2=fun x=>((f1 ⟨x⟩)/(f2 ⟨x⟩)):=rfl

-- Definition: Scalar multiplication of a physical mapping by a constant physical Scalar d2
def physmapsmul''{d1 d2:Dimensions}(f:Scalar d1 → ℝ)(a: Scalar d2):Scalar d1→ Scalar d2:=
  fun x=>(f x) • a

-- Theorem: Definitional lemma for physmapsmul''
theorem phymapsmul_def''{d1 d2:Dimensions}(f:Scalar d1 → ℝ)(a: Scalar d2):
  physmapsmul'' f a=fun x=>(f x) • a:=rfl

-- Theorem: The mathcast of a scalar-multiplied map matches the scalar action on the mathcast function
theorem smul_cast''{d1 d2:Dimensions}(f:Scalar d1 → ℝ )(a: Scalar d2):
  mathcast (physmapsmul'' f a)=a.val • (mathcast'' f):=by
  rw[phymapsmul_def'', mathcast_def'', mathcast_def]
  refine Eq.symm (funext ?_)
  intro x
  simp
  rw[mul_comm]

-- Definition: Physical dimension cast for the input domain (Scalar d1 to Scalar d2)
def physmapcast''{d1 d2:Dimensions}(f:Scalar d1 → ℝ)(h:d1=d2):Scalar d2→ ℝ:=
  fun a=>(f (a.cast h))

-- Theorem: Definitional lemma for physmapcast''
theorem phymapcast_def''{d1 d2:Dimensions}(f:Scalar d1 → ℝ)(h:d1=d2):
  physmapcast'' f h=fun a=> (f (a.cast h)):=rfl

/--             Basic Kinematics                      -/

-- First, define a general structure for "One-Dimensional Motion" as a core building block
structure OneDimMotion where
  -- Position
  pos : Time → Length
  differentiable_pos : Differentiable ℝ pos
  -- Velocity
  vel : Time → Speed := physderiv pos
  differentiable_vel : Differentiable ℝ vel
  -- Acceleration
  acc : Time → Acceleration := physderiv vel
  -- Record of the component-wise net external force
  F : Finset (Time → Force)

-- Define points in each dimension using a compositional approach
structure point_1d where
  m : Mass
  motion : OneDimMotion
  -- Newton's Second Law: F = ma
  Newton : ∀ t, m * motion.acc t = ∑ f ∈ motion.F, f t
  -- Mapping from physical time to real position value
  point_toreal : Time → ℝ := fun t => (motion.pos t).val

structure point_2d where
  m : Mass
  motion_x : OneDimMotion
  motion_y : OneDimMotion
  Newtonx : ∀ t, m * motion_x.acc t = ∑ f ∈ motion_x.F, f t
  Newtony : ∀ t, m * motion_y.acc t = ∑ f ∈ motion_y.F, f t
  -- Mapping from physical time to a real (x, y) coordinate pair
  point_toreal : Time → ℝ × ℝ := fun t => ((motion_x.pos t).val, (motion_y.pos t).val)

structure point_3d where
  m : Mass
  motion_x : OneDimMotion
  motion_y : OneDimMotion
  motion_z : OneDimMotion
  Newtonx : ∀ t, m * motion_x.acc t = ∑ f ∈ motion_x.F, f t
  Newtony : ∀ t, m * motion_y.acc t = ∑ f ∈ motion_y.F, f t
  Newtonz : ∀ t, m * motion_z.acc t = ∑ f ∈ motion_z.F, f t
  -- Mapping from physical time to a real (x, y, z) coordinate triplet
  point_toreal : Time → ℝ × ℝ × ℝ := fun t => ((motion_x.pos t).val, (motion_y.pos t).val, (motion_z.pos t).val)

structure isolate_system_1d where
  points : Finset point_1d
  -- The sum of internal forces is 0
  sumforce : ∀ t, ∑ p ∈ points, (∑ f ∈ p.motion.F, f t) = 0
  -- Conservation of momentum (equivalent to net external force being 0)
  summomentum : ∀ t, ∑ p ∈ points, (p.m * p.motion.vel t) = ∑ p ∈ points, (p.m * p.motion.vel 0)

structure isolate_system_2d where
  points : Finset point_2d
  -- Internal forces sum to 0 in X-axis
  sumforce_x : ∀ t, ∑ p ∈ points, (∑ f ∈ p.motion_x.F, f t) = 0
  -- Momentum conservation in X-axis
  summomentum_x : ∀ t, ∑ p ∈ points, (p.m * p.motion_x.vel t) = ∑ p ∈ points, (p.m * p.motion_x.vel 0)
  -- Internal forces sum to 0 in Y-axis
  sumforce_y : ∀ t, ∑ p ∈ points, (∑ f ∈ p.motion_y.F, f t) = 0
  -- Momentum conservation in Y-axis
  summomentum_y : ∀ t, ∑ p ∈ points, (p.m * p.motion_y.vel t) = ∑ p ∈ points, (p.m * p.motion_y.vel 0)

structure isolate_system_3d where
  points : Finset point_3d
  -- Internal forces sum to 0 in X-axis
  sumforce_x : ∀ t, ∑ p ∈ points, (∑ f ∈ p.motion_x.F, f t) = 0
  -- Momentum conservation in X-axis
  summomentum : ∀ t, ∑ p ∈ points, (p.m * p.motion_x.vel t) = ∑ p ∈ points, (p.m * p.motion_x.vel 0)
  -- Internal forces sum to 0 in Y-axis
  sumforce_y : ∀ t, ∑ p ∈ points, (∑ f ∈ p.motion_y.F, f t) = 0
  -- Momentum conservation in Y-axis
  summomentum_y : ∀ t, ∑ p ∈ points, (p.m * p.motion_y.vel t) = ∑ p ∈ points, (p.m * p.motion_y.vel 0)
  -- Internal forces sum to 0 in Z-axis
  sumforce_z : ∀ t, ∑ p ∈ points, (∑ f ∈ p.motion_z.F, f t) = 0
  -- Momentum conservation in Z-axis
  summomentum_z : ∀ t, ∑ p ∈ points, (p.m * p.motion_z.vel t) = ∑ p ∈ points, (p.m * p.motion_z.vel 0)

/--                 Rigid Body Mechanics                     -/

-- Define an axis in 3D space as an affine line
class axis where
  A : Set (ℝ × ℝ × ℝ)
  affine : ∃ a, ∃ v, (v ≠ 0) ∧ (∀ x : A, ∃ t : ℝ, (x : (ℝ × ℝ × ℝ)) = a + t • v)

-- Distance from a point to an axis
noncomputable def distance_ptl(a : ℝ × ℝ × ℝ)(l : axis) : ℝ := sInf {r : ℝ | ∃ b : l.A, dist a b = r}

structure rotating_rigid_body where
  points : Set point_3d
  -- Set of real-coordinate points occupied by the rigid body at time t
  points_toreal : Time → Set (ℝ × ℝ × ℝ) := fun t => {x | ∃! a : points, x = (a : point_3d).point_toreal t}
  -- Mass distribution function
  Mass' : ℝ × ℝ × ℝ → Mass
  -- Angular velocity (dimension: 1/T)
  ang_vel : Time → Scalar (-time_unit)
  -- Constraint: mass is zero outside the body's initial volume
  h : ∀ x, x ∉ points_toreal 0 → Mass' x = 0

-- Calculation of Moment of Inertia relative to an axis A
noncomputable def rotation_inertia(A : axis)(B : rotating_rigid_body) : Scalar (mass_unit + 2 • length_unit) :=
  ⟨∫ x in (B.points_toreal 0), (distance_ptl x A)^2 * ((B.Mass' x)).val⟩
