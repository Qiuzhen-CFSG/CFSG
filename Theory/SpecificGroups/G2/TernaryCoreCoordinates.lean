module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The root formulas use the licensed split-octonion model from
Atlas/LinearGroups/G2, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917;
see LICENSES/ATLAS-CITATION.cff. Changes: ternary radical coordinates,
central cubic extensions, and the literal parabolic generator actions.
-/
public import Theory.AtlasPort.LinearGroups.G2.LieParabolicSetup
public import Theory.GroupTheory.CentralCubicReconstruction

/-!
# Canonical coordinates on both ternary G₂ parabolic radicals

Each actual five-root subgroup over ZMod 3 is a central cubic extension
of an elementary four-dimensional group. Correcting the central root
parameter makes the torus involution fix that parameter and negate the
quotient. The group law, commutator, canonical inverted section and kernel
are explicit, with the distinct short and long root conventions retained.
These are the concrete targets for the original-core reconstruction in
Aschbacher–Smith I.4.5, printed p.417. No original-group recognition is
asserted. AtlasCoreComparison applies the cubic-extension interface;
TernaryCoreActions supplies the actual endpoint generator actions.
-/

@[expose] public section

open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.Explicit Atlas.SplitOctonion
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace Atlas.G2.TernaryCore
abbrev V := Multiplicative (Fin 4 → ZMod 3)
@[simp] private theorem char_three : (3:(ZMod 3))=0 := by decide
@[simp] private theorem char_six : (6:(ZMod 3))=0 := by decide

def short (k : (ZMod 3)) (v : V) : radical₁ (F := (ZMod 3)) :=
  ⟨unipotentProduct ![k+v.toAdd 0*v.toAdd 3,v.toAdd 0,v.toAdd 1,v.toAdd 2,v.toAdd 3,0],
    ⟨_,rfl,rfl⟩⟩
def long (k : (ZMod 3)) (v : V) : radical₂ (F := (ZMod 3)) :=
  ⟨unipotentProduct ![v.toAdd 0,v.toAdd 1,k-v.toAdd 2*v.toAdd 3,v.toAdd 2,0,v.toAdd 3],
    ⟨_,rfl,rfl⟩⟩
def shortForm (v w : V) : (ZMod 3) := v.toAdd 0*w.toAdd 3-w.toAdd 0*v.toAdd 3
def longForm (v w : V) : (ZMod 3) := v.toAdd 3*w.toAdd 2-v.toAdd 2*w.toAdd 3

theorem short_mul (k l : (ZMod 3)) (v w : V) :
    short k v*short l w=short (k+l-shortForm v w) (v*w) := by
  apply Subtype.ext
  change unipotentProduct _*unipotentProduct _=unipotentProduct _
  rw [unipotentProduct_mul]
  congr 1
  ext i
  fin_cases i <;> dsimp [shortForm,unipotentProductParameters] <;> (try simp only [char_three,char_six]) <;> ring_nf
  linear_combination -(w.toAdd 0*v.toAdd 3)*char_three

theorem long_mul (k l : (ZMod 3)) (v w : V) :
    long k v*long l w=long (k+l-longForm v w) (v*w) := by
  apply Subtype.ext
  change unipotentProduct _*unipotentProduct _=unipotentProduct _
  rw [unipotentProduct_mul]
  congr 1
  ext i
  fin_cases i <;> dsimp [longForm,unipotentProductParameters] <;> (try simp only [char_three,char_six]) <;> ring_nf

/-- Canonical coordinates on the actual five-root subgroup. -/
def shortCoordinates : (ZMod 3) × V ≃ radical₁ (F := (ZMod 3)) where
  toFun x := short x.1 x.2
  invFun x := let t := unipotentParameters x.val
             (t 0-t 1*t 4,Multiplicative.ofAdd ![t 1,t 2,t 3,t 4])
  left_inv := by
    rintro ⟨k,v⟩
    simp only [short,unipotentParameters_product]
    apply Prod.ext
    · dsimp
      ring
    · apply Multiplicative.toAdd.injective
      ext i
      fin_cases i <;> rfl
  right_inv := by
    rintro ⟨x,t,ht,rfl⟩
    apply Subtype.ext
    simp only [unipotentParameters_product]
    apply congrArg unipotentProduct
    ext i
    fin_cases i <;> simp [ht]

@[simp] theorem short_one : short 0 1=1 := by
  apply Subtype.ext
  simp [short,unipotentProduct]

theorem short_injective : Function.Injective (fun x : (ZMod 3) × V => short x.1 x.2) :=
  shortCoordinates.injective

theorem short_surjective (x : radical₁ (F := (ZMod 3))) : ∃ k v, short k v=x := by
  obtain ⟨⟨k,v⟩,h⟩ := shortCoordinates.surjective x
  exact ⟨k,v,h⟩

@[simp] theorem shortCoordinates_symm (k : (ZMod 3)) (v : V) :
    shortCoordinates.symm (short k v)=(k,v) := shortCoordinates.symm_apply_apply (k,v)

/-- The literal four-dimensional abelian quotient in root coordinates. -/
def shortQuotient : radical₁ (F := (ZMod 3)) →* V where
  toFun x := (shortCoordinates.symm x).2
  map_one' := by
    have h := shortCoordinates_symm 0 1
    rw [short_one] at h
    exact congrArg Prod.snd h
  map_mul' x y := by
    obtain ⟨k,v,rfl⟩ := short_surjective x
    obtain ⟨l,w,rfl⟩ := short_surjective y
    rw [short_mul]
    rw [shortCoordinates_symm,shortCoordinates_symm,shortCoordinates_symm]

@[simp] theorem shortQuotient_apply (k : (ZMod 3)) (v : V) : shortQuotient (short k v)=v :=
  congrArg Prod.snd (shortCoordinates.symm_apply_apply (k,v))

/-- The canonical involution fixes the cubic coordinate and negates the quotient. -/
def shortInvolution : MulAut (radical₁ (F := (ZMod 3))) where
  toFun x := short (shortCoordinates.symm x).1 ((shortCoordinates.symm x).2)⁻¹
  invFun x := short (shortCoordinates.symm x).1 ((shortCoordinates.symm x).2)⁻¹
  left_inv x := by
    obtain ⟨k,v,rfl⟩ := short_surjective x
    simp only [shortCoordinates_symm,inv_inv]
  right_inv x := by
    obtain ⟨k,v,rfl⟩ := short_surjective x
    simp only [shortCoordinates_symm,inv_inv]
  map_mul' x y := by
    obtain ⟨k,v,rfl⟩ := short_surjective x
    obtain ⟨l,w,rfl⟩ := short_surjective y
    rw [short_mul]
    simp only [shortCoordinates_symm]
    rw [short_mul]
    congr 1
    · simp [shortForm]
    · exact mul_inv _ _

@[simp] theorem shortInvolution_apply (k : (ZMod 3)) (v : V) :
    shortInvolution (short k v)=short k v⁻¹ := by
  change short (shortCoordinates.symm (short k v)).1
    ((shortCoordinates.symm (short k v)).2)⁻¹=_
  rw [shortCoordinates_symm]

/-- The actual radical, quotient and distinguished involution satisfy cubic reconstruction. -/
def shortExtension : CubicInvolutionExtension (radical₁ (F := (ZMod 3))) V where
  quotient := shortQuotient
  surjective v := ⟨short 0 v,shortQuotient_apply 0 v⟩
  central := by
    intro x hx
    obtain ⟨k,v,rfl⟩ := short_surjective x
    have hv : v=1 := (shortQuotient_apply k v).symm.trans hx
    subst v
    apply mem_center_iff.mpr
    intro y
    obtain ⟨l,w,rfl⟩ := short_surjective y
    simp only [short_mul,mul_one,one_mul]
    congr 1
    simp [shortForm,add_comm]
  cube x := by
    obtain ⟨k,v,rfl⟩ := short_surjective x
    rw [pow_succ,pow_two,short_mul,short_mul]
    have hk : k+k-shortForm v v+k-shortForm (v*v) v=0 := by
      simp [shortForm]
      ring_nf
      simp only [char_three,mul_zero]
    have hv : v*v*v=1 := by
      apply Multiplicative.toAdd.injective
      ext i
      change v.toAdd i+v.toAdd i+v.toAdd i=0
      ring_nf
      simp only [char_three,mul_zero]
    rw [hk,hv,short_one]
  involution := shortInvolution
  involutive x := by
    obtain ⟨k,v,rfl⟩ := short_surjective x
    rw [shortInvolution_apply,shortInvolution_apply,inv_inv]
  fixed x hx := by
    obtain ⟨k,v,rfl⟩ := short_surjective x
    have hv : v=1 := (shortQuotient_apply k v).symm.trans hx
    rw [hv,shortInvolution_apply,inv_one]
  inverted x := by
    obtain ⟨k,v,rfl⟩ := short_surjective x
    rw [shortInvolution_apply,shortQuotient_apply,shortQuotient_apply]

/-- Canonical coordinates on the actual five-root subgroup. -/
def longCoordinates : (ZMod 3) × V ≃ radical₂ (F := (ZMod 3)) where
  toFun x := long x.1 x.2
  invFun x := let t := unipotentParameters x.val
             (t 2+t 3*t 5,Multiplicative.ofAdd ![t 0,t 1,t 3,t 5])
  left_inv := by
    rintro ⟨k,v⟩
    simp only [long,unipotentParameters_product]
    apply Prod.ext
    · dsimp
      ring
    · apply Multiplicative.toAdd.injective
      ext i
      fin_cases i <;> rfl
  right_inv := by
    rintro ⟨x,t,ht,rfl⟩
    apply Subtype.ext
    simp only [unipotentParameters_product]
    apply congrArg unipotentProduct
    ext i
    fin_cases i <;> simp [ht]

@[simp] theorem long_one : long 0 1=1 := by
  apply Subtype.ext
  simp [long,unipotentProduct]

theorem long_injective : Function.Injective (fun x : (ZMod 3) × V => long x.1 x.2) :=
  longCoordinates.injective

theorem long_surjective (x : radical₂ (F := (ZMod 3))) : ∃ k v, long k v=x := by
  obtain ⟨⟨k,v⟩,h⟩ := longCoordinates.surjective x
  exact ⟨k,v,h⟩

@[simp] theorem longCoordinates_symm (k : (ZMod 3)) (v : V) :
    longCoordinates.symm (long k v)=(k,v) := longCoordinates.symm_apply_apply (k,v)

/-- The literal four-dimensional abelian quotient in root coordinates. -/
def longQuotient : radical₂ (F := (ZMod 3)) →* V where
  toFun x := (longCoordinates.symm x).2
  map_one' := by
    have h := longCoordinates_symm 0 1
    rw [long_one] at h
    exact congrArg Prod.snd h
  map_mul' x y := by
    obtain ⟨k,v,rfl⟩ := long_surjective x
    obtain ⟨l,w,rfl⟩ := long_surjective y
    rw [long_mul]
    rw [longCoordinates_symm,longCoordinates_symm,longCoordinates_symm]

@[simp] theorem longQuotient_apply (k : (ZMod 3)) (v : V) : longQuotient (long k v)=v :=
  congrArg Prod.snd (longCoordinates.symm_apply_apply (k,v))

/-- The canonical involution fixes the cubic coordinate and negates the quotient. -/
def longInvolution : MulAut (radical₂ (F := (ZMod 3))) where
  toFun x := long (longCoordinates.symm x).1 ((longCoordinates.symm x).2)⁻¹
  invFun x := long (longCoordinates.symm x).1 ((longCoordinates.symm x).2)⁻¹
  left_inv x := by
    obtain ⟨k,v,rfl⟩ := long_surjective x
    simp only [longCoordinates_symm,inv_inv]
  right_inv x := by
    obtain ⟨k,v,rfl⟩ := long_surjective x
    simp only [longCoordinates_symm,inv_inv]
  map_mul' x y := by
    obtain ⟨k,v,rfl⟩ := long_surjective x
    obtain ⟨l,w,rfl⟩ := long_surjective y
    rw [long_mul]
    simp only [longCoordinates_symm]
    rw [long_mul]
    congr 1
    · simp [longForm]
    · exact mul_inv _ _

@[simp] theorem longInvolution_apply (k : (ZMod 3)) (v : V) :
    longInvolution (long k v)=long k v⁻¹ := by
  change long (longCoordinates.symm (long k v)).1
    ((longCoordinates.symm (long k v)).2)⁻¹=_
  rw [longCoordinates_symm]

/-- The actual radical, quotient and distinguished involution satisfy cubic reconstruction. -/
def longExtension : CubicInvolutionExtension (radical₂ (F := (ZMod 3))) V where
  quotient := longQuotient
  surjective v := ⟨long 0 v,longQuotient_apply 0 v⟩
  central := by
    intro x hx
    obtain ⟨k,v,rfl⟩ := long_surjective x
    have hv : v=1 := (longQuotient_apply k v).symm.trans hx
    subst v
    apply mem_center_iff.mpr
    intro y
    obtain ⟨l,w,rfl⟩ := long_surjective y
    simp only [long_mul,mul_one,one_mul]
    congr 1
    simp [longForm,add_comm]
  cube x := by
    obtain ⟨k,v,rfl⟩ := long_surjective x
    rw [pow_succ,pow_two,long_mul,long_mul]
    have hk : k+k-longForm v v+k-longForm (v*v) v=0 := by
      simp [longForm]
      ring_nf
      simp only [char_three,mul_zero]
    have hv : v*v*v=1 := by
      apply Multiplicative.toAdd.injective
      ext i
      change v.toAdd i+v.toAdd i+v.toAdd i=0
      ring_nf
      simp only [char_three,mul_zero]
    rw [hk,hv,long_one]
  involution := longInvolution
  involutive x := by
    obtain ⟨k,v,rfl⟩ := long_surjective x
    rw [longInvolution_apply,longInvolution_apply,inv_inv]
  fixed x hx := by
    obtain ⟨k,v,rfl⟩ := long_surjective x
    have hv : v=1 := (longQuotient_apply k v).symm.trans hx
    rw [hv,longInvolution_apply,inv_one]
  inverted x := by
    obtain ⟨k,v,rfl⟩ := long_surjective x
    rw [longInvolution_apply,longQuotient_apply,longQuotient_apply]

/-- The coordinate involution is literal conjugation by the indicated Atlas torus element. -/
theorem shortInvolution_ambient (x : radical₁ (F := (ZMod 3))) :
    (shortInvolution x : Model (ZMod 3))=MulAut.conj (torus (-1) (-1)) (x:Model (ZMod 3)) := by
  obtain ⟨k,v,rfl⟩ := short_surjective x
  rw [shortInvolution_apply]
  change unipotentProduct _=torus (-1) (-1)*unipotentProduct _*(torus (-1) (-1))⁻¹
  rw [torus_unipotentProduct]
  congr 1
  ext i
  fin_cases i <;> dsimp [torusUnipotentParameters] <;> simp

theorem short_inv (k : (ZMod 3)) (v : V) : (short k v)⁻¹=short (-k) v⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [short_mul]
  simp [shortForm,short_one]

/-- The canonical inverted section is explicit in all four root coordinates. -/
theorem shortExtension_section (v : V) : shortExtension.invertedSection v=short 0 v := by
  apply shortExtension.inverted_lift_unique (shortExtension.section_inverted v)
  · change shortInvolution (short 0 v)=(short 0 v)⁻¹
    rw [shortInvolution_apply,short_inv,neg_zero]
  · exact shortExtension.quotient_section v |>.trans (shortQuotient_apply 0 v).symm

/-- The complete commutator form has its exact cubic-line codomain. -/
theorem shortExtension_commutator (v w : V) :
    (shortExtension.commutatorValue v w : radical₁ (F := (ZMod 3)))=short (shortForm v w) 1 := by
  apply mul_left_cancel (a:=short 0 v*short 0 w)
  rw [←shortExtension_section v,←shortExtension_section w,←shortExtension.section_mul,
    shortExtension_section,shortExtension_section,shortExtension_section,short_mul,short_mul]
  simp [shortForm]

/-- The central root parameter as a homomorphism into the literal quotient kernel. -/
def shortKernelHom : Multiplicative (ZMod 3) →* shortQuotient.ker where
  toFun k := ⟨short k.toAdd 1,MonoidHom.mem_ker.mpr (shortQuotient_apply _ _)⟩
  map_one' := Subtype.ext short_one
  map_mul' k l := by
    apply Subtype.ext
    change short (k.toAdd+l.toAdd) 1=short k.toAdd 1*short l.toAdd 1
    rw [short_mul]
    simp [shortForm]

@[simp] theorem shortKernelHom_apply (k : Multiplicative (ZMod 3)) :
    (shortKernelHom k : radical₁ (F := (ZMod 3)))=short k.toAdd 1 := rfl

/-- The kernel is the actual cubic root subgroup, with its additive parameter. -/
noncomputable def shortKernelEquiv : Multiplicative (ZMod 3) ≃* shortQuotient.ker :=
  MulEquiv.ofBijective shortKernelHom (by
    constructor
    · intro k l h
      have hh := congrArg (fun x : shortQuotient.ker => shortCoordinates.symm x.val) h
      change shortCoordinates.symm (short k.toAdd 1)=shortCoordinates.symm (short l.toAdd 1) at hh
      rw [shortCoordinates_symm,shortCoordinates_symm] at hh
      exact Multiplicative.toAdd.injective (congrArg Prod.fst hh)
    · rintro ⟨x,hx⟩
      obtain ⟨k,v,rfl⟩ := short_surjective x
      have hv : v=1 := (shortQuotient_apply k v).symm.trans hx
      refine ⟨Multiplicative.ofAdd k,Subtype.ext ?_⟩
      change short k 1=short k v
      rw [hv])

@[simp] theorem shortKernelEquiv_apply (k : Multiplicative (ZMod 3)) :
    (shortKernelEquiv k : radical₁ (F := (ZMod 3)))=short k.toAdd 1 := rfl

theorem shortExtension_form (v w : V) :
    shortExtension.commutatorValue v w=shortKernelEquiv (Multiplicative.ofAdd (shortForm v w)) :=
  Subtype.ext (shortExtension_commutator v w)

/-- The coordinate involution is literal conjugation by the indicated Atlas torus element. -/
theorem longInvolution_ambient (x : radical₂ (F := (ZMod 3))) :
    (longInvolution x : Model (ZMod 3))=MulAut.conj (torus 1 (-1)) (x:Model (ZMod 3)) := by
  obtain ⟨k,v,rfl⟩ := long_surjective x
  rw [longInvolution_apply]
  change unipotentProduct _=torus 1 (-1)*unipotentProduct _*(torus 1 (-1))⁻¹
  rw [torus_unipotentProduct]
  congr 1
  ext i
  fin_cases i <;> dsimp [torusUnipotentParameters] <;> simp

theorem long_inv (k : (ZMod 3)) (v : V) : (long k v)⁻¹=long (-k) v⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [long_mul]
  simp [longForm,long_one,mul_comm]

/-- The canonical inverted section is explicit in all four root coordinates. -/
theorem longExtension_section (v : V) : longExtension.invertedSection v=long 0 v := by
  apply longExtension.inverted_lift_unique (longExtension.section_inverted v)
  · change longInvolution (long 0 v)=(long 0 v)⁻¹
    rw [longInvolution_apply,long_inv,neg_zero]
  · exact longExtension.quotient_section v |>.trans (longQuotient_apply 0 v).symm

/-- The complete commutator form has its exact cubic-line codomain. -/
theorem longExtension_commutator (v w : V) :
    (longExtension.commutatorValue v w : radical₂ (F := (ZMod 3)))=long (longForm v w) 1 := by
  apply mul_left_cancel (a:=long 0 v*long 0 w)
  rw [←longExtension_section v,←longExtension_section w,←longExtension.section_mul,
    longExtension_section,longExtension_section,longExtension_section,long_mul,long_mul]
  simp [longForm]

/-- The central root parameter as a homomorphism into the literal quotient kernel. -/
def longKernelHom : Multiplicative (ZMod 3) →* longQuotient.ker where
  toFun k := ⟨long k.toAdd 1,MonoidHom.mem_ker.mpr (longQuotient_apply _ _)⟩
  map_one' := Subtype.ext long_one
  map_mul' k l := by
    apply Subtype.ext
    change long (k.toAdd+l.toAdd) 1=long k.toAdd 1*long l.toAdd 1
    rw [long_mul]
    simp [longForm]

@[simp] theorem longKernelHom_apply (k : Multiplicative (ZMod 3)) :
    (longKernelHom k : radical₂ (F := (ZMod 3)))=long k.toAdd 1 := rfl

/-- The kernel is the actual cubic root subgroup, with its additive parameter. -/
noncomputable def longKernelEquiv : Multiplicative (ZMod 3) ≃* longQuotient.ker :=
  MulEquiv.ofBijective longKernelHom (by
    constructor
    · intro k l h
      have hh := congrArg (fun x : longQuotient.ker => longCoordinates.symm x.val) h
      change longCoordinates.symm (long k.toAdd 1)=longCoordinates.symm (long l.toAdd 1) at hh
      rw [longCoordinates_symm,longCoordinates_symm] at hh
      exact Multiplicative.toAdd.injective (congrArg Prod.fst hh)
    · rintro ⟨x,hx⟩
      obtain ⟨k,v,rfl⟩ := long_surjective x
      have hv : v=1 := (longQuotient_apply k v).symm.trans hx
      refine ⟨Multiplicative.ofAdd k,Subtype.ext ?_⟩
      change long k 1=long k v
      rw [hv])

@[simp] theorem longKernelEquiv_apply (k : Multiplicative (ZMod 3)) :
    (longKernelEquiv k : radical₂ (F := (ZMod 3)))=long k.toAdd 1 := rfl

theorem longExtension_form (v w : V) :
    longExtension.commutatorValue v w=longKernelEquiv (Multiplicative.ofAdd (longForm v w)) :=
  Subtype.ext (longExtension_commutator v w)

/-- The radical of the short commutator form is the middle coordinate plane. -/
theorem shortForm_radical (v : V) :
    (∀ w,shortForm v w=0) ↔ v.toAdd 0=0 ∧ v.toAdd 3=0 := by
  constructor
  · intro h
    have h0 := h (Multiplicative.ofAdd ![0,0,0,1])
    have h3 := h (Multiplicative.ofAdd ![1,0,0,0])
    constructor
    · simpa [shortForm] using h0
    · simpa [shortForm] using h3
  · rintro ⟨h0,h3⟩ w
    simp [shortForm,h0,h3]

/-- The radical of the long commutator form is the first coordinate plane. -/
theorem longForm_radical (v : V) :
    (∀ w,longForm v w=0) ↔ v.toAdd 2=0 ∧ v.toAdd 3=0 := by
  constructor
  · intro h
    have h2 := h (Multiplicative.ofAdd ![0,0,0,1])
    have h3 := h (Multiplicative.ofAdd ![0,0,1,0])
    constructor
    · simpa [longForm] using h2
    · simpa [longForm] using h3
  · rintro ⟨h2,h3⟩ w
    simp [longForm,h2,h3]

end Atlas.G2.TernaryCore
