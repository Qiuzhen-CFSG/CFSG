module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.CartanActions
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.NaturalShears

/-!
# The long-root subsystem and its actual rank-one action

The central commutator of the first two long roots lands in the third.
Their structural commutations and geometric disjointness make the last
two roots faithful additive coordinates. Transvection generation gives
the action of the entire long SL₂ on their product, with upper roots
acting as shears and the Weyl element exchanging coordinates.

The rank-one braid normalizes the shear at one. The short reflection
exchanges the two commutator inputs and fixes the output, forcing symmetry
of its coefficient. NaturalShears supplies multiplicativity of the
coefficient operators, so symmetry identifies the coefficient with field
multiplication. The same actual action then gives every signed long-root
weight of the long coroot. No tensor-module identification, simplicity,
perfectness or field-size restriction is used.

LongRootApplication supplies the commutator containment and disjointness
from the canonical roots of the original quotient, including after whole
pinning scalar alignment. This removes the long-twisted equation from the
remaining source module obligations.

Source: Fong--Seitz I (6E)(b), printed p.43; II §7 and (9.31), printed p.219.
Commutators here are xyx⁻¹y⁻¹. The source application proves the conversion
to right commutators using characteristic-two root involutions.
-/

@[expose] public noncomputable section
open Subgroup Theory.PSL2.SemilinearCoverage
open scoped commutatorElement
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.LongAction
variable {F Y : Type*} [Field F] [CharP F 2] [Group Y] {σ : F ≃+* F}
variable (p : RankOnePair σ Y) (c : p.PositiveCommutations)
  (hf : Function.Injective p.longMap)
  (hd : Disjoint (p.longOrbit 1).range (p.longOrbit 2).range)
  (hc : ∀ a b : (ScalarMarking.SourceFixed (σ := σ)), ⁅p.l 1 b,p.l 0 a⁆ ∈ (p.longOrbit 2).range)
local notation "K" => ScalarMarking.SourceFixed (σ := σ)

include hf in
private theorem linj (i : Fin 3) : Function.Injective (p.l i) :=
  (p.longOrbit_injective hf i).comp Multiplicative.ofAdd.injective

private theorem ladd (i : Fin 3) (a b : K) : p.l i (a+b) = p.l i a*p.l i b :=
  (p.longOrbit i).map_mul _ _
private theorem lzero (i : Fin 3) : p.l i 0 = 1 := (p.longOrbit i).map_one
private theorem linv (i : Fin 3) (a : K) : (p.l i a)⁻¹ = p.l i a := by
  rw [← map_inv, ← ofAdd_neg, CharTwo.neg_eq]

/-- Ordered coordinates on the two commuting long-root groups. -/
def coordinates : Multiplicative K × Multiplicative K →* Y where
  toFun z := p.longOrbit 1 z.1 * p.longOrbit 2 z.2
  map_one' := by change p.longOrbit 1 1 * p.longOrbit 2 1 = 1; simp only [map_one, mul_one]
  map_mul' z v := by
    simp only [Prod.fst_mul,Prod.snd_mul,map_mul]
    exact (c.long1_long2 v.1.toAdd z.2.toAdd).mul_mul_mul_comm _ _

include hf hd in
theorem coordinates_injective : Function.Injective (coordinates p c) := by
  intro z v h
  have hh : ((⟨p.longOrbit 1 z.1,⟨_,rfl⟩⟩,⟨p.longOrbit 2 z.2,⟨_,rfl⟩⟩) :
      (p.longOrbit 1).range × (p.longOrbit 2).range) =
      (⟨p.longOrbit 1 v.1,⟨_,rfl⟩⟩,⟨p.longOrbit 2 v.2,⟨_,rfl⟩⟩) :=
    Subgroup.mul_injective_of_disjoint hd h
  exact Prod.ext
    (p.longOrbit_injective hf 1 (congrArg (fun z => (z.1 : Y)) hh))
    (p.longOrbit_injective hf 2 (congrArg (fun z => (z.2 : Y)) hh))

/-- The coefficient is extracted from the actual central commutator. -/
def coefficient (a b : K) : K := (hc a b).choose.toAdd

theorem coefficient_spec (a b : K) :
    p.l 2 (coefficient p hc a b) = ⁅p.l 1 b,p.l 0 a⁆ :=
  (hc a b).choose_spec

theorem uni_first (a b : K) :
    p.longMap (uni a)*p.l 1 b*(p.longMap (uni a))⁻¹ =
      p.l 1 b*p.l 2 (coefficient p hc a b) := by
  rw [coefficient_spec]
  change p.l 0 a * p.l 1 b * (p.l 0 a)⁻¹ = _
  simp only [commutatorElement_def, linv]
  have hb : p.l 1 b*p.l 1 b=1 := by rw [← ladd,CharTwo.add_self_eq_zero,lzero]
  simp only [←mul_assoc,hb,one_mul]

private theorem uni_coordinates (a : K) (z : Multiplicative K × Multiplicative K) :
    p.longMap (uni a)*coordinates p c z*(p.longMap (uni a))⁻¹ =
      coordinates p c (z.1,.ofAdd (coefficient p hc a z.1.toAdd+z.2.toAdd)) := by
  change (MulAut.conj (p.longMap (uni a))) (p.l 1 z.1.toAdd*p.l 2 z.2.toAdd) = _
  rw [map_mul]
  change (p.longMap (uni a)*p.l 1 z.1.toAdd*(p.longMap (uni a))⁻¹)*
    (p.l 0 a*p.l 2 z.2.toAdd*(p.l 0 a)⁻¹) = _
  rw [uni_first p hc, (c.long0_long2 a z.2.toAdd).mul_inv_cancel]
  change _ = p.l 1 z.1.toAdd*p.l 2 _
  rw [ladd, mul_assoc]

private theorem weyl_coordinates (z : Multiplicative K × Multiplicative K) :
    p.dihedral.B (coordinates p c z) = coordinates p c (z.2,z.1) := by
  change p.dihedral.B (p.l 1 z.1.toAdd*p.l 2 z.2.toAdd) = _
  rw [map_mul, p.l_two, p.dihedral.B_B]
  exact (c.long1_long2 z.2.toAdd z.1.toAdd).symm.eq

private theorem normalizes_of_involutive (x : Y) (hx : x*x=1)
    (h : ∀ z, x*coordinates p c z*x⁻¹ ∈ (coordinates p c).range) :
    x ∈ normalizer ((coordinates p c).range : Set Y) := by
  have hi : x⁻¹=x := inv_eq_of_mul_eq_one_right hx
  apply mem_normalizer_iff.mpr
  intro y
  constructor
  · rintro ⟨z,rfl⟩
    exact h z
  · rintro ⟨z,hz⟩
    have hh := h z
    rw [hz] at hh
    have he : x*(x*y*x⁻¹)*x⁻¹=y := by
      rw [hi]
      calc
        _ = (x*x)*y*(x*x) := by group
        _ = y := by rw [hx,one_mul,mul_one]
    rw [he] at hh
    exact hh

include hc in
private theorem normalizes_uni (a : K) :
    p.longMap (uni a) ∈ normalizer ((coordinates p c).range : Set Y) := by
  apply normalizes_of_involutive p c
  · change p.l 0 a*p.l 0 a=1
    rw [← ladd,CharTwo.add_self_eq_zero,lzero]
  · intro z
    exact ⟨_,(uni_coordinates p c hc a z).symm⟩

private theorem normalizes_weyl :
    p.longMap (weyl K) ∈ normalizer ((coordinates p c).range : Set Y) := by
  apply normalizes_of_involutive p c p.dihedral.b p.dihedral.b_sq
  intro z
  exact ⟨_,(weyl_coordinates p c z).symm⟩

include hc in
theorem normalizes (g : SL2 K) :
    p.longMap g ∈ normalizer ((coordinates p c).range : Set Y) := by
  apply Matrix.SL2.transvection_induction
    (fun g => p.longMap g ∈ normalizer ((coordinates p c).range : Set Y))
  · intro i j hij a
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact normalizes_uni p c hc a
    · rw [lower_transvection_eq_weyl_uni,map_mul,map_mul]
      exact mul_mem (mul_mem (normalizes_weyl p c) (normalizes_uni p c hc a))
        (normalizes_weyl p c)
    · exact (hij rfl).elim
  · intro a b ha hb
    rw [map_mul]
    exact mul_mem ha hb

/-- The entire source long rank-one group acts on these two literal roots. -/
def action : SL2 K →* MulAut (Multiplicative K × Multiplicative K) :=
  (MulAut.congr (MonoidHom.ofInjective (coordinates_injective p c hf hd)).symm).toMonoidHom.comp
    ((coordinates p c).range.normalizerMonoidHom.comp
      (p.longMap.codRestrict _ (normalizes p c hc)))

/-- This action intertwines the original coordinate product and conjugation. -/
theorem action_intertwines (g : SL2 K) (z : Multiplicative K × Multiplicative K) :
    coordinates p c (action p c hf hd hc g z) =
      p.longMap g * coordinates p c z * (p.longMap g)⁻¹ := by
  exact congrArg Subtype.val
    ((MonoidHom.ofInjective (coordinates_injective p c hf hd)).apply_symm_apply _)

theorem action_uni (a : K) (z : Multiplicative K × Multiplicative K) :
    action p c hf hd hc (uni a) z =
      (z.1,.ofAdd (coefficient p hc a z.1.toAdd+z.2.toAdd)) := by
  apply coordinates_injective p c hf hd
  rw [action_intertwines,uni_coordinates]

theorem action_weyl (a b : Multiplicative K) :
    action p c hf hd hc (weyl K) (a,b) = (b,a) := by
  apply coordinates_injective p c hf hd
  rw [action_intertwines]
  exact weyl_coordinates p c (a,b)


include hf in
theorem coefficient_zero (a : K) : coefficient p hc a 0 = 0 := by
  apply linj p hf 2
  rw [coefficient_spec,lzero,lzero,commutatorElement_one_left]

/-- The additive coefficient operator of the actual upper-root action. -/
def shear (a : K) : K →+ K where
  toFun := coefficient p hc a
  map_zero' := coefficient_zero p hf hc a
  map_add' b d := by
    have hh := map_mul (action p c hf hd hc (uni a)) (.ofAdd b,.ofAdd 0) (.ofAdd d,.ofAdd 0)
    simp only [Prod.mk_mul_mk,← ofAdd_add,add_zero,action_uni,toAdd_ofAdd] at hh
    exact congrArg (fun z : Multiplicative K × Multiplicative K => z.2.toAdd) hh

theorem shear_one (a : K) : shear p c hf hd hc 1 a = a := by
  have hbraid : uni (1 : K)*weyl K*uni 1 = weyl K*uni 1*weyl K := by
    ext k l
    fin_cases k <;> fin_cases l <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two,CharTwo.add_self_eq_zero]
  have hh := congrArg
    (fun g : SL2 K => action p c hf hd hc g (.ofAdd a,.ofAdd 0)) hbraid
  simp only [map_mul,MulAut.mul_apply,action_uni,action_weyl,toAdd_ofAdd] at hh
  have he := congrArg (fun z : Multiplicative K × Multiplicative K => z.1.toAdd) hh
  change coefficient p hc 1 a = a
  simpa only [coefficient_zero p hf hc,add_zero,zero_add,toAdd_ofAdd] using he

include hf in
/-- The short reflection exchanges the two entries and fixes the output root. -/
theorem coefficient_comm (a b : K) : coefficient p hc a b = coefficient p hc b a := by
  apply linj p hf 2
  have hh := congrArg p.dihedral.A (coefficient_spec p hc a b)
  have hA (x : K) : p.dihedral.A (p.l 2 x) = p.l 2 x := p.orthogonalLong x
  rw [hA,map_commutatorElement,p.l_one,p.dihedral.A_A,← p.l_one] at hh
  rw [hh,← commutatorElement_inv,← coefficient_spec,linv]

include c hf hd hc

/-- The central commutator coefficient is forced to be field multiplication.
This uses both source reflections and the whole SL₂ action, also over F₂. -/
theorem coefficient_mul (a b : K) : coefficient p hc a b = a*b := by
  have hm := NaturalShears.parameter_mul (action p c hf hd hc) (shear p c hf hd hc)
    (fun b a d => action_uni p c hf hd hc b (.ofAdd a,.ofAdd d))
    (action_weyl p c hf hd hc) (shear_one p c hf hd hc) a b 1
  change coefficient p hc (a*b) 1 = coefficient p hc a (coefficient p hc b 1) at hm
  have hone (x : K) : coefficient p hc x 1 = x :=
    (coefficient_comm p hf hc x 1).trans (shear_one p c hf hd hc x)
  rw [hone,hone] at hm
  exact hm.symm

/-- The literal source long–long commutator, with no coefficient premise. -/
theorem commutator (a b : K) : ⁅p.l 1 b,p.l 0 a⁆ = p.l 2 (a*b) := by
  rw [← coefficient_spec p hc,coefficient_mul p c hf hd hc]

/-- Ordered exchange in the positive presentation convention. -/
theorem exchange (a b : K) : p.l 0 a*p.l 1 b = p.l 1 b*p.l 0 a*p.l 2 (a*b) := by
  have hh := uni_first p hc a b
  rw [coefficient_mul p c hf hd hc] at hh
  have he := congrArg (fun y => y*p.l 0 a) hh
  change (p.l 0 a*p.l 1 b*(p.l 0 a)⁻¹)*p.l 0 a = _ at he
  simp only [mul_assoc,inv_mul_cancel,mul_one] at he
  rw [(c.long0_long2 a (a*b)).symm.eq] at he
  exact he.trans (mul_assoc _ _ _).symm

/-- The same action gives the two non-simple long-root weights. -/
theorem tor_coordinates (t : Kˣ) (a b : K) :
    p.longMap (tor t)*(p.l 1 a*p.l 2 b)*(p.longMap (tor t))⁻¹ =
      p.l 1 (t.val⁻¹*a)*p.l 2 (t.val*b) := by
  have hh := NaturalShears.action_tor (action p c hf hd hc) (shear p c hf hd hc)
    (fun b a d => action_uni p c hf hd hc b (.ofAdd a,.ofAdd d))
    (action_weyl p c hf hd hc) (shear_one p c hf hd hc) t a b
  have he := congrArg (coordinates p c) hh
  rw [action_intertwines] at he
  change p.longMap (tor t)*(p.l 1 a*p.l 2 b)*(p.longMap (tor t))⁻¹ =
    p.l 1 (coefficient p hc (t⁻¹).val a)*p.l 2 (coefficient p hc t.val b) at he
  simpa only [coefficient_mul p c hf hd hc,Units.val_inv_eq_inv_val] using he

/-- All three positive long-root characters of the long coroot. -/
theorem tor_long (t : Kˣ) (i : Fin 3) (a : K) :
    p.longMap (tor t)*p.l i a*(p.longMap (tor t))⁻¹ =
      p.l i (![t.val^2,t.val⁻¹,t.val] i*a) := by
  fin_cases i
  · change p.longMap (tor t)*p.longMap (uni a)*(p.longMap (tor t))⁻¹ = _
    rw [← map_inv,← map_mul,← map_mul,Borel_conj_uni]
    · rfl
    · exact (mem_Borel_iff _).mpr (by simp)
  · change p.longMap (tor t)*p.l 1 a*(p.longMap (tor t))⁻¹ = p.l 1 (t.val⁻¹*a)
    simpa only [lzero,mul_one,mul_zero] using tor_coordinates p c hf hd hc t a 0
  · change p.longMap (tor t)*p.l 2 a*(p.longMap (tor t))⁻¹ = p.l 2 (t.val*a)
    simpa only [lzero,one_mul,mul_zero] using tor_coordinates p c hf hd hc t 0 a

omit c hf hd hc in
private theorem W_tor (t : Kˣ) : p.dihedral.W (p.longMap (tor t)) = p.longMap (tor t⁻¹) := by
  rw [p.W_longMap]
  change p.longMap (weyl K)*p.longMap (tor t)*(p.longMap (weyl K))⁻¹ = _
  rw [← map_inv,← map_mul,← map_mul,weyl_tor]

/-- Opposition gives inverse characters on the three negative long roots. -/
theorem tor_signed_long (t : Kˣ) (positive : Bool) (i : Fin 3) (a : K) :
    p.longMap (tor t)*p.signedValue positive (p.l i a)*(p.longMap (tor t))⁻¹ =
      p.signedValue positive (p.l i
        ((if positive then ![t.val^2,t.val⁻¹,t.val] i
          else (![t.val^2,t.val⁻¹,t.val] i)⁻¹)*a)) := by
  cases positive
  · have hh := congrArg p.dihedral.W (tor_long p c hf hd hc t⁻¹ i a)
    simp only [map_mul,map_inv,W_tor,inv_inv,Units.val_inv_eq_inv_val] at hh
    change p.longMap (tor t)*p.dihedral.W (p.l i a)*(p.longMap (tor t))⁻¹ =
      p.dihedral.W (p.l i ((![(t.val)^2,t.val⁻¹,t.val] i)⁻¹*a))
    rw [hh]
    congr 3
    fin_cases i <;> simp
  · exact tor_long p c hf hd hc t i a

/-- These weights use the actual fixed-field marking in the signed presentation. -/
theorem hB_signed_long {n : ℕ} {hn : 0 < n}
    (e : ScalarMarking (binaryParameters n hn) σ)
    (t : Kˣ) (positive : Bool) (i : Fin 3) (a : K) :
    (p.signedRoots e).hB (Units.map e.fixed.toMonoidHom t)*
      (p.signedRoots e).longSigned positive i (e.fixed a)*
      ((p.signedRoots e).hB (Units.map e.fixed.toMonoidHom t))⁻¹ =
    (p.signedRoots e).longSigned positive i
      (e.fixed ((if positive then ![t.val^2,t.val⁻¹,t.val] i
        else (![t.val^2,t.val⁻¹,t.val] i)⁻¹)*a)) := by
  rw [p.hB_parameter,p.signedRoots_long,p.signedRoots_long]
  exact tor_signed_long p c hf hd hc t positive i a

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.LongAction
