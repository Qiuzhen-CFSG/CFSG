module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.SylowCoordinates
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
/-!
# Fixed spaces and actual commutator lines

Upper-unipotent coordinates on the original V_H compute its fixed space
and prove [A,V_H] = C_{V_H}(A). For each field line in that fixed space,
surjectivity of the original A-parameter constructs u in V_H outside its
fixed space with [A,⟨u⟩] exactly the ambient pullback of that line. Thus the
doubled natural-module argument uses actual commutators and original subgroups.
The fixed space has field dimension m and order q^m; when m=1, containment
and the source line order suffice to identify the original line.

These results do not identify the source V₁ as a field line in the doubled
case and do not recognize the reciprocal transvection action on A.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.3.7(4), cases (i) and (ii), printed p.773.
-/

@[expose] public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] {T : Sylow 2 G} {H A : Subgroup G} {F : BinaryField}
namespace NaturalSylowCoordinates
variable {m : ℕ} (c : NaturalSylowCoordinates T H A F m)
open scoped commutatorElement

/-- The upper fixed space in the actual chosen coordinates. -/
def fixedSpace (_c : NaturalSylowCoordinates T H A F m) :
    Submodule F.Carrier (Fin m → Fin 2 → F.Carrier) where
  carrier := {v | ∀ i, v i 1 = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw i; simp [hv i,hw i]
  smul_mem' := by intro a v hv i; simp [hv i]

/-- Pull a field subspace back to its original ambient subgroup in V_H. -/
def liftSpace (U : Submodule F.Carrier (Fin m → Fin 2 → F.Carrier)) : Subgroup G :=
  (U.toAddSubgroup.toSubgroup.comap c.coordinates.toMonoidHom).map
    (omegaClosure T H).subtype

theorem mem_liftSpace (U : Submodule F.Carrier (Fin m → Fin 2 → F.Carrier))
    (v : omegaClosure T H) :
    (v : G) ∈ c.liftSpace U ↔ (c.coordinates v).toAdd ∈ U := by
  constructor
  · rintro ⟨w,hw,he⟩
    exact (Subtype.ext he : w = v) ▸ hw
  · exact fun hv => ⟨v,hv,rfl⟩

theorem liftSpace_le (U : Submodule F.Carrier (Fin m → Fin 2 → F.Carrier)) :
    c.liftSpace U ≤ omegaClosure T H := map_subtype_le _

def displacement (a : A) (w : omegaClosure T H) : omegaClosure T H :=
  localAction T H (inclusion c.le_local a) w * w⁻¹

theorem displacement_val (a : A) (w : omegaClosure T H) :
    (c.displacement a w : G) = ⁅(a : G),(w : G)⁆ := rfl

theorem displacement_coordinates (a : A) (w : omegaClosure T H) (i : Fin m) :
    (c.coordinates (c.displacement a w)).toAdd i =
      ![(c.parameter a).toAdd * (c.coordinates w).toAdd i 1,0] := by
  simp only [displacement,map_mul,map_inv]
  simp only [toAdd_mul,toAdd_inv,Pi.add_apply,Pi.neg_apply]
  rw [c.intertwines]
  ext j
  fin_cases j <;> simp

theorem mem_fixed_iff (w : omegaClosure T H) :
    (w : G) ∈ centralizer (A : Set G) ↔ ∀ i, (c.coordinates w).toAdd i 1 = 0 := by
  constructor
  · intro hw i
    obtain ⟨a,ha⟩ := c.surjective (Multiplicative.ofAdd 1)
    have hf : localAction T H (inclusion c.le_local a) w = w := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hw a a.property)
    have he := congrFun (c.intertwines a w i) 0
    rw [hf,ha] at he
    simpa using he.symm
  · intro hw a ha
    have he : localAction T H (inclusion c.le_local ⟨a,ha⟩) w = w := by
      apply c.coordinates.injective
      apply Multiplicative.toAdd.injective
      funext i
      rw [c.intertwines]
      ext j
      fin_cases j <;> simp [hw i]
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)

theorem fixed_eq_liftSpace :
    omegaClosure T H ⊓ centralizer (A : Set G) = c.liftSpace c.fixedSpace := by
  apply le_antisymm
  · rintro w ⟨hw,hc⟩
    exact (c.mem_liftSpace c.fixedSpace ⟨w,hw⟩).mpr ((c.mem_fixed_iff ⟨w,hw⟩).mp hc)
  · intro w hw
    have hW := c.liftSpace_le c.fixedSpace hw
    exact ⟨hW,(c.mem_fixed_iff ⟨w,hW⟩).mpr
      ((c.mem_liftSpace c.fixedSpace ⟨w,hW⟩).mp hw)⟩

include c in
/-- The natural action makes its full moved subgroup exactly its fixed space,
for any positive number of copies (and also for zero copies). -/
theorem commutator_eq_fixed :
    ⁅A,omegaClosure T H⁆ = omegaClosure T H ⊓ centralizer (A : Set G) := by
  apply le_antisymm
  · apply commutator_le.mpr
    intro a ha w hw
    have he := c.displacement_coordinates ⟨a,ha⟩ ⟨w,hw⟩
    exact ⟨(c.displacement ⟨a,ha⟩ ⟨w,hw⟩).property,
      (c.mem_fixed_iff (c.displacement ⟨a,ha⟩ ⟨w,hw⟩)).mpr (fun i => by
        rw [he i]; rfl)⟩
  · rintro w ⟨hw,hc⟩
    let w' : omegaClosure T H := ⟨w,hw⟩
    let u := c.coordinates.symm (Multiplicative.ofAdd
      (fun i => ![0,(c.coordinates w').toAdd i 0]))
    obtain ⟨a,ha⟩ := c.surjective (Multiplicative.ofAdd 1)
    have he : c.displacement a u = w' := by
      apply c.coordinates.injective
      apply Multiplicative.toAdd.injective
      funext i
      rw [c.displacement_coordinates,ha]
      have hu : (c.coordinates u).toAdd i = ![0,(c.coordinates w').toAdd i 0] := by
        simp only [u,MulEquiv.apply_symm_apply]
        rfl
      rw [hu]
      ext j
      fin_cases j <;> simp [(c.mem_fixed_iff w').mp hc i]
    have he' : ⁅(a : G),(u : G)⁆ = w := congrArg Subtype.val he
    exact he' ▸
      commutator_mem_commutator a.property u.property

end NaturalSylowCoordinates

namespace NaturalSylowCoordinates
variable {m : ℕ} (c : NaturalSylowCoordinates T H A F m)
open scoped commutatorElement

include c in
private theorem mem_zpowers_eq_one_or (w : omegaClosure T H) {v : G}
    (hv : v ∈ zpowers (w : G)) : v = 1 ∨ v = w := by
  have hw : (w : G) ^ 2 = 1 := by
    have hww : w * w = 1 := by
      apply c.coordinates.injective
      rw [map_mul,map_one]
      apply Multiplicative.toAdd.injective
      change (c.coordinates w).toAdd + (c.coordinates w).toAdd = 0
      ext i j
      exact CharTwo.add_self_eq_zero _
    exact (pow_two (w : G)).trans (congrArg Subtype.val hww)
  obtain ⟨k,rfl⟩ := mem_zpowers_iff.mp hv
  rw [zpow_eq_zpow_emod' k hw]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left; simp [hk]
  · right; simp [hk]

/-- The displacement line of a vector, in the original natural coordinates. -/
def vectorLine (w : omegaClosure T H) :
    Submodule F.Carrier (Fin m → Fin 2 → F.Carrier) :=
  Submodule.span F.Carrier {fun i => ![(c.coordinates w).toAdd i 1,0]}

/-- Every scalar multiple on this line is a single literal commutator. -/
theorem commutator_vector_eq_line (w : omegaClosure T H) :
    ⁅A,zpowers (w : G)⁆ = c.liftSpace (c.vectorLine w) := by
  apply le_antisymm
  · apply commutator_le.mpr
    intro a ha v hv
    rcases c.mem_zpowers_eq_one_or w hv with rfl | rfl
    · simp
    · apply (c.mem_liftSpace (c.vectorLine w) (c.displacement ⟨a,ha⟩ w)).mpr
      apply Submodule.mem_span_singleton.mpr
      refine ⟨(c.parameter ⟨a,ha⟩).toAdd, ?_⟩
      funext i
      rw [c.displacement_coordinates]
      ext j
      fin_cases j <;> simp
  · intro v hv
    have hvW := c.liftSpace_le (c.vectorLine w) hv
    obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp
      ((c.mem_liftSpace (c.vectorLine w) ⟨v,hvW⟩).mp hv)
    obtain ⟨a,ha⟩ := c.surjective (Multiplicative.ofAdd t)
    have he : c.displacement a w = ⟨v,hvW⟩ := by
      apply c.coordinates.injective
      apply Multiplicative.toAdd.injective
      rw [← ht]
      funext i
      rw [c.displacement_coordinates,ha]
      ext j
      fin_cases j <;> simp
    have he' : ⁅(a : G),(w : G)⁆ = v := congrArg Subtype.val he
    exact he' ▸
      commutator_mem_commutator a.property (mem_zpowers (w : G))

/-- Every field line in the fixed space is realized by an actual vector outside
that fixed space. This works for one copy, two copies, and arbitrary multiplicity. -/
theorem exists_vector_commutator (U : Submodule F.Carrier (Fin m → Fin 2 → F.Carrier))
    (hU : Module.finrank F.Carrier U = 1) (hfix : U ≤ c.fixedSpace) :
    ∃ w : omegaClosure T H, (w : G) ∉ centralizer (A : Set G) ∧
      ⁅A,zpowers (w : G)⁆ = c.liftSpace U := by
  have hne : U ≠ ⊥ := by
    intro he
    rw [he,finrank_bot] at hU
    exact Nat.zero_ne_one hU
  obtain ⟨v,hv,hv0⟩ := U.ne_bot_iff.mp hne
  let w := c.coordinates.symm (Multiplicative.ofAdd (fun i => ![0,v i 0]))
  have hw (i : Fin m) : (c.coordinates w).toAdd i = ![0,v i 0] := by
    simp only [w,MulEquiv.apply_symm_apply]
    rfl
  have hline : c.vectorLine w = U := by
    have he : (fun i => ![(c.coordinates w).toAdd i 1,0]) = v := by
      funext i
      rw [hw]
      ext j
      fin_cases j
      · rfl
      · exact (hfix hv i).symm
    exact (congrArg (fun z => Submodule.span F.Carrier {z}) he).trans
      (eq_span_singleton_of_mem_of_finrank_eq_one hU hv hv0).symm
  refine ⟨w,?_,by rw [c.commutator_vector_eq_line,hline]⟩
  intro hc
  apply hv0
  ext i j
  fin_cases j
  · have hz := (c.mem_fixed_iff w).mp hc i
    rw [hw] at hz
    exact hz
  · exact hfix hv i

end NaturalSylowCoordinates

namespace NaturalSylowCoordinates
variable {m : ℕ} (c : NaturalSylowCoordinates T H A F m)

/-- Forget the zero second coordinates of the fixed space. -/
def fixedSpaceEquiv : c.fixedSpace ≃ₗ[F.Carrier] (Fin m → F.Carrier) where
  toFun v i := v.val i 0
  invFun v := ⟨fun i => ![v i,0],fun _ => rfl⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    ext j
    fin_cases j
    · rfl
    · exact (v.property i).symm
  right_inv v := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_fixedSpace : Module.finrank F.Carrier c.fixedSpace = m := by
  rw [c.fixedSpaceEquiv.finrank_eq]
  simp

/-- A coordinate subspace and its literal ambient pullback have equal size. -/
def liftSpaceEquiv (U : Submodule F.Carrier (Fin m → Fin 2 → F.Carrier)) :
    c.liftSpace U ≃ U where
  toFun v := ⟨(c.coordinates ⟨v,c.liftSpace_le U v.property⟩).toAdd,
    (c.mem_liftSpace U ⟨v,c.liftSpace_le U v.property⟩).mp v.property⟩
  invFun u := ⟨(c.coordinates.symm (Multiplicative.ofAdd u.val) : G),
    (c.mem_liftSpace U _).mpr (by
      rw [MulEquiv.apply_symm_apply]
      exact u.property)⟩
  left_inv v := by
    apply Subtype.ext
    change (c.coordinates.symm (c.coordinates ⟨v,c.liftSpace_le U v.property⟩) : G) = v
    rw [MulEquiv.symm_apply_apply]
  right_inv u := by
    apply Subtype.ext
    change (c.coordinates (c.coordinates.symm (Multiplicative.ofAdd u.val))).toAdd = u.val
    rw [MulEquiv.apply_symm_apply]
    rfl

include c in
theorem card_fixed :
    Nat.card ↥(omegaClosure T H ⊓ centralizer (A : Set G)) = Nat.card F.Carrier ^ m := by
  rw [c.fixed_eq_liftSpace, Nat.card_congr (c.liftSpaceEquiv c.fixedSpace),
    Nat.card_congr c.fixedSpaceEquiv.toEquiv,Nat.card_fun,Nat.card_fin]

/-- In the one-copy case, containment and the source line order identify the
original line with the full commutator. No line-transporter premise is used. -/
theorem one_copy_line_eq_commutator {U : Subgroup G}
    (c : NaturalSylowCoordinates T H A F 1)
    (hU : U ≤ omegaClosure T H ⊓ centralizer (A : Set G))
    (hcard : Nat.card U = Nat.card F.Carrier) : U = ⁅A,omegaClosure T H⁆ := by
  rw [c.commutator_eq_fixed]
  let : Finite ↥(omegaClosure T H ⊓ centralizer (A : Set G)) := by
    apply Nat.finite_of_card_ne_zero
    rw [c.card_fixed,pow_one]
    exact Nat.card_pos.ne'
  apply eq_of_le_of_card_ge hU
  rw [c.card_fixed,pow_one,hcard]

end NaturalSylowCoordinates

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
