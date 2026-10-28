module
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Structure
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Context
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.NormalizerControl.Geometry
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.NormalizerControl.ExceptionalAction.Local

/-!
# Exceptional action forces seven-divisibility and fusion

A normalizer element outside the actual involution centralizer moves z. Its
induced automorphism of Q preserves F and V by their intrinsic descriptions.
Together with the local six-point orbit, this makes the orbit of z under
N(F) ∩ N(V) all seven nonidentity points of V. Orbit-stabilizer gives the
required divisor of |N(F)|. Transport of a commuting square root of z then
gives fusion of the two marked involutions.

This auxiliary argument uses the genuine centralizer equivalence in the
second nonsplit case of Huppert--Blackburn III, XII.1.18(b), printed p.314.
It assumes neither normalizer control nor splitting nor recognition.
-/
namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.NormalizerControl.ExceptionalAction
open NonsplitModels Model Subgroup
set_option maxRecDepth 100000
universe u
variable {G : Type u} [Group G] (D : LocalData G) (e : D.centralizer ≃* Second)

private noncomputable def induced (g : G)
    (hg : g ∈ normalizer (ambientExceptionalSubgroup D e : Set G)) : MulAut exceptionalSubgroup :=
  let E := exceptionalSubgroup.equivMapOfInjective (embedding D e) (embedding_injective D e)
  (E.trans ((ambientExceptionalSubgroup D e).normalizerMonoidHom ⟨g, hg⟩)).trans E.symm

private theorem induced_embedding (g : G)
    (hg : g ∈ normalizer (ambientExceptionalSubgroup D e : Set G)) (x : exceptionalSubgroup) :
    embedding D e (induced D e g hg x) = g * embedding D e x * g⁻¹ := by
  let E := exceptionalSubgroup.equivMapOfInjective (embedding D e) (embedding_injective D e)
  have h := congrArg (fun q : ambientExceptionalSubgroup D e => (q : G))
    (E.apply_symm_apply ((ambientExceptionalSubgroup D e).normalizerMonoidHom ⟨g, hg⟩ (E x)))
  exact h

private theorem normalizes_image (g : G)
    (hg : g ∈ normalizer (ambientExceptionalSubgroup D e : Set G))
    (K : Subgroup Second) (hK : K ≤ exceptionalSubgroup)
    (hstable : ∀ x : exceptionalSubgroup,
      (induced D e g hg x : Second) ∈ K ↔ (x : Second) ∈ K) :
    g ∈ normalizer (K.map (embedding D e) : Set G) := by
  intro x
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨induced D e g hg ⟨q, hK hq⟩, (hstable ⟨q, hK hq⟩).mpr hq,
      induced_embedding D e g hg _⟩
  · rintro ⟨q, hq, he⟩
    let a := induced D e g hg
    let r := a.symm ⟨q, hK hq⟩
    have har : a r = ⟨q, hK hq⟩ := a.apply_symm_apply _
    have hr : (r : Second) ∈ K := (hstable r).mp (by
      change (a r : Second) ∈ K
      rw [har]
      exact hq)
    refine ⟨r, hr, ?_⟩
    apply (MulAut.conj g).injective
    change g * embedding D e r * g⁻¹ = g * x * g⁻¹
    rw [← induced_embedding D e g hg r]
    change embedding D e (a r : Second) = g * x * g⁻¹
    rw [har]
    exact he

private theorem local_normalizes_image (K : Subgroup Second)
    (hK : ∀ a x : Second, x ∈ K → a * x * a⁻¹ ∈ K) (a : Second) :
    embedding D e a ∈ normalizer (K.map (embedding D e) : Set G) := by
  intro x
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨a * q * a⁻¹, hK a q hq, by simp only [map_mul, map_inv]⟩
  · intro hx
    have hh : embedding D e a⁻¹ * (embedding D e a * x * (embedding D e a)⁻¹) *
        (embedding D e a⁻¹)⁻¹ ∈ K.map (embedding D e) := by
      obtain ⟨q, hq, he⟩ := hx
      exact ⟨a⁻¹ * q * (a⁻¹)⁻¹, hK a⁻¹ q hq, by simp only [map_mul, map_inv, he]⟩
    change x ∈ K.map (embedding D e)
    simpa only [map_inv, inv_inv, mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using hh

private def zQ : exceptionalSubgroup :=
  ⟨centralPoint, fourGroup_le_exceptionalSubgroup
    (threeGroup_le_fourGroup centralPoint_mem_threeGroup)⟩

private theorem moved_z (g : G)
    (hg : g ∈ normalizer (ambientExceptionalSubgroup D e : Set G))
    (hmove : g ∉ D.centralizer) : induced D e g hg zQ ≠ zQ := by
  intro h
  have he := induced_embedding D e g hg zQ
  rw [h] at he
  change embedding D e centralPoint = g * embedding D e centralPoint * g⁻¹ at he
  rw [embedding_centralPoint] at he
  apply hmove
  exact mem_centralizer_singleton_iff.mpr (by
    have hh := congrArg (· * g) he
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh.symm)

private theorem ambient_fusion (g : G)
    (hg : g ∈ normalizer (ambientExceptionalSubgroup D e : Set G))
    (hmove : g ∉ D.centralizer) :
    IsConj (embedding D e outerPoint) (embedding D e squarePoint) := by
  let a := induced D e g hg
  let y : exceptionalSubgroup := ⟨squarePoint, squarePoint_mem_exceptionalSubgroup⟩
  let r : exceptionalSubgroup := ⟨element 36, squarePoint_commuting_root.1⟩
  have hr : r ^ 2 = zQ := Subtype.ext squarePoint_commuting_root.2.2
  have hq : (a y : Second) ∉ fourGroup :=
    fun h => squarePoint_not_mem_fourGroup ((four_invariant a y).mp h)
  have hy2 : y ^ 2 = 1 := Subtype.ext (by
    rw [← squarePoint_order]
    exact pow_orderOf_eq_one squarePoint)
  have hc : r * y = y * r := Subtype.ext squarePoint_commuting_root.2.1
  have haz : a zQ ≠ 1 := by
    intro h
    have h' : zQ = 1 := a.injective (h.trans a.map_one.symm)
    exact centralPoint_ne_one (congrArg Subtype.val h')
  have hf := square_fusion (a y) (a r) hq
    (by simpa only [map_pow, map_one] using congrArg a hy2)
    (by simpa only [map_mul] using congrArg a hc)
    (by simpa only [← map_pow, hr] using haz)
    (by
      rw [← map_pow, hr]
      intro h
      exact moved_z D e g hg hmove (Subtype.ext h))
  have hf' := (embedding D e).map_isConj hf
  apply hf'.trans
  apply IsConj.symm
  exact isConj_iff.mpr ⟨g, (induced_embedding D e g hg y).symm⟩

private theorem seven_divides [Finite G] (g : G)
    (hg : g ∈ normalizer (ambientExceptionalSubgroup D e : Set G))
    (hmove : g ∉ D.centralizer) :
    7 ∣ Nat.card (normalizer (ambientFourGroup D e : Set G)) := by
  classical
  let V := threeGroup.map (embedding D e)
  let L := normalizer (ambientFourGroup D e : Set G) ⊓ normalizer (V : Set G)
  let : MulDistribMulAction L V := MulDistribMulAction.compHom V (Subgroup.inclusion (show L ≤ normalizer (V : Set G) from inf_le_right))
  have hlocal (a : Second) : embedding D e a ∈ L :=
    ⟨local_normalizes_image D e fourGroup four_conj a,
      local_normalizes_image D e threeGroup three_conj a⟩
  have hgL : g ∈ L :=
    ⟨normalizes_image D e g hg fourGroup fourGroup_le_exceptionalSubgroup
      (four_invariant (induced D e g hg)),
     normalizes_image D e g hg threeGroup
      (threeGroup_le_fourGroup.trans fourGroup_le_exceptionalSubgroup)
      (three_invariant (induced D e g hg))⟩
  let z : V := ⟨embedding D e centralPoint, ⟨centralPoint, centralPoint_mem_threeGroup, rfl⟩⟩
  let b : L := ⟨g, hgL⟩
  let w : exceptionalSubgroup := induced D e g hg zQ
  have hw : (w : Second) ∈ threeGroup :=
    (three_invariant (induced D e g hg) zQ).mpr centralPoint_mem_threeGroup
  have hw1 : (w : Second) ≠ 1 := by
    intro h
    have h' : zQ = 1 := (induced D e g hg).injective
      ((Subtype.ext h).trans (induced D e g hg).map_one.symm)
    exact centralPoint_ne_one (congrArg Subtype.val h')
  have hwz : (w : Second) ≠ centralPoint :=
    fun h => moved_z D e g hg hmove (Subtype.ext h)
  have hbw : ((b • z : V) : G) = embedding D e w :=
    (induced_embedding D e g hg zQ).symm
  have hz1 : z ≠ 1 := by
    intro h
    exact centralPoint_ne_one ((embedding_injective D e)
      ((congrArg Subtype.val h).trans (map_one (embedding D e)).symm))
  have ho : MulAction.orbit L z = {v : V | v ≠ 1} := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩ h
      have h' := congrArg (fun x : V => a⁻¹ • x) h
      apply hz1
      simpa only [inv_smul_smul, smul_one] using h'
    · intro hv
      by_cases hvz : v = z
      · rw [hvz]
        exact MulAction.mem_orbit_self z
      obtain ⟨q, hq, he⟩ := v.property
      have hq1 : q ≠ 1 := by
        intro h
        apply hv
        apply Subtype.ext
        change (v : G) = 1
        simpa only [h, map_one] using he.symm
      have hqz : q ≠ centralPoint := by
        intro h
        apply hvz
        exact Subtype.ext (by simpa only [h] using he.symm)
      obtain ⟨a, ha⟩ := isConj_iff.mp (three_fusion w q hw hq hw1 hwz hq1 hqz)
      refine ⟨(⟨embedding D e a, hlocal a⟩ : L) * b, ?_⟩
      change ((⟨embedding D e a, hlocal a⟩ : L) * b) • z = v
      rw [mul_smul]
      apply Subtype.ext
      change embedding D e a * ((b • z : V) : G) * (embedding D e a)⁻¹ = (v : G)
      rw [hbw, ← map_inv, ← map_mul, ← map_mul, ha, he]
  have hV : Nat.card V = 8 := by
    exact (card_map_of_injective (embedding_injective D e)).trans threeGroup_card
  have horbit : Nat.card (MulAction.orbit L z) = 7 := by
    rw [ho]
    change Nat.card {v : V // ¬ v = 1} = 7
    let := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hV]
  have hd : 7 ∣ Nat.card L := by
    have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup L z)
    rw [Nat.card_prod, horbit] at hc
    exact ⟨_, hc.symm⟩
  exact hd.trans (card_dvd_of_le (show L ≤ normalizer (ambientFourGroup D e : Set G) from inf_le_left))

end Theory.GroupTheory.HeldM22A10.SecondExclusion.NormalizerControl.ExceptionalAction

namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.NormalizerControl
open NonsplitModels Subgroup

/-- Exceptional action on Q forces seven-divisibility and the marked ambient fusion. -/
public theorem exceptional_action {G : Type*} [Group G] [Finite G]
    (D : LocalData G) (e : D.centralizer ≃* Second) (g : G)
    (hg : g ∈ normalizer (ambientExceptionalSubgroup D e : Set G))
    (hmove : g ∉ D.centralizer) :
    7 ∣ Nat.card (normalizer (ambientFourGroup D e : Set G)) ∧
      IsConj (embedding D e outerPoint) (embedding D e squarePoint) := by
  exact ⟨ExceptionalAction.seven_divides D e g hg hmove,
    ExceptionalAction.ambient_fusion D e g hg hmove⟩

end Theory.GroupTheory.HeldM22A10.SecondExclusion.NormalizerControl
