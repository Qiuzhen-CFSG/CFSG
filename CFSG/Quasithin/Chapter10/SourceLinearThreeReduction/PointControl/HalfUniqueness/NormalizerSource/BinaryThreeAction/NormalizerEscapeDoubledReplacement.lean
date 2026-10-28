module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeDoubledThompson
public import CFSG.Quasithin.ChapterB.Section02.RankLifting

/-!
# Maximum elementary replacement on the full doubled core

Each nontrivial maximum elementary image is the marked shear four-group,
whose fixed subgroup has order sixteen. The exact cardinal bound therefore
makes C C_A(C) another maximum elementary subgroup. A trivial image already
centralizes the full elementary core. Thus the full core lies in the actual
Thompson subgroup, without discarding its multiplicity action kernel.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open BinaryLinearThree BinaryLinearThree.DoubledOffenders
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS
variable {J : Type*} [Group J] [Finite J] {κ : GroupClass} {L R : Subgroup J}
    {h : Input κ L R} {q : AbelianCore.NaturalQuotient h 2} {P : Sylow 2 J}

private theorem coordinates_fixed_iff (d : DoubledCoreAction h q P)
    (A : Subgroup J) (x : commutatorCore L) :
    (d.coordinates x).toAdd ∈ fixedSpace τ (A.map d.actor) ↔
      (x : J) ∈ centralizer (A : Set J) := by
  let := h.component_normal
  constructor
  · intro hx a ha
    let y : commutatorCore L := ⟨a*x*a⁻¹,
      (inferInstance : (commutatorCore L).Normal).conj_mem x x.property a⟩
    have he : d.coordinates y = d.coordinates x := by
      apply Multiplicative.toAdd.injective
      exact (d.equivariant a x y rfl).trans (hx ⟨d.actor a,mem_map_of_mem _ ha⟩)
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (d.coordinates.injective he))
  · intro hx
    rintro ⟨_,a,ha,rfl⟩
    have he : (x : J) = a*x*a⁻¹ := by rw [hx a ha,mul_inv_cancel_right]
    exact (d.equivariant a x x he).symm

private theorem coordinates_kernel (d : DoubledCoreAction h q P) :
    d.actor.ker = centralizer (commutatorCore L : Set J) := by
  ext a
  constructor
  · intro ha x hx
    have hf : (d.coordinates ⟨x,hx⟩).toAdd ∈ fixedSpace τ ((zpowers a).map d.actor) := by
      have hh : (zpowers a).map d.actor = ⊥ :=
        (Subgroup.map_eq_bot_iff _).mpr (zpowers_le.mpr ha)
      rw [hh]
      intro b
      change τ (b : D) _ = _
      rw [mem_bot.mp b.property]
      rfl
    exact ((coordinates_fixed_iff d _ ⟨x,hx⟩).mp hf a (mem_zpowers a)).symm
  · intro ha
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨x,rfl⟩ := d.coordinates.surjective (Multiplicative.ofAdd v)
    have he : (x : J) = a*x*a⁻¹ := by rw [←ha x x.property,mul_inv_cancel_right]
    exact (d.equivariant a x x he).symm

private def fixedCoordinates (d : DoubledCoreAction h q P) (A : Subgroup J) :
    (commutatorCore L ⊓ centralizer (A : Set J) : Subgroup J) ≃
      fixedSpace τ (A.map d.actor) where
  toFun x := ⟨(d.coordinates ⟨x,x.property.1⟩).toAdd,
    (coordinates_fixed_iff d A _).mpr x.property.2⟩
  invFun v := ⟨d.coordinates.symm (Multiplicative.ofAdd v.val),
    (d.coordinates.symm (Multiplicative.ofAdd v.val)).property,
    (coordinates_fixed_iff d A _).mp (by rw [d.coordinates.apply_symm_apply]; exact v.property)⟩
  left_inv x := by simp
  right_inv v := by simp

private theorem maximum_image_offender (d : DoubledCoreAction h q P)
    (hc : IsMulCommutative (commutatorCore L)) (A : Subgroup J)
    (hA : A ∈ elementaryAbelianMaxSubgroups R) (hne : A.map d.actor ≠ ⊥) :
    IsOffender τ (A.map d.actor) := by
  let := h.component_normal
  let : IsElementaryAbelian 2 (commutatorCore L) :=
    h.abelianCore_elementary_of_naturalQuotient hc q
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (A.map d.actor) := IsElementaryAbelian.map d.actor
  let : Finite (A.map d.actor) := Finite.of_surjective
    (fun a : A => (⟨d.actor a,mem_map_of_mem _ a.property⟩ : A.map d.actor))
    (by rintro ⟨_,a,ha,rfl⟩; exact ⟨⟨a,ha⟩,rfl⟩)
  refine ⟨⟨hne,inferInstance⟩,?_⟩
  have hb := maxElementary_card_le_fixed_mul_image R (commutatorCore L) A
    ((commutator_le_left _ _).trans h.radical.twoCore_le) hA d.actor (coordinates_kernel d)
  have hV : Nat.card (commutatorCore L) = 64 := by
    rw [Nat.card_congr d.coordinates.toEquiv]
    simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
  rw [hV,Nat.card_congr (fixedCoordinates d A)] at hb
  have hF := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace τ (A.map d.actor))
  rw [Nat.card_zmod] at hF
  have hI : Nat.card (A.map d.actor) = 2 ^ rank (A.map d.actor) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 (A.map d.actor)).exists_card_eq
    rw [rank,hn,Nat.log_pow (by decide : 1 < 2)]
  rw [hF,hI,←pow_add] at hb
  have hb' : 6 ≤ Module.finrank (ZMod 2) (fixedSpace τ (A.map d.actor)) +
      rank (A.map d.actor) := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
  have hd := fixedCodim_add_finrank τ (A.map d.actor)
  have hdim : Module.finrank (ZMod 2) (Vector × Vector) = 6 := by
    simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector,Module.finrank_prod]
  rw [hdim] at hd
  omega

/-- Equality in the native offender bound puts the complete doubled core
inside the actual elementary Thompson subgroup. -/
theorem DoubledCoreAction.core_le_thompson (d : DoubledCoreAction h q P)
    (hc : IsMulCommutative (commutatorCore L)) (hRP : R ≤ (P : Subgroup J)) :
    commutatorCore L ≤ elementaryAbelianMaxJ R := by
  let := h.component_normal
  let : IsElementaryAbelian 2 (commutatorCore L) :=
    h.abelianCore_elementary_of_naturalQuotient hc q
  have hCR : commutatorCore L ≤ R :=
    (commutator_le_left _ _).trans h.radical.twoCore_le
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty R
  by_cases hz : A.map d.actor = ⊥
  · have hAC : A ≤ centralizer (commutatorCore L : Set J) := by
      rw [←coordinates_kernel d]
      exact (Subgroup.map_eq_bot_iff _).mp hz
    exact (maxElementary_contains_elementary_centralizer R A (commutatorCore L)
      hA hCR (le_centralizer_iff.mp hAC)).trans (le_sSup hA)
  have hmarked := d.unique_offender _ (map_mono (hA.1.trans hRP))
    (maximum_image_offender d hc A hA hz)
  have hTh := (d.thompson_baumann_images hc hRP).1
  have hfixed : Nat.card
      (commutatorCore L ⊓ centralizer (A : Set J) : Subgroup J) = 16 := by
    rw [Nat.card_congr (fixedCoordinates d A),hmarked,←hTh,
      ←Nat.card_congr (fixedCoordinates d (elementaryAbelianMaxJ R))]
    exact (d.thompson_baumann_fixed_card hc hRP).1
  have himage : Nat.card (A.map d.actor) = 4 := by
    rw [hmarked,card_map_of_injective δ_injective,
      card_map_of_injective (MulAut.conj d.frame).injective,BinaryLinearThree.card_R]
  have hC : Nat.card (commutatorCore L) = 64 := by
    rw [Nat.card_congr d.coordinates.toEquiv]
    simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
  let : IsElementaryAbelian 2 A := hA.2.1
  have hrep := (maxElementary_card_bound_and_eq R (commutatorCore L) A hCR hA.1 0
    (by simpa using (maxOrder_eq_card_of_mem R A hA).symm)
    d.actor (coordinates_kernel d)).2 (by rw [hC,hfixed,himage]; rfl)
  exact le_sup_left.trans (le_sSup hrep)

end CFSG.Quasithin.ChapterC.BinaryMS
