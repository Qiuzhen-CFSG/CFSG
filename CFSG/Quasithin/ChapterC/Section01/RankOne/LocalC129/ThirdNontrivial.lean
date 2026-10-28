module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.ChiSieve
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.SpecificGroups.Alternating.FourThirdCentralizer
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.CComponent.QuotientLifting
public import GorensteinWalter.Classification

/-!
# The third lower-central term in an ordinary A₇ block extension

Every Sylow two-group of A₇ contains an element with nontrivial square.
Faithfulness of the prescribed binary natural module makes that square
move the actual elementary layer U(K). The generic square-movement
criterion therefore makes the third lower-central term of the ambient
Sylow two-group nontrivial. A7 normality is derived from the source
strong-quasithin rank bound, rather than assumed.

This is the nontrivial-characteristic-subgroup step of C.1.29, p.134.
-/
public section
open Subgroup
open scoped Pointwise
namespace alternatingGroup.SevenComponent

theorem sylow_has_nontrivial_square (S : Sylow 2 (alternatingGroup (Fin 7))) :
    ∃ a ∈ (S : Subgroup (alternatingGroup (Fin 7))), a ^ 2 ≠ 1 := by
  let a : alternatingGroup (Fin 7) := ⟨GorensteinWalter.d8rho, GorensteinWalter.d8rho_mem⟩
  have ha : a ∈ (GorensteinWalter.sylowD8 : Subgroup (alternatingGroup (Fin 7))) :=
    GorensteinWalter.d8rho_mem_sylowD8
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7))
    GorensteinWalter.sylowD8 S
  refine ⟨MulAut.conj g a, ?_, ?_⟩
  · rw [← hg]
    change MulAut.conj g a ∈ MulAut.conj g •
      (GorensteinWalter.sylowD8 : Subgroup (alternatingGroup (Fin 7)))
    exact Subgroup.smul_mem_pointwise_smul a (MulAut.conj g) _ ha
  · intro he
    have hh : a ^ 2 = 1 := (MulAut.conj g).injective (by simpa only [map_pow, map_one] using he)
    have hh' := congrArg (fun z : alternatingGroup (Fin 7) => (z : Equiv.Perm (Fin 7))) hh
    exact (by decide : GorensteinWalter.d8rho ^ 2 ≠ 1) hh'
end alternatingGroup.SevenComponent

namespace CFSG.Quasithin.ChapterC.LocalC129
open Theory.GroupTheory
variable {L G : Type*} [Group L] [Finite L] [Group G] [Finite G]

omit [Finite L] in
theorem square_moves_blockU_of_alternating {n : ℕ} (hn : 5 ≤ n)
    (h : IsAlternatingBlock L n) (a : L)
    (ha : (QuotientGroup.mk' (pCore 2 L) a) ^ 2 ≠ 1) :
    ∃ u ∈ blockU L, a ^ 2 * u * (a ^ 2)⁻¹ ≠ u := by
  obtain ⟨rho, ⟨model⟩, hact⟩ := h.2.2
  by_contra hnone
  push Not at hnone
  have hr : BinaryPermutation.naturalRepresentation (Fin n)
      (model.quotientIso (QuotientGroup.mk' (pCore 2 L) (a ^ 2))).val =
      BinaryPermutation.naturalRepresentation (Fin n) 1 := by
    apply LinearMap.ext
    intro v
    obtain ⟨w, hw⟩ := model.moduleIso.surjective (Multiplicative.ofAdd v)
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (blockFixed L) w
    have he := model.intertwining (a ^ 2) u
    have hc : blockConjugate L (a ^ 2) u = u := Subtype.ext (hnone u u.property)
    rw [hc] at he
    have hv := congrArg Multiplicative.toAdd he
    rw [hact, hw] at hv
    change v = BinaryPermutation.naturalRepresentation (Fin n)
      (model.quotientIso (QuotientGroup.mk' (pCore 2 L) (a ^ 2))).val v at hv
    simpa only [map_one, Module.End.one_apply] using hv.symm
  have hq : model.quotientIso (QuotientGroup.mk' (pCore 2 L) (a ^ 2)) = 1 :=
    Subtype.ext ((BinaryPermutation.naturalRepresentation_injective (Fin n) (by simpa using hn)) hr)
  apply ha
  rw [← map_pow]
  exact model.quotientIso.map_eq_one_iff.mp hq

/-- Every Sylow two-group containing an ordinary A₇ block has nontrivial
third lower-central term. The elementary moving layer is the actual U(K). -/
theorem alternating_seven_sylow_third_ne_bot (hs : IsStronglyQuasithin G) (T : Sylow 2 G)
    {K : Subgroup G} (hK : IsBlock K) (ha : IsAlternatingBlock K 7) :
    (⊤ : Subgroup T).lowerCentralSeries 2 ≠ ⊥ := by
  let : K.Normal := alternating_seven_normal hs hK ha
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_subnormal K hK.subnormal
  obtain ⟨e⟩ := ha.2.2.quotient_iso
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨b, hb, hbsq⟩ := alternatingGroup.SevenComponent.sylow_has_nontrivial_square
    (S.mapSurjective hq)
  obtain ⟨a, haS, hab⟩ := hb
  have hqa : (QuotientGroup.mk' (pCore 2 K) a) ^ 2 ≠ 1 := by
    intro he
    apply hbsq
    rw [← hab]
    change (e (QuotientGroup.mk' (pCore 2 K) a)) ^ 2 = 1
    rw [← map_pow, he, map_one]
  obtain ⟨u, hu, hmove⟩ := square_moves_blockU_of_alternating (by decide) ha a hqa
  let V := (blockU K).map K.subtype
  let : IsElementaryAbelian 2 (blockU K) := ha.2.1.elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map K.subtype
  have hVK : V ≤ K := map_subtype_le _
  have hVT : V ≤ (T : Subgroup G) :=
    ((map_mono blockU_le_core).trans (pCoreIn_le_of_subnormal 2 hK.subnormal)).trans
      (pCore_isPGroup.le_sylow_of_normal T)
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) :=
    (show (T : Subgroup G) ≤ normalizer (K : Set G) from le_normalizer_of_normal).trans
      (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hat : (a : G) ∈ (T : Subgroup G) := by
    rw [hS] at haS
    exact haS
  apply Subgroup.third_ne_bot_of_square_movement (T : Subgroup G) V hVT hTV a u hat
    (mem_map.mpr ⟨u, hu, rfl⟩)
  intro hh
  exact hmove (Subtype.ext hh)

/-- The actual normalized A₄ used by C.1.29 is forced into every
characteristic-normalizer overgroup. Its existence is constructed separately. -/
theorem normalized_four_le_control (hs : IsStronglyQuasithin G)
    (T : Sylow 2 G) {K : Subgroup G} (hK : IsBlock K)
    (ha : IsAlternatingBlock K 7) (Y M : Subgroup G)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (eY : Y ≃* alternatingGroup (Fin 4))
    (hM : (T : Subgroup G).characteristicNormalizerClosure ≤ M) : Y ≤ M :=
  (alternatingGroup.FourThirdCentralizer.le_characteristicNormalizerClosure
    (T : Subgroup G) Y T.isPGroup' hTY eY
    (alternating_seven_sylow_third_ne_bot hs T hK ha)).trans hM
end CFSG.Quasithin.ChapterC.LocalC129
