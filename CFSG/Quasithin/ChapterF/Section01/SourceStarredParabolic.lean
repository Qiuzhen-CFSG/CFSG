module
public import CFSG.Quasithin.ChapterF.Section01.SourceIncidence
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreRestriction

/-!
# The starred local parabolics in F.1.9

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed
pp.261–262, proof of Lemma F.1.9. Starting with the genuine six conditions
of F.1.1, set Pᵢ* = O₂(Pᵢ)Lᵢ and Sᵢ* = O₂(Pᵢ)(S ∩ Lᵢ).

The common Borel has odd index in Pᵢ, so S is Sylow in Pᵢ and contains
its core. Relative normality and the core intersection formula identify
O₂(Pᵢ*) with O₂(Pᵢ). The product index formula makes Sᵢ* Sylow, and
Sᵢ* ∩ Lᵢ = S ∩ Lᵢ identifies its normalizer inside Pᵢ* with Pᵢ* ∩ B.
The quotient equivalence is induced by the original inclusion Lᵢ → Pᵢ*;
its representative formula records the original local quotient marking.

The final construction supplies every field of `LocalRankOneData` without
additional premises. Faithfulness of the generated triple and rank-two
recognition are separate from these local conclusions.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The starred parabolic O₂(Pᵢ)Lᵢ used in F.1.9. -/
def starredParabolic (L : Fin 2 → Subgroup G) (S : Subgroup G) (i : Fin 2) : Subgroup G :=
  twoCore (parabolic L S i) ⊔ L i

/-- The source Sylow subgroup O₂(Pᵢ)(S ∩ Lᵢ) of the starred parabolic. -/
def starredSylow (L : Fin 2 → Subgroup G) (S : Subgroup G) (i : Fin 2) : Subgroup G :=
  twoCore (parabolic L S i) ⊔ (S ⊓ L i)

theorem local_le_starredParabolic (i : Fin 2) : L i ≤ starredParabolic L S i := le_sup_right

private theorem local_le_parabolic (i : Fin 2) : L i ≤ parabolic L S i :=
  le_sup_left.trans le_sup_left

private theorem parabolic_normalizes_local (h : HypothesisF11 L S) (i : Fin 2) :
    parabolic L S i ≤ normalizer (L i : Set G) :=
  sup_le (sup_le (L i).le_normalizer (h.S_normalizes i)) (h.cross i)

private theorem parabolic_normalizes_core (i : Fin 2) :
    parabolic L S i ≤ normalizer (twoCore (parabolic L S i) : Set G) :=
  (parabolic L S i).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

theorem HypothesisF11.parabolic_odd_index (h : HypothesisF11 L S) (i : Fin 2) :
    ¬ 2 ∣ S.relIndex (parabolic L S i) := by
  let := h.finite_commonBorel
  let := h.finite_local i
  obtain ⟨T, hT⟩ := h.sylow i
  have hST : S.subgroupOf (L i) = (T : Subgroup (L i)) := by
    apply map_injective (L i).subtype_injective
    rw [subgroupOf_map_subtype, hT]
  have hind : ¬ 2 ∣ S.relIndex (L i) := by
    change ¬ 2 ∣ (S.subgroupOf (L i)).index
    rw [hST]
    exact T.not_dvd_index
  have hBP : ¬ 2 ∣ (commonBorel L S).relIndex (parabolic L S i) := by
    rw [parabolic_eq_sup_commonBorel, relIndex_sup_of_normalizes _ _
      (h.commonBorel_normalizes_local i)]
    exact fun hd => hind (hd.trans (relIndex_dvd_of_le_left _ le_sup_right))
  rw [← relIndex_mul_relIndex S (commonBorel L S) (parabolic L S i)
    le_sup_right (commonBorel_le_parabolic i)]
  exact fun hd => (Nat.prime_two.dvd_mul.mp hd).elim h.commonBorel_odd_index hBP

theorem HypothesisF11.sylow_parabolic (h : HypothesisF11 L S) (i : Fin 2) :
    ∃ T : Sylow 2 (parabolic L S i),
      (T : Subgroup (parabolic L S i)).map (parabolic L S i).subtype = S := by
  have hp : IsPGroup 2 (S.subgroupOf (parabolic L S i)) := h.S_isP.comap_subtype
  refine ⟨hp.toSylow (h.parabolic_odd_index i), ?_⟩
  exact map_subgroupOf_eq_of_le (le_sup_right.trans le_sup_left)

theorem HypothesisF11.parabolic_core_le_S (h : HypothesisF11 L S) (i : Fin 2) :
    twoCore (parabolic L S i) ≤ S := by
  obtain ⟨T, hT⟩ := h.sylow_parabolic i
  exact (pCoreIn_le_sylow _ T).trans_eq hT

theorem starredParabolic_le (i : Fin 2) : starredParabolic L S i ≤ parabolic L S i :=
  sup_le (map_subtype_le _) (local_le_parabolic i)

theorem HypothesisF11.starredParabolic_normal (h : HypothesisF11 L S) (i : Fin 2) :
    ((starredParabolic L S i).subgroupOf (parabolic L S i)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  exact (le_inf (parabolic_normalizes_core i) (parabolic_normalizes_local h i)).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

theorem HypothesisF11.starredParabolic_same_core (h : HypothesisF11 L S) (i : Fin 2) :
    twoCore (starredParabolic L S i) = twoCore (parabolic L S i) := by
  apply le_antisymm
  · exact pCoreIn_mono_of_normalizes (starredParabolic_le i)
      ((normal_subgroupOf_iff_le_normalizer (starredParabolic_le i)).mp
        (h.starredParabolic_normal i))
  · exact le_pCoreIn_of_normalizes (pCore_isPGroup.map _) le_sup_left
      ((starredParabolic_le i).trans (parabolic_normalizes_core i))

theorem HypothesisF11.starredParabolic_supplement (h : HypothesisF11 L S) (i : Fin 2) :
    starredParabolic L S i ⊔ commonBorel L S = parabolic L S i := by
  have hQB : twoCore (parabolic L S i) ≤ commonBorel L S :=
    (h.parabolic_core_le_S i).trans le_sup_right
  have hQ : twoCore (parabolic L S i) ≤ L i ⊔ commonBorel L S := hQB.trans le_sup_right
  rw [starredParabolic, sup_assoc, sup_eq_right.mpr hQ]
  exact (parabolic_eq_sup_commonBorel L S i).symm

theorem HypothesisF11.local_inf_parabolic_core (h : HypothesisF11 L S) (i : Fin 2) :
    L i ⊓ twoCore (parabolic L S i) = twoCore (L i) := by
  apply le_antisymm (inf_pCoreIn_le_of_le 2 (local_le_parabolic i))
  exact le_inf (map_subtype_le _) (pCoreIn_mono_of_normalizes
    (local_le_parabolic i) (parabolic_normalizes_local h i))

theorem HypothesisF11.starredSylow_le_S (h : HypothesisF11 L S) (i : Fin 2) :
    starredSylow L S i ≤ S := sup_le (h.parabolic_core_le_S i) inf_le_left

theorem starredSylow_le (i : Fin 2) : starredSylow L S i ≤ starredParabolic L S i :=
  sup_le_sup_left inf_le_right _

theorem HypothesisF11.starredSylow_inf_local (h : HypothesisF11 L S) (i : Fin 2) :
    starredSylow L S i ⊓ L i = S ⊓ L i := by
  exact le_antisymm (inf_le_inf_right _ (h.starredSylow_le_S i))
    (le_inf le_sup_right inf_le_right)

theorem HypothesisF11.starredSylow_isSylow (h : HypothesisF11 L S) (i : Fin 2) :
    ∃ T : Sylow 2 (starredParabolic L S i),
      (T : Subgroup (starredParabolic L S i)).map (starredParabolic L S i).subtype =
        starredSylow L S i := by
  let := h.finite_parabolic i
  let : Finite (starredSylow L S i) := Finite.of_injective
    (inclusion ((starredSylow_le i).trans (starredParabolic_le i))) (inclusion_injective _)
  let := h.finite_local i
  obtain ⟨T, hT⟩ := h.sylow i
  have hST : (S ⊓ L i).subgroupOf (L i) = (T : Subgroup (L i)) := by
    apply map_injective (L i).subtype_injective
    rw [map_subgroupOf_eq_of_le inf_le_right, hT]
  have hind : ¬ 2 ∣ (S ⊓ L i).relIndex (L i) := by
    change ¬ 2 ∣ ((S ⊓ L i).subgroupOf (L i)).index
    rw [hST]
    exact T.not_dvd_index
  have hgen : L i ⊔ starredSylow L S i = starredParabolic L S i := by
    apply le_antisymm (sup_le le_sup_right (starredSylow_le i))
    exact sup_le (le_sup_left.trans le_sup_right) le_sup_left
  have hind' : ¬ 2 ∣ (starredSylow L S i).relIndex (starredParabolic L S i) := by
    rw [← hgen, relIndex_sup_of_normalizes _ _
      ((h.starredSylow_le_S i).trans (h.S_normalizes i))]
    exact fun hd => hind (hd.trans (relIndex_dvd_of_le_left _ le_sup_right))
  have hp : IsPGroup 2 ((starredSylow L S i).subgroupOf (starredParabolic L S i)) :=
    (h.S_isP.to_le (h.starredSylow_le_S i)).comap_subtype
  refine ⟨hp.toSylow hind', ?_⟩
  exact map_subgroupOf_eq_of_le (starredSylow_le i)

/-- The other normalizer in the displayed F.1.9 calculation. -/
theorem HypothesisF11.starredParabolic_localSylow_normalizer
    (h : HypothesisF11 L S) (i : Fin 2) :
    starredParabolic L S i ⊓ commonBorel L S =
      starredParabolic L S i ⊓ normalizer ((S ⊓ L i : Subgroup G) : Set G) := by
  rw [h.commonBorel_eq_normalizer i, ← inf_assoc,
    inf_eq_left.mpr (starredParabolic_le i)]

/-- F.1.9: the starred Borel is the normalizer of the actual starred Sylow subgroup. -/
theorem HypothesisF11.starredParabolic_normalizer_intersection
    (h : HypothesisF11 L S) (i : Fin 2) :
    starredParabolic L S i ⊓ commonBorel L S =
      starredParabolic L S i ⊓ normalizer (starredSylow L S i : Set G) := by
  apply le_antisymm
  · apply inf_le_inf_left
    exact (le_inf ((commonBorel_le_parabolic i).trans (parabolic_normalizes_core i))
      (h.commonBorel_normalizes_localSylow i)).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · have hn : starredParabolic L S i ⊓ normalizer (starredSylow L S i : Set G) ≤
        normalizer ((S ⊓ L i : Subgroup G) : Set G) := by
      rw [← h.starredSylow_inf_local i]
      apply le_normalizer_iff.mpr
      intro x hx y hy
      exact ⟨le_normalizer_iff.mp inf_le_right x hx y hy.1,
        le_normalizer_iff.mp ((starredParabolic_le i).trans
          (parabolic_normalizes_local h i)) x hx.1 y hy.2⟩
    apply le_inf inf_le_left
    rw [h.commonBorel_eq_normalizer i]
    exact le_inf (inf_le_left.trans (starredParabolic_le i)) hn

theorem HypothesisF11.local_inf_commonBorel (h : HypothesisF11 L S) (i : Fin 2) :
    L i ⊓ commonBorel L S = borel (L i) S := by
  rw [h.commonBorel_eq_normalizer i, ← inf_assoc,
    inf_eq_left.mpr (local_le_parabolic i)]
  rfl

theorem HypothesisF11.starredParabolic_borel_product (h : HypothesisF11 L S) (i : Fin 2) :
    starredParabolic L S i ⊓ commonBorel L S =
      twoCore (parabolic L S i) ⊔ borel (L i) S := by
  have hQB : twoCore (parabolic L S i) ≤ commonBorel L S :=
    (h.parabolic_core_le_S i).trans le_sup_right
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ (twoCore (parabolic L S i) : Set G) * (L i : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _
        ((local_le_parabolic i).trans (parabolic_normalizes_core i))]
      exact hx.1
    obtain ⟨q, hq, l, hl, rfl⟩ := hxprod
    have hlB : l ∈ commonBorel L S :=
      ((commonBorel L S).mul_mem_cancel_left (hQB hq)).mp hx.2
    have hlb : l ∈ borel (L i) S := by
      rw [← h.local_inf_commonBorel i]
      exact ⟨hl, hlB⟩
    exact mul_mem (mem_sup_left hq) (mem_sup_right hlb)
  · exact sup_le (le_inf le_sup_left hQB)
      (le_inf ((borel_le _ _).trans le_sup_right) (borel_le_commonBorel i))

/-- The natural map from the original local group to the starred core quotient. -/
def starredQuotientMap (L : Fin 2 → Subgroup G) (S : Subgroup G) (i : Fin 2) :
    L i →* (starredParabolic L S i ⧸ pCore 2 (starredParabolic L S i)) :=
  (QuotientGroup.mk' _).comp (inclusion (local_le_starredParabolic i))

theorem HypothesisF11.starredQuotientMap_ker (h : HypothesisF11 L S) (i : Fin 2) :
    (starredQuotientMap L S i).ker = pCore 2 (L i) := by
  have hc : (twoCore (starredParabolic L S i)).subgroupOf (L i) = pCore 2 (L i) := by
    apply map_injective (L i).subtype_injective
    rw [subgroupOf_map_subtype, inf_comm, h.starredParabolic_same_core i,
      h.local_inf_parabolic_core i]
    rfl
  rw [← hc]
  ext x
  change QuotientGroup.mk (inclusion (local_le_starredParabolic i) x) =
    (1 : starredParabolic L S i ⧸ pCore 2 (starredParabolic L S i)) ↔
      (x : G) ∈ twoCore (starredParabolic L S i)
  rw [QuotientGroup.eq_one_iff]
  exact (mem_map_iff_mem (f := (starredParabolic L S i).subtype)
    (starredParabolic L S i).subtype_injective).symm

theorem HypothesisF11.starredQuotientMap_surjective (h : HypothesisF11 L S) (i : Fin 2) :
    Function.Surjective (starredQuotientMap L S i) := by
  intro z
  induction z using QuotientGroup.induction_on with
  | H x =>
    have hxprod : (x : G) ∈ (twoCore (parabolic L S i) : Set G) * (L i : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _
        ((local_le_parabolic i).trans (parabolic_normalizes_core i))]
      exact x.property
    obtain ⟨q, hq, l, hl, he⟩ := hxprod
    let q' : starredParabolic L S i := ⟨q, mem_sup_left hq⟩
    let l' : L i := ⟨l, hl⟩
    have hq' : q' ∈ pCore 2 (starredParabolic L S i) := by
      apply (mem_map_iff_mem (f := (starredParabolic L S i).subtype)
        (starredParabolic L S i).subtype_injective).mp
      change q ∈ twoCore (starredParabolic L S i)
      rwa [h.starredParabolic_same_core i]
    have hx : q' * inclusion (local_le_starredParabolic i) l' = x :=
      Subtype.ext he
    refine ⟨l', ?_⟩
    rw [← hx]
    change _ = (QuotientGroup.mk' _) (_ * _)
    have hqone : (QuotientGroup.mk' (pCore 2 (starredParabolic L S i))) q' = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hq'
    rw [map_mul, hqone, one_mul]
    rfl

/-- F.1.9's quotient equivalence, induced by the literal inclusion of Lᵢ. -/
noncomputable def HypothesisF11.starredQuotientEquiv (h : HypothesisF11 L S) (i : Fin 2) :
    (L i ⧸ pCore 2 (L i)) ≃*
      (starredParabolic L S i ⧸ pCore 2 (starredParabolic L S i)) :=
  (QuotientGroup.quotientMulEquivOfEq (h.starredQuotientMap_ker i).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (h.starredQuotientMap_surjective i))

@[simp] theorem HypothesisF11.starredQuotientEquiv_mk (h : HypothesisF11 L S)
    (i : Fin 2) (x : L i) :
    h.starredQuotientEquiv i (QuotientGroup.mk x) =
      QuotientGroup.mk (inclusion (local_le_starredParabolic i) x) := rfl

/-- Transport to an isomorphic carrier preserves the actual rank-one alternatives. -/
theorem IsRankOneModel.of_equiv {A B : Type*} [Group A] [Group B]
    (h : IsRankOneModel A) (e : B ≃* A) : IsRankOneModel B := by
  cases h with
  | linear n hn h =>
    obtain ⟨F, hF, hfin, hcard, ⟨d⟩⟩ := h
    exact .linear n hn ⟨F, hF, hfin, hcard, ⟨e.trans d⟩⟩
  | suzuki m h => exact .suzuki m ⟨e.trans h.some⟩
  | projective_unitary n hn h =>
    obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨d⟩⟩ := h
    exact .projective_unitary n hn ⟨F, hF, hfin, J, hcard, hconj, ⟨e.trans d⟩⟩
  | special_unitary n hn h =>
    obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨d⟩⟩ := h
    exact .special_unitary n hn ⟨F, hF, hfin, J, hcard, hconj, ⟨e.trans d⟩⟩
  | dihedral h => exact .dihedral ⟨e.trans h.some⟩

/-- The genuine starred local data used by F.1.9, constructed from F.1.1. -/
noncomputable def HypothesisF11.starredLocalRankOneData (h : HypothesisF11 L S) (i : Fin 2) :
    LocalRankOneData (parabolic L S i) (commonBorel L S) where
  finite_P := h.finite_parabolic i
  Pstar := starredParabolic L S i
  Pstar_le := starredParabolic_le i
  normal := h.starredParabolic_normal i
  same_core := h.starredParabolic_same_core i
  supplement := h.starredParabolic_supplement i
  characteristic_two := h.characteristic_two i
  sylow := (h.starredSylow_isSylow i).choose
  borel_eq := by
    rw [(h.starredSylow_isSylow i).choose_spec]
    exact h.starredParabolic_normalizer_intersection i
  quotient := (h.quotient i).of_equiv (h.starredQuotientEquiv i).symm

@[simp] theorem HypothesisF11.starredLocalRankOneData_Pstar
    (h : HypothesisF11 L S) (i : Fin 2) :
    (h.starredLocalRankOneData i).Pstar = starredParabolic L S i := rfl

/-- The Sylow witness in the packaged data has the exact source product as image. -/
theorem HypothesisF11.starredLocalRankOneData_sylow_image
    (h : HypothesisF11 L S) (i : Fin 2) :
    ((h.starredLocalRankOneData i).sylow :
      Subgroup (h.starredLocalRankOneData i).Pstar).map
        (h.starredLocalRankOneData i).Pstar.subtype = starredSylow L S i :=
  (h.starredSylow_isSylow i).choose_spec

/-- F.1.9's local input to the faithful parabolic triple. -/
theorem HypothesisF11.localRankOneData (h : HypothesisF11 L S) (i : Fin 2) :
    Nonempty (LocalRankOneData (parabolic L S i) (commonBorel L S)) :=
  ⟨h.starredLocalRankOneData i⟩

end CFSG.Quasithin.ChapterF.Source
