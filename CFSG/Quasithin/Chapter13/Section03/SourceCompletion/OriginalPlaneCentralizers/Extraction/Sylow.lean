module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Extraction.Setup
public import Theory.Representation.G2BinaryNondegeneratePlane.PointwiseFixed
public import Theory.GroupTheory.ElementaryThompsonFixedIndex
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.GroupTheory.RelativeSylowNormalizer

/-!
# Sylow repositioning in the original plane centralizer

For Q ≤ S ≤ C_M(A) a two-group, the faithful plane action gives [S:Q] ≤ 2.
Every nonidentity plane actor fixes at most sixteen of the sixty-four
module vectors. Elementary replacement then forces every maximal elementary
subgroup of S into Q, so J(S) = J(Q). Characteristic-normalizer control for
Q promotes a chosen Sylow subgroup of C_M(A) to one of C_G(A).

The final application fills the setup, characteristic-two and Sylow fields
of the literal LocalData record from the source context. Extraction of a
normalized escaping component remains a separate step within this owner.
Source: Aschbacher--Smith 13.3.12, printed p.889, and B.4.6(13).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open Stellmacher
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

omit [Finite G] in
private theorem module_card (d : MarkedPlane V) : Nat.card V = 64 := by
  have hc := Nat.card_congr d.coordinates.toEquiv
  change Nat.card V = Nat.card W at hc
  norm_num only [Nat.card_fun, Nat.card_fin, Nat.card_zmod] at hc
  exact hc

theorem Context.plane_fixed_card (s : Context T L V) (d : MarkedPlane V)
    (a : (centralizer (d.A : Set G) ⊓ normalizer (L : Set G) : Subgroup G))
    (ha : a.val ∉ centralizer (V : Set G)) :
    Nat.card (V ⊓ centralizer ({a.val} : Set G) : Subgroup G) ≤ 16 := by
  let g := s.planeCentralizerAction d a
  have hg : g ≠ 1 := by
    intro hg
    have hk : a ∈ (s.planeCentralizerAction d).ker := hg
    rw [s.planeCentralizerAction_ker d] at hk
    exact ha hk
  let f : (V ⊓ centralizer ({a.val} : Set G) : Subgroup G) →
      {v : W // rho g.val v = v} := fun v =>
    ⟨d.coordinates (Additive.ofMul ⟨v.val, v.property.1⟩), by
      rw [s.planeCentralizerAction_apply, ← d.equivariant]
      apply congrArg d.coordinates
      apply Additive.toMul.injective
      apply Subtype.ext
      change a.val * v.val * a.val⁻¹ = v.val
      exact mul_inv_eq_iff_eq_mul.mpr
        (mem_centralizer_singleton_iff.mp v.property.2).symm⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have he := d.coordinates.injective (congrArg Subtype.val hxy)
    exact Subtype.ext (congrArg (fun v : Additive V => v.toMul.val) he)
  exact (Nat.card_le_card_of_injective f hf).trans (pointwise_nontrivial_fixed_card g hg)

theorem Context.plane_twoGroup_index (s : Context T L V) (d : MarkedPlane V)
    (S : Subgroup G) (hS : IsPGroup 2 S)
    (hQS : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ S)
    (hSM : S ≤ centralizer (d.A : Set G) ⊓ normalizer (L : Set G)) :
    S ⊓ centralizer (V : Set G) = (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).relIndex S ≤ 2 := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let M := centralizer (d.A : Set G) ⊓ normalizer (L : Set G)
  let f := s.planeCentralizerAction d
  have he : S ⊓ centralizer (V : Set G) = Q :=
    (Chapter1.isSylowIn_iff.mp (show Chapter1.IsSylowIn 2 Q
      (centralizer (V : Set G)) from s.core_sylow_centralizer)).2.2 _
      (hS.to_le inf_le_left) (le_inf hQS s.chosen.core_centralizes) inf_le_right
  refine ⟨he, ?_⟩
  have hp : IsPGroup 2 ((S.subgroupOf M).map f) := hS.comap_subtype.map _
  obtain ⟨e⟩ := pointwise_plane_equiv_s3
  have hc : Nat.card ((S.subgroupOf M).map f) ≤ 2 := by
    have hh := twoSubgroup_card_le_two_permThree
      (((S.subgroupOf M).map f).map e.toMonoidHom) (hp.map _)
    simpa only [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective] using hh
  have hi : (centralizer (V : Set G)).relIndex S =
      f.ker.relIndex (S.subgroupOf M) := by
    have hh := relIndex_map_map_of_injective f.ker (S.subgroupOf M) M.subtype_injective
    rw [s.planeCentralizerAction_ker d,
      subgroupOf_map_subtype, map_subgroupOf_eq_of_le hSM] at hh
    have hCM : centralizer (V : Set G) ≤ M :=
      le_inf (Subgroup.centralizer_le d.le_module) s.earlier_geometry.1.centralizer_le
    change _ = (s.planeCentralizerAction d).ker.relIndex _
    rw [s.planeCentralizerAction_ker d]
    simpa only [inf_eq_left.mpr hCM] using hh
  change Q.relIndex S ≤ 2
  rw [← he, inf_comm S, inf_relIndex_right, hi, relIndex_ker]
  exact hc

theorem Context.plane_thompson (s : Context T L V) (d : MarkedPlane V)
    (S : Subgroup G) (hS : IsPGroup 2 S)
    (hQS : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ S)
    (hSM : S ≤ centralizer (d.A : Set G) ⊓ normalizer (L : Set G)) :
    elementaryAbelianMaxJ S = elementaryAbelianMaxJ ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  obtain ⟨he, hi⟩ := s.plane_twoGroup_index d S hS hQS hSM
  change S ⊓ centralizer (V : Set G) = Q at he
  have hJ : elementaryAbelianMaxJ S ≤ Q := by
    apply sSup_le
    intro B hB
    by_contra hnot
    obtain ⟨a, haB, haQ⟩ := SetLike.not_le_iff_exists.mp hnot
    have haS := hB.1 haB
    have haC : a ∉ centralizer (V : Set G) := fun ha => haQ (he ▸ ⟨haS,ha⟩)
    have hc := s.plane_fixed_card d ⟨a,hSM haS⟩ haC
    have hbound := (maxElementary_fixedIndex_le_relIndex S Q B V hQS
      s.chosen.le_core (le_centralizer_iff.mp s.chosen.core_centralizes) hB).1.trans
      ((maxElementary_fixedIndex_le_relIndex S Q B V hQS
        s.chosen.le_core (le_centralizer_iff.mp s.chosen.core_centralizes) hB).2.trans
        ((relIndex_le_of_le_right hB.1 index_ne_zero_of_finite).trans hi))
    have hfix : (centralizer ({a} : Set G)).relIndex V ≤
        (centralizer (B : Set G)).relIndex V :=
      relIndex_le_of_le_left (Subgroup.centralizer_le (by simpa using haB))
        index_ne_zero_of_finite
    have hcount : Nat.card (V ⊓ centralizer ({a} : Set G) : Subgroup G) *
        (centralizer ({a} : Set G)).relIndex V = 64 := by
      have hh := relIndex_mul_relIndex (⊥ : Subgroup G)
        (centralizer ({a} : Set G) ⊓ V) V bot_le inf_le_right
      simpa only [relIndex_bot_left, inf_relIndex_right, inf_relIndex_left, module_card d,
        inf_comm (centralizer ({a} : Set G)) V] using hh
    nlinarith
  exact (elementaryAbelianMaxJ_eq_of_intermediate S Q hJ hQS).symm

theorem Context.plane_sylow_in_normalizer (s : Context T L V) (d : MarkedPlane V) :
    ∃ S : Sylow 2 (centralizer (d.A : Set G)),
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤
        (S : Subgroup (centralizer (d.A : Set G))).map (centralizer (d.A : Set G)).subtype ∧
      (S : Subgroup (centralizer (d.A : Set G))).map (centralizer (d.A : Set G)).subtype ≤
        normalizer (L : Set G) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let H := centralizer (d.A : Set G)
  let M := H ⊓ normalizer (L : Set G)
  have hQM : Q ≤ M := le_inf (s.plane_local_control d).1
    ((pCoreIn_le 2 _).trans (sup_le L.le_normalizer s.chosen.sylow_normalizes_component))
  obtain ⟨P, hQP⟩ := ((isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).comap_subtype
    (K := M)).exists_le_sylow
  let S := (P : Subgroup M).map M.subtype
  have hQS : Q ≤ S := by
    rw [← map_subgroupOf_eq_of_le hQM]
    exact map_mono hQP
  have hSM : S ≤ M := map_subtype_le _
  have hp : IsPGroup 2 S := P.isPGroup'.map _
  have hJ := s.plane_thompson d S hp hQS hSM
  have hQne : Q ≠ ⊥ := fun hb => s.chosen.ne_bot
    (le_bot_iff.mp (hb ▸ s.chosen.le_core))
  have hJn : elementaryAbelianMaxJ Q ≠ ⊥ :=
    elementaryAbelianMaxJ_ne_bot_of_finite_pGroup Q (isPGroup_pCoreIn 2 _) hQne
  have hcontrol : Q.characteristicNormalizerClosure ≤ normalizer (L : Set G) := by
    have hh := s.earlier_geometry.1.characteristic_normalizers_le
    change ((T : Subgroup G) ⊓ centralizer (V : Set G)).characteristicNormalizerClosure ≤ _ at hh
    rwa [s.earlier_geometry.2.1] at hh
  have hn : H ⊓ normalizer (S : Set G) ≤ M := by
    apply le_inf inf_le_left
    have hSN := normalizer_le_normalizer_elementaryAbelianMaxJ S
    rw [hJ] at hSN
    exact inf_le_right.trans (hSN.trans
      ((normalizer_maxJ_le_characteristicNormalizerClosure Q Q
        (sSup_le fun _ hA => hA.1) le_rfl hJn).trans hcontrol))
  obtain ⟨R, hR⟩ := exists_sylow_eq_of_relative_normalizer_le
    (show ∃ P : Sylow 2 M, (P : Subgroup M).map M.subtype = S from ⟨P,rfl⟩)
    (show M ≤ H from inf_le_left) hn
  exact ⟨R,hR.symm ▸ hQS,hR.symm ▸ hSM.trans inf_le_right⟩

/-- The actual component supplies the remaining fields; the C.2.3 setup,
characteristic two and compatible Sylow are all constructed from the source
context. Component existence and its normalization remain with this owner. -/
theorem Context.localData_of_normalized_component (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G)
    (hJ : J ∈ Chapter1.cComponentsIn (centralizer (d.A : Set G)))
    (hq : IsQuasisimple (J ⧸ pCore 2 J))
    (hf : generalizedFitting J = pCore 2 J)
    (hout : ¬ J ≤ centralizer (d.A : Set G) ⊓ normalizer (L : Set G))
    (hn : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ normalizer (J : Set G)) :
    Nonempty (LocalData T L d J) := by
  obtain ⟨S, _, hSM⟩ := s.plane_sylow_in_normalizer d
  exact s.localData_of_input d J
    ⟨s.source_pushingUpSetup d,hJ,hq,hf,hout,hn⟩ S hSM

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
