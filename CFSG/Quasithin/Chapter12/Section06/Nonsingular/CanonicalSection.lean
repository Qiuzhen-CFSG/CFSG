module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ResidualBlock

/-!
# The proper original A6 section in the canonical component

Map the literal L_v into K_v/O2(K_v). Its two-core quotient is still A6.
If the image were the whole quotient, core normalization would make L_v
normal in K_v with a two-group quotient. Two-perfectness would give
L_v=K_v, contrary to the original escape from M. Thus the image is proper,
without assuming that the canonical two-core lies in M or that R=R_v.

The resulting cubic rank, order and quintic divisibility bounds are the
inputs to CanonicalModels; PreferredCanonical constructs the section at
the same source-preferred point. Source: Aschbacher--Smith 12.6.18,
printed p.827, combined manuscript of 1 March 2004.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The literal A6 image is proper without placing the canonical two-core in M. -/
theorem SourceHypothesis.nonsingular_canonical_proper_section
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (he : ¬ Kv (v : G) ≤ M L)
    (S : Sylow 2 (Gv (v : G)))
    (hRN : R L (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) (v : G) ≤
      normalizer (Lv L (v : G) : Set G)) :
    let A := ((Lv L (v : G)).subgroupOf (Kv (v : G))).map (QuotientGroup.mk' (pCore 2 (Kv (v : G))))
    A ≠ ⊤ ∧ Nonempty ((A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6)) := by
  let C := Kv (v : G)
  let A₀ := (Lv L (v : G)).subgroupOf C
  let q := QuotientGroup.mk' (pCore 2 C)
  let A := A₀.map q
  have hAC : Lv L (v : G) ≤ C := (H.nonsingular_canonical_component D v hv).2.1
  let a : A₀ ≃* Lv L (v : G) := subgroupOfEquivOfLe hAC
  obtain ⟨eA⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  have hkA : IsPGroup 2 (q.subgroupMap A₀).ker := by
    rw [Subgroup.ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  refine ⟨?_,⟨((q.subgroupMap A₀).pCoreQuotientEquiv (q.subgroupMap_surjective A₀) hkA).symm.trans
    ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eA)⟩⟩
  intro ht
  change A = ⊤ at ht
  have hgen : A₀ ⊔ pCore 2 C = ⊤ := by
    have hh := congrArg (Subgroup.comap q) ht
    simpa only [A,q,comap_map_eq,QuotientGroup.ker_mk',comap_top] using hh
  let P := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  have hPC : P ≤ normalizer (C : Set G) := (map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv _)).mp (Kv_normalIn_Gv _))
  have hQ : C.pCoreIn 2 ≤ R L C P (v : G) :=
    (pCoreIn_mono_of_normalizes (show C ≤ C ⊔ P from le_sup_left)
      (sup_le C.le_normalizer hPC)).trans (core_le_R_of_sylow L C _ S (Kv_le_Gv _))
  have hn : pCore 2 C ≤ normalizer (A₀ : Set C) := by
    apply le_normalizer_iff.mpr
    intro x hx y hy
    exact le_normalizer_iff.mp hRN x (hQ (mem_map_of_mem C.subtype hx)) y hy
  let : A₀.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [←hgen]
    exact sup_le A₀.le_normalizer hn))
  have hp : IsPGroup 2 (C ⧸ A₀) :=
    isPGroup_quotient_of_sup_eq_top A₀ (pCore 2 C) pCore_isPGroup hgen
  have hr : pResidual 2 C ≤ A₀ := sInf_le ⟨inferInstance,hp⟩
  rw [(pResidual_eq_top_iff 2 C).mpr (Kv_isPPerfect (v : G))] at hr
  apply he
  intro c hc
  exact (Lv_le_L L (v : G)).trans L.le_normalizer
    (hr (show (⟨c,hc⟩ : C) ∈ (⊤ : Subgroup C) from mem_top _))

/-- The unchanged proper A6 section supplies the exact bounds used in the FF model sieve. -/
theorem SourceHypothesis.nonsingular_canonical_component_bounds
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (he : ¬ Kv (v : G) ≤ M L)
    (S : Sylow 2 (Gv (v : G)))
    (hRN : R L (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) (v : G) ≤
      normalizer (Lv L (v : G) : Set G)) :
    2 ≤ primeRank 3 (Star (Kv (v : G))) ∧
      360 < Nat.card (Star (Kv (v : G))) ∧ 5 ∣ Nat.card (Star (Kv (v : G))) := by
  let A := ((Lv L (v : G)).subgroupOf (Kv (v : G))).map (QuotientGroup.mk' (pCore 2 (Kv (v : G))))
  obtain ⟨hA,⟨e⟩⟩ := H.nonsingular_canonical_proper_section D v hv he S hRN
  have hr : 2 ≤ primeRank 3 A := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 A) pCore_isPGroup,
      primeRank_equiv 3 e]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  have hd : 360 ∣ Nat.card A := by
    have hh := card_quotient_dvd_card (pCore 2 A)
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh ⊢
    exact hh
  refine ⟨hr.trans (Theory.GroupTheory.primeRank_le_of_injective 3 A.subtype A.subtype_injective),?_,
    (show 5 ∣ 360 by decide).trans (hd.trans A.card_subgroup_dvd_card)⟩
  exact (Nat.le_of_dvd Nat.card_pos hd).trans_lt
    (lt_of_le_of_ne (card_le_card_group A) (fun hh => hA (A.eq_top_of_card_eq hh)))
end CFSG.Quasithin.Chapter12.Section06
