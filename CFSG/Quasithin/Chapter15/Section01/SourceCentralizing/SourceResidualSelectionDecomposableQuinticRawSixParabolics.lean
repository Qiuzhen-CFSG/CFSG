module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixPoint
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawParabolicPlacement
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawClassicalCore
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SixParabolics
-- Only intrinsic interval calculations are reused from the record-based catalogue.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SixParabolics

/-! The actual ordinary A6 block has two S-normalized native parabolics.
The marked intersection is a maximal member of the same Sylow interval;
fixing it fixes both members. Their full source placement then gives the
actual intersection join without any whole-M generation premise. -/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source CaseIComponentData
open Theory.SpecificGroups.SymmetricSix
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

private theorem raw_six_interval {G1 S0 K : Subgroup G}
    (hK : K ∈ Chapter1.LIn G1 S0)
    (hf : generalizedFitting K = pCore 2 K)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    Nonempty (SixParabolicInterval K (S0 ⊓ K)) := by
  obtain ⟨S,hS⟩ := ComponentModels.source20_sylow_intersection hK.2
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,
      QuotientGroup.ker_mk']
  obtain ⟨P,Q,hP,hQ,hPQ,hI,hSP,hSQ,_,_,hall⟩ :=
    alternating_two_kernel_parabolics S q hq (hk ▸ pCore_isPGroup)
  have hgen : P ⊔ Q = ⊤ := by
    apply hP.2
    apply lt_of_le_of_ne le_sup_left
    intro he
    have hQP : Q ≤ P := le_sup_right.trans_eq he.symm
    have hEq : Q = P := by
      by_contra hn
      exact hP.ne_top (hQ.2 P (lt_of_le_of_ne hQP hn))
    exact hPQ hEq.symm
  have hfit (D : Subgroup K) (hSD : (S : Subgroup K) ≤ D) :
      generalizedFitting D = pCore 2 D :=
    generalizedFitting_eq_pCore_of_normalized_by_pCore D hf
      ((pCore_isPGroup.le_sylow_of_normal S).trans (hSD.trans D.le_normalizer))
  obtain ⟨hPi,⟨ep⟩⟩ := CaseIComponentData.maximal_six_quotient e S P hSP.le hP
  obtain ⟨hQi,⟨eq⟩⟩ := CaseIComponentData.maximal_six_quotient e S Q hSQ.le hQ
  let B := P.map K.subtype
  let C := Q.map K.subtype
  let b : P ≃* B := P.equivMapOfInjective K.subtype K.subtype_injective
  let c : Q ≃* C := Q.equivMapOfInjective K.subtype K.subtype_injective
  have hBK : B.subgroupOf K = P := comap_map_eq_self_of_injective K.subtype_injective _
  have hCK : C.subgroupOf K = Q := comap_map_eq_self_of_injective K.subtype_injective _
  refine ⟨⟨⟨S,hS⟩,B,C,map_subtype_le _,map_subtype_le _,?_,?_,hBK ▸ hP,hCK ▸ hQ,
    ?_,?_,?_,?_,hBK ▸ hPi,hCK ▸ hQi,?_,?_,?_⟩⟩
  · rw [←hS]
    exact (map_lt_map_iff_of_injective K.subtype_injective).mpr hSP
  · rw [←hS]
    exact (map_lt_map_iff_of_injective K.subtype_injective).mpr hSQ
  · rw [←map_inf _ _ _ K.subtype_injective,hI,hS]
  · rw [←Subgroup.map_sup,hgen,←MonoidHom.range_eq_map,range_subtype]
  · rw [←map_generalizedFitting_equiv b,←pCore_map_iso 2 b,hfit P hSP.le]
  · rw [←map_generalizedFitting_equiv c,←pCore_map_iso 2 c,hfit Q hSQ.le]
  · exact ⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans ep⟩
  · exact ⟨(QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).symm.trans eq⟩
  · intro D hSD hDK
    have hs : (S : Subgroup K) ≤ D.subgroupOf K := by
      intro x hx
      exact hSD (hS ▸ mem_map_of_mem K.subtype hx)
    rcases hall (D.subgroupOf K) hs with he | he | he | he
    · exact Or.inl (by rw [←map_subgroupOf_eq_of_le hDK,he,hS])
    · exact Or.inr (Or.inl (by rw [←map_subgroupOf_eq_of_le hDK,he]))
    · exact Or.inr (Or.inr (Or.inl (by rw [←map_subgroupOf_eq_of_le hDK,he])))
    · exact Or.inr (Or.inr (Or.inr (le_antisymm hDK (subgroupOf_eq_top.mp he))))

/-- In the actual ordinary A6 block the two original intersections generate
that same block. The complete parabolic closure quotients are derived. -/
theorem PreparedChosenModule.raw_six_original_intersections_generate
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (houtM : ¬L ≤ M)
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L)
    (hb : IsAlternatingBlock L 6) :
    (M ⊓ L) ⊔ ((centralizer (Z1 : Set G) ⊓ Mc) ⊓ L) = L := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let N := centralizer (Z1 : Set G) ⊓ Mc
  obtain ⟨ρ,⟨m⟩,_⟩ := hb.2.2
  let e := m.quotientIso
  have hn : S ≤ normalizer (L : Set G) := by
    apply h.raw_local_normalizes_of_oddRank hG T hZ hZne hL hi.quasisimple Nat.prime_three (by decide)
    rw [primeRank_equiv 3 e,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 Nat.prime_three (by decide)]
  obtain ⟨i⟩ := raw_six_interval hL hb.2.1.fitting e
  have hmax := h.raw_six_marked_coatom hG T hM hJ hu hZ hL houtM hi hb
  have hMc : centralizer (centralInvolutions T : Set G) ≤ Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hu ▸ Set.mem_singleton Mc).2
  have hSN : S ≤ N := by
    intro x hx
    exact ⟨hx.2,hMc (fun z hz => (centralInvolutions_le_centralizer_sylow T hz x hx.1).symm)⟩
  have hproper : ¬ L ≤ N := hi.outside
  have hne : N ⊓ L ≠ S ⊓ L := by
    intro he
    have hlt : (N ⊓ L).subgroupOf L < i.left.subgroupOf L := by
      apply (map_lt_map_iff_of_injective L.subtype_injective).mp
      rw [map_subgroupOf_eq_of_le (show N ⊓ L ≤ L from inf_le_right),
        map_subgroupOf_eq_of_le i.left_le,he]
      exact i.sylow_left
    exact i.left_maximal.ne_top (hmax.2 _ hlt)
  have hpos : N ⊓ L = i.left ∨ N ⊓ L = i.right := by
    rcases i.exhaustive (N ⊓ L) (inf_le_inf_right _ hSN) inf_le_right with he | he | he | he
    · exact (hne he).elim
    · exact Or.inl he
    · exact Or.inr he
    · exact (hproper (he ▸ inf_le_left)).elim
  have hNS : S ≤ normalizer (S ⊓ L : Set G) :=
    (le_inf S.le_normalizer hn).trans inf_normalizer_le_normalizer_inf
  have hNN : S ≤ normalizer (N ⊓ L : Set G) :=
    (le_inf (hSN.trans N.le_normalizer) hn).trans inf_normalizer_le_normalizer_inf
  have hpq : i.left ≠ i.right := by
    intro he
    have hh := i.intersection
    rw [he,inf_idem] at hh
    exact i.sylow_right.ne hh.symm
  have hnorm : S ≤ normalizer (i.left : Set G) ∧ S ≤ normalizer (i.right : Set G) := by
    rcases hpos with he | he
    · have hnL : S ≤ normalizer (i.left : Set G) := he ▸ hNN
      exact ⟨hnL,CaseIComponentData.six_interval_other_fixed i
        (Or.inl rfl) (Or.inr rfl) hpq hn hNS hnL⟩
    · have hnR : S ≤ normalizer (i.right : Set G) := he ▸ hNN
      exact ⟨CaseIComponentData.six_interval_other_fixed i
        (Or.inr rfl) (Or.inl rfl) hpq.symm hn hNS hnR,hnR⟩
  have hnot := i.not_aThree_products hb.2.1.fitting e
  have htwo : IsPGroup 2 S := T.isPGroup'.to_le inf_le_left
  obtain ⟨ep⟩ := i.left_quotient
  obtain ⟨eq⟩ := i.right_quotient
  have hleft := h.raw_parabolic_placement_of_sylow_normalizes hG T hM hJ hu hZ hZne
    hSyl hL.1 i.left_le hnorm.1 i.left_fitting
    (Or.inl (NormalSymmetricThreeExtension.normalized_join _ _ hnorm.1 ep htwo)) hnot.1
  have hright := h.raw_parabolic_placement_of_sylow_normalizes hG T hM hJ hu hZ hZne
    hSyl hL.1 i.right_le hnorm.2 i.right_fitting
    (Or.inl (NormalSymmetricThreeExtension.normalized_join _ _ hnorm.2 eq htwo)) hnot.2
  apply le_antisymm (sup_le inf_le_right inf_le_right)
  calc
    L = i.left ⊔ i.right := i.generated.symm
    _ ≤ (M ⊓ L) ⊔ (N ⊓ L) := sup_le
      (hleft.elim (fun hh => hh.trans le_sup_left) (fun hh => hh.trans le_sup_right))
      (hright.elim (fun hh => hh.trans le_sup_left) (fun hh => hh.trans le_sup_right))

end CFSG.Quasithin.Chapter15.Section01
