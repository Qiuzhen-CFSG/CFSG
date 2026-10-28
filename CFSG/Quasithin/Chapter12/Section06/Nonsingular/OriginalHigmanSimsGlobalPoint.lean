module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsGlobalSource
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsPointCore
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsSingularComponentsLocal
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.OddCore

/-!
# The actual nonabelian singular point in the original HS branch

The original returned pair supplies its literal singular centralizer and
the Sylow marking used by the full centralizer map. The native point-core
obstruction forces V to escape this centralizer's two-core. The already
proved original intersection bound then supplies F.9 and its nonabelian
conclusions, through the actual quotient by that whole two-core.

Neither nonsingular-centralizer control nor nonabelianness is assumed.
The resulting singular geometry is an input to the remaining global
comparison with the original maximal faithful A8 component.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original contrary HS branch supplies a singular point with actual
nonabelian span and the exact involution-centralizer preimage in its star
quotient. The ambient group, Sylow, full module and marking are unchanged. -/
theorem SourceHypothesis.exists_original_hs_nonabelian_singular_point
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ hZ : ZV L V = ⊥, ∃ z : V, z ≠ 1 ∧ ¬ D.Nonsingular z ∧
      (T : Subgroup G) ≤ Gv (z : G) ∧ ¬ Gv (z : G) ≤ M L ∧
      (D.fullSetup hZ T z).Gz ∈ (D.fullSetup hZ T z).Hz ∧
      ((D.fullSetup hZ T z).f9 (Gv (z : G))).Hypothesis ∧
      ¬ V ≤ (Gv (z : G)).pCoreIn 2 ∧
      ¬ IsMulCommutative ((D.fullSetup hZ T z).VH (Gv (z : G))) ∧
      Nat.card (Nonabelian.Setup.star (Gv (z : G)) V) = 2 ∧
      primeRank 3 (centralizer (Nonabelian.Setup.star (Gv (z : G)) V :
        Set ((Gv (z : G)) ⧸ pCore 2 (Gv (z : G))))) = 2 ∧
      V ⊓ (Gv (z : G)).pCoreIn 2 = (D.fullSetup hZ T z).V₅ ∧
      (centralizer (Nonabelian.Setup.star (Gv (z : G)) V :
        Set ((Gv (z : G)) ⧸ pCore 2 (Gv (z : G))))).comap
          (QuotientGroup.mk' (pCore 2 (Gv (z : G)))) =
        (normalizer (V : Set G)).subgroupOf (Gv (z : G)) := by
  classical
  obtain ⟨hZ,u,w,hu,_,_,P,t,_,_,_,hz,hsz,hTz,_,hout,hHz,hK,hnot,⟨e⟩,S,hzS,_⟩ :=
    H.exists_original_hs_singular_local_component D hTV hTI v hv he
  let z : V := u*w
  have hzc : (z : G) ∉ centralizer (Kv (u : G) : Set G) := by
    intro hc
    have hmem : (z : G) ∈ zpowers (u : G) :=
      (H.nonsingular_hs_original_geometry D u hu hK hTV hnot e).2.1 ▸ ⟨z.property,hc⟩
    have huo : orderOf (u : G) = 2 := by
      apply orderOf_eq_prime
      · exact elemPow_eq_one_of_isElementaryAbelian (u : G) u.property
      · intro hh
        exact nonsingular_ne_one D hu (Subtype.ext hh)
    rw [mem_zpowers_iff_mem_range_orderOf,huo] at hmem
    obtain ⟨i,hi,hei⟩ := Finset.mem_image.mp hmem
    have hi2 : i < 2 := Finset.mem_range.mp hi
    interval_cases i
    · apply hz
      apply Subtype.ext
      change (z : G) = 1
      simpa only [pow_zero] using hei.symm
    · have hzsing : ¬ D.Nonsingular z := hsz
      apply hzsing
      have hzu : z = u := Subtype.ext (by simpa using hei.symm)
      rw [hzu]
      exact hu
  have hncore := H.nonsingular_hs_selected_module_not_le_core D u hu hK e S z hzS hzc
  have hbound := H.original_hs_conjugate_intersection_bound D hTV hTI v hv he
  have hnz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G) := by
    change (T : Subgroup G) ≤ normalizer (zpowers (z : G) : Set G)
    apply hTz.trans
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    rw [zpowers_eq_closure,centralizer_closure]
    rfl
  have hHz' : Gv (z : G) ∈ (D.fullSetup hZ T z).Hz := by
    rwa [(D.fullSetup hZ T z).Gz_eq] at hHz
  have hf := H.original_f9_of_earlier_geometry D hZ z hz hTV hnz hbound hHz'
  have ha := H.original_abelian_criteria D hZ z hz hTV hnz hbound hHz'
  have hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH (Gv (z : G))) :=
    fun hc => hncore (ha.1.mp (ha.2.2.mpr hc))
  obtain ⟨_,hcard,hcap,_,hcentralizer⟩ :=
    H.original_nonabelian_geometry D hZ z hz hTV hnz hbound hHz' hn
  have hrank := H.original_star_point_centralizer_three_rank D hZ z hz hTV hnz hbound
    hHz' hncore
  exact ⟨hZ,z,hz,hsz,hTz,hout,hHz,hf,hncore,hn,hcard,hrank,hcap,hcentralizer⟩

end CFSG.Quasithin.Chapter12.Section06
