module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryLocalCore
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryQuotientComponents
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.OddRadical
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import Theory.GroupTheory.CComponent.TwoClosedKernel
public import Theory.GroupTheory.SolvableRadical.TwoCoreOddQuotient

/-!
# The full action kernel and the lifted component's two-core quotient

The original Sylow meets the full action kernel inside the normal local
core Q. Its intersection is therefore normalized by the original local
base. Frattini factorization and minimality of the escaping H make this
Sylow subgroup normal in H, hence normal in the full kernel.

For a normal lifted C-component, this two-closed kernel makes its radical
modulo its intrinsic two-core odd; the common A.3.6 clauses then prove
quasisimplicity. For a nonnormal lift, the source 1.2.1(3) quotient theorem
already gives quasisimplicity. No solvability of the full kernel is assumed.
The actual chosen-orbit application is NonFFSourceDoubledBinaryKernel.
Source: Aschbacher–Smith, proof of Proposition 7.7.3 immediately before
7.7.7, printed p.707, and A.3.6, printed pp.43–45, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryKernel

/-- Minimality and the full-kernel Frattini factorization make its original
Sylow subgroup normal in H. -/
theorem kernel_sylow_normal_of_minimal_escape
    {G : Type*} [Group G] [Finite G] (H B M : Subgroup G)
    (hH : H ∈ Chapter3.HStar B M) (N : Subgroup H) [N.Normal]
    (S : Sylow 2 N) (hNM : N.map H.subtype ≤ M)
    (hB : B ≤ normalizer (((S : Subgroup N).map N.subtype).map H.subtype : Set G))
    (hne : ((S : Subgroup N).map (H.subtype.comp N.subtype)) ≠ ⊥) :
    ((S : Subgroup N).map N.subtype).Normal ∧ (S : Subgroup N).Normal := by
  let P := (S : Subgroup N).map N.subtype
  let A := P.map H.subtype
  let X := H ⊓ normalizer (A : Set G)
  have hAH : A ≤ H := map_subtype_le P
  have hAX : A ≤ X := le_inf hAH A.le_normalizer
  have hp : IsPGroup 2 A := (S.isPGroup'.map N.subtype).map H.subtype
  have hcore : A ≤ X.pCoreIn 2 := le_pCoreIn_of_normalizes hp hAX inf_le_right
  have hXB : B ≤ X := le_inf hH.1.1.2 hB
  have hfr : (normalizer (P : Set H)).map H.subtype ⊔ N.map H.subtype = H := by
    have hh := congrArg (map H.subtype) S.normalizer_sup_eq_top
    simpa only [Subgroup.map_sup, ← MonoidHom.range_eq_map, H.range_subtype] using hh
  have hNX : (normalizer (P : Set H)).map H.subtype ≤ X :=
    le_inf (map_subtype_le _) (P.le_normalizer_map H.subtype)
  have hXM : ¬ X ≤ M := by
    intro hh
    exact hH.1.2 (hfr.symm.le.trans (sup_le (hNX.trans hh) hNM))
  have hHX : H ≤ X := hH.2 ⟨⟨?_,hXB⟩,hXM⟩ inf_le_left
  · have hn : (A.subgroupOf H).Normal :=
      normal_subgroupOf_of_le_normalizer (hHX.trans inf_le_right)
    have he : A.subgroupOf H = P :=
      comap_map_eq_self_of_injective H.subtype_injective P
    have hP : P.Normal := he ▸ hn
    refine ⟨hP,?_⟩
    let := hP
    have hn' : (P.comap N.subtype).Normal := inferInstance
    have he' : P.comap N.subtype = (S : Subgroup N) :=
      comap_map_eq_self_of_injective N.subtype_injective _
    exact he' ▸ hn'
  · intro hz
    apply hne
    rw [← map_map]
    exact le_bot_iff.mp (hz ▸ hcore)

/-- If the original Sylow meets a normal kernel inside the normal local
core, minimal escape makes that kernel two-closed. -/
theorem kernel_twoClosed_of_original_core
    {G : Type*} [Group G] [Finite G] (H B M Q U : Subgroup G)
    (hH : H ∈ Chapter3.HStar B M) (N : Subgroup H) [N.Normal]
    (P : Sylow 2 H) (hNM : N.map H.subtype ≤ M)
    (hQP : Q ≤ (P : Subgroup H).map H.subtype)
    (hBQ : B ≤ normalizer (Q : Set G))
    (hinter : ((P : Subgroup H) ⊓ N).map H.subtype ≤ Q)
    (hU : U ≠ ⊥) (hUP : U ≤ (P : Subgroup H).map H.subtype)
    (hUN : U ≤ N.map H.subtype) :
    ∃ S : Sylow 2 N, (S : Subgroup N).Normal := by
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_normal N
  have hSP : (S : Subgroup N).map N.subtype = (P : Subgroup H) ⊓ N := by
    rw [hS,subgroupOf_map_subtype]
  have hA : ((S : Subgroup N).map N.subtype).map H.subtype =
      Q ⊓ N.map H.subtype := by
    rw [hSP]
    apply le_antisymm (le_inf hinter (map_mono inf_le_right))
    rw [Subgroup.map_inf _ _ H.subtype H.subtype_injective]
    exact inf_le_inf_right _ hQP
  have hHN : H ≤ normalizer (N.map H.subtype : Set G) := by
    apply le_normalizer_iff.mpr
    intro g hg n hn
    obtain ⟨a,ha,rfl⟩ := hn
    exact ⟨⟨g,hg⟩ * a * (⟨g,hg⟩ : H)⁻¹,
      (inferInstance : N.Normal).conj_mem a ha ⟨g,hg⟩,rfl⟩
  have hBN : B ≤ normalizer (N.map H.subtype : Set G) := hH.1.1.2.trans hHN
  have hnorm : B ≤ normalizer
      (((S : Subgroup N).map N.subtype).map H.subtype : Set G) := by
    rw [hA]
    exact (le_inf hBQ hBN).trans inf_normalizer_le_normalizer_inf
  have hne : (S : Subgroup N).map (H.subtype.comp N.subtype) ≠ ⊥ := by
    intro he
    have hUA : U ≤ ((S : Subgroup N).map N.subtype).map H.subtype := by
      rw [hSP,Subgroup.map_inf _ _ H.subtype H.subtype_injective]
      exact le_inf hUP hUN
    rw [map_map,he] at hUA
    exact hU (le_bot_iff.mp hUA)
  exact ⟨S,(kernel_sylow_normal_of_minimal_escape H B M hH N S hNM hnorm hne).2⟩

/-- A component image through a two-closed full kernel has a quasisimple
intrinsic two-core quotient in the source SQTK group. -/
theorem lifted_component_twoCore_quasisimple
    {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (N C : Subgroup H) [N.Normal]
    (hN : ∃ S : Sylow 2 N, (S : Subgroup N).Normal)
    (hquot : pCore 2 (H ⧸ N) = ⊥) (hC : C.IsCComponent)
    (him : IsComponent (H ⧸ N) (C.map (QuotientGroup.mk' N))) :
    IsQuasisimple (C ⧸ pCore 2 C) := by
  classical
  by_cases hn : C.Normal
  · let := hn
    have ho : Odd (Nat.card (solvableRadical (C ⧸ pCore 2 C))) :=
      odd_radical_twoCore_quotient_iff.mpr
        (odd_radical_relIndex_of_component_quotient N C hN hquot him)
    exact Chapter1.Section02.quasisimple_twoCore_quotient_of_a36_of_odd_radical
      (ChapterA.SQTKStructure.a36Input_of_theoremsAC
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)) hH hC ho
  · have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
      refine ⟨?_,hH.isKGroup.quotient _⟩
      intro p hp ho
      let : Fact p.Prime := ⟨hp⟩
      exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
        (hH.stronglyQuasithin p hp ho)
    let := (Chapter1.Section02.nonnormal_twoCore_image_isComponent hQ hC hn).2
    exact IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hC).symm

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryKernel
