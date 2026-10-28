module
public import CFSG.Quasithin.Chapter10.SourceBaumannBlocks
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFivePairCore
public import Theory.GroupTheory.PGroup.OmegaCenterDetection

/-!
# The original core in the zero-centralizer branch of 10.2.1

Assume the Baumann normalizer escapes M and C_Z(L₀)=1 for Z=Ω₁(Z(T)).
The original two Sylow-conjugate components are alternating-five blocks.
The C.1.13(c) splitting expresses O₂(L₀T) as their two elementary block
layers and a common centralizer. That centralizer is T-invariant inside T;
omega-center detection and C_Z(L₀)=1 force it to vanish.

Consequently O₂(L₀T) is elementary and lies in L₀, hence equals O₂(L₀).
This core is characteristic in L₀ and normal in M=N_G(L₀). Both groups
contain the same Sylow subgroup, so O₂(M)=O₂(L₀T) as well. The identification
with the chosen local module and the subsequent dihedral-factor normalizer
argument remain separate source steps.
Source: Aschbacher–Smith, 10.2.1, printed pp.742–743, using C.1.13(c),
printed pp.124–125, and the p-group omega-center intersection principle.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The source zero-centralizer hypothesis removes the common fixed factor
from the literal local two-core. -/
theorem source_orbit_core_centralizer_eq_bot
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    (localJoin T L).pCoreIn 2 ⊓ centralizer (localOrbit T L : Set G) = ⊥ := by
  let H := localJoin T L
  let Q := H.pCoreIn 2
  let C := Q ⊓ centralizer (localOrbit T L : Set G)
  have hQT : Q ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H
      (T.subtype (show (T : Subgroup G) ≤ H from le_sup_right))
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ H from le_sup_right)] at hh
    exact hh
  have hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (show (T : Subgroup G) ≤ H from le_sup_right).trans
      (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf hTQ ((le_normalizer_componentOrbit L T).trans
      (normalizer_le_normalizer_centralizer (localOrbit T L)))).trans
      inf_normalizer_le_normalizer_inf
  apply eq_bot_of_normalized_of_omega_center_disjoint (T : Subgroup G) C
    T.isPGroup' (inf_le_left.trans hQT) hTC
  apply bot_unique
  apply le_trans (le_inf (inf_le_left.trans ?_) (inf_le_right.trans inf_le_right)) hz.le
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro x hx hx2
  obtain ⟨z,hz,rfl⟩ := hx
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨z.property, hx2, fun t ht => congrArg (T : Subgroup G).subtype
      ((mem_center_iff.mp hz) ⟨t,ht⟩)⟩

/-- The literal core is the join of the two original alternating-five block
layers, with an actual exchanging Sylow element and original orbit map. -/
theorem source_a5_zero_centralizer_pair_core
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ∃ t : localJoin T L, (t : G) ∈ (T : Subgroup G) ∧
      let A := L.subgroupOf (localJoin T L)
      let B := A.map (MulAut.conj t).toMonoidHom
      A ≠ B ∧ IsBlock B ∧ IsAlternatingBlock B 5 ∧
        (A ⊔ B).map (localJoin T L).subtype = localOrbit T L ∧
        pCore 2 (localJoin T L) = (blockU A).map A.subtype ⊔ (blockU B).map B.subtype ∧
        IsElementaryAbelian 2 (pCore 2 (localJoin T L)) := by
  let H := localJoin T L
  let A := L.subgroupOf H
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  obtain ⟨ha,haa,_⟩ := source_a5_original_block_of_baumann_not_controlled D e hn hout
  obtain ⟨t,ht,htn,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let tH : H := ⟨t, (show (T : Subgroup G) ≤ H from le_sup_right) ht⟩
  let B := A.map (MulAut.conj tH).toMonoidHom
  have hb : IsBlock B := ha.map_equiv (MulAut.conj tH)
  have hab : IsAlternatingBlock B 5 :=
    RankOne.Solvable.isAlternatingBlock_of_equiv ((MulAut.conj tH).subgroupMap A) haa
  have hmapA : A.map H.subtype = L := map_subgroupOf_eq_of_le hLH
  have hmapB : B.map H.subtype = L.map (MulAut.conj t).toMonoidHom := by
    rw [show B = A.map (MulAut.conj tH).toMonoidHom from rfl, map_map]
    rw [show H.subtype.comp (MulAut.conj tH).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp H.subtype from rfl, ←map_map, hmapA]
  have hne : A ≠ B := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map H.subtype) he).symm.trans hmapA)
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := by
    let := D.quasisimple
    exact IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLH).symm
        (pCore_map_iso 2 (subgroupOfEquivOfLe hLH).symm))
  have hc := ha.commutator_eq_bot_of_quasisimple_quotient hb hqA hne
  have hmapPair : (A ⊔ B).map H.subtype = localOrbit T L := by
    rw [Subgroup.map_sup,hmapA,hmapB,hpair]
  have hc0 : pCore 2 H ⊓ centralizer ((A ⊔ B : Subgroup H) : Set H) = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ H.subtype_injective).mp
    apply bot_unique
    apply le_trans ?_ (source_orbit_core_centralizer_eq_bot hz).le
    apply le_inf (map_mono inf_le_left)
    have hh := (map_mono (f := H.subtype) (show
      pCore 2 H ⊓ centralizer ((A ⊔ B : Subgroup H) : Set H) ≤
        centralizer ((A ⊔ B : Subgroup H) : Set H) from inf_le_right)).trans
      (map_centralizer_le_centralizer_image _ H.subtype)
    change _ ≤ centralizer ((A ⊔ B).map H.subtype : Set G) at hh
    rwa [hmapPair] at hh
  refine ⟨tH,ht,hne,hb,hab,hmapPair,?_,
    alternatingFive_pair_core_elementary A B ha hb haa hab hc hc0⟩
  simpa only [hc0, sup_bot_eq] using alternatingFive_pair_core_split A B ha hb haa hab hc

/-- The original local core is elementary in the zero-centralizer branch. -/
theorem source_a5_zero_centralizer_core_elementary
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    IsElementaryAbelian 2 ((localJoin T L).pCoreIn 2) := by
  obtain ⟨t,ht,hne,hb,hab,hpair,hsplit,hE⟩ :=
    source_a5_zero_centralizer_pair_core D e hn hout hz
  exact hE.map (localJoin T L).subtype

/-- The orbit, local join and maximal local normalizer have the same embedded
two-core in the source zero-centralizer branch. -/
theorem source_a5_zero_centralizer_core_eq
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    (localJoin T L).pCoreIn 2 = (localOrbit T L).pCoreIn 2 ∧
      D.maximalLocal.pCoreIn 2 = (localJoin T L).pCoreIn 2 := by
  let H := localJoin T L
  let Q := H.pCoreIn 2
  obtain ⟨t,ht,hne,hb,hab,hpair,hsplit,hE⟩ :=
    source_a5_zero_centralizer_pair_core D e hn hout hz
  have hQO : Q ≤ localOrbit T L := by
    rw [←hpair]
    apply map_mono
    rw [hsplit]
    exact sup_le_sup (map_subtype_le _) (map_subtype_le _)
  have hHQ : H ≤ normalizer (Q : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hHO : H ≤ normalizer (localOrbit T L : Set G) :=
    sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
  have hQOcore : Q = (localOrbit T L).pCoreIn 2 :=
    le_antisymm (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) hQO
      ((show localOrbit T L ≤ H from le_sup_left).trans hHQ))
      (pCoreIn_mono_of_normalizes le_sup_left hHO)
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_normalizer_componentOrbit L T
  have hMQ : D.maximalLocal ≤ normalizer (Q : Set G) := by
    rw [hQOcore]
    exact normalizer_le_normalizer_characteristic_image (localOrbit T L)
      (pCore 2 (localOrbit T L))
  have hQM : Q ≤ D.maximalLocal := hQO.trans (localOrbit T L).le_normalizer
  have hMT : D.maximalLocal.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow D.maximalLocal (T.subtype hTM)
    rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM] at hh
  refine ⟨hQOcore, le_antisymm ?_ ?_⟩
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 D.maximalLocal)
      (hMT.trans le_sup_right)
      (hHO.trans (D.maximalLocal.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image D.maximalLocal (pCore 2 D.maximalLocal))))
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) hQM hMQ

end CFSG.Quasithin.Chapter10
