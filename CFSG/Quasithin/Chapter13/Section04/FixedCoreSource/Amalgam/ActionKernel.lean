module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.Locality
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.ReducedNormal.CentralSeedOvergroup
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Subnormal
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Residual
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Kernel control for the actual omega-center span

After locality, characteristic two and B.2.14 make V₀=⟨Ω₁(Z(T))^X⟩
two-reduced in the original join X. Each local two-residual moves the
seed: otherwise its Sylow supplement would centralize the seed, contrary
to the fixed-line index. F.6.7 therefore puts both local action kernels in
their two-cores. F.6.8 identifies their intersections with O₂(X).

Reducedness gives the reverse containment, proving
C_A(V₀)=C_B(V₀)=C_T(V₀)=O₂(X), with all subgroups embedded in the original
ambient group. Neither nonsolvability nor a structural alternative is assumed.
Source: Aschbacher–Smith, 13.4.7, printed p.899; B.2.14 and F.6.7–8.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open Stellmacher.SectionsFiveToSeven
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open ChapterF Chapter12.Section02 Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G]

private theorem seed_local_kernel {A B W : Subgroup G}
    (hg : IsGoldschmidtTriple A B) [W.Normal]
    (hseed : omegaOneCenter (A ⊓ B) ≤ W)
    (hmove : ⁅A, omegaOneCenter (A ⊓ B)⁆ ≠ ⊥) :
    A ⊓ centralizer (W : Set G) ≤ A.pCoreIn 2 := by
  apply (hg.left_subnormal_core_iff_not_residual_le _
    (inferInstance : (centralizer (W : Set G)).Normal).isSubnormal).mpr
  intro hres
  apply hmove
  apply commutator_eq_bot_iff_le_centralizer.mpr
  nth_rw 1 [← hg.left_residual_sup_intersection]
  refine sup_le (hres.trans (centralizer_le hseed)) ?_
  intro t ht z hz
  exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht |>.symm

/-- Local and Sylow kernels for a reduced module containing the original central seed. -/
theorem reduced_seed_kernel {A B W : Subgroup G}
    (hg : IsGoldschmidtTriple A B) (hW : IsPReduced 2 W)
    (hseed : omegaOneCenter (A ⊓ B) ≤ W)
    (hmoveA : ⁅A, omegaOneCenter (A ⊓ B)⁆ ≠ ⊥)
    (hmoveB : ⁅B, omegaOneCenter (A ⊓ B)⁆ ≠ ⊥) :
    A ⊓ centralizer (W : Set G) = pCore 2 G ∧
    B ⊓ centralizer (W : Set G) = pCore 2 G ∧
    (A ⊓ B) ⊓ centralizer (W : Set G) = pCore 2 G := by
  let := hW.normal
  have hA := seed_local_kernel hg hseed hmoveA
  have hB := seed_local_kernel hg.symm
    (by simpa only [inf_comm B A] using hseed)
    (by simpa only [inf_comm B A] using hmoveB)
  have hT : (A ⊓ B) ⊓ centralizer (W : Set G) = pCore 2 G :=
    le_antisymm (hg.normal_intersection_le_twoCore _ hA hB)
      (le_inf hg.twoCore_isGreatest.1.1 (le_centralizer_iff.mp hW.le_centralizer_pCore))
  have heA := hg.left_intersection_eq_core_intersection _ hA
  have heB := hg.symm.left_intersection_eq_core_intersection _ hB
  exact ⟨heA.1.trans (heA.2.trans hT), heB.1.trans (heB.2.trans (by
    simpa only [inf_comm B A] using hT)), hT⟩

/-- The original pair supplies locality, reducedness and all three exact kernels. -/
theorem original_pair_action_kernel {T : Sylow 2 G} {L V A B : Subgroup G}
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    let X := A ⊔ B
    let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    IsPReduced 2 (W.subgroupOf X) ∧
      A ⊓ centralizer (W : Set G) = X.pCoreIn 2 ∧
      B ⊓ centralizer (W : Set G) = X.pCoreIn 2 ∧
      (T : Subgroup G) ⊓ centralizer (W : Set G) = X.pCoreIn 2 := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z X
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  have hZT : Z ≤ (T : Subgroup G) := fun z hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hZC : Z ≤ centralizer (T : Set G) := fun z hz =>
    ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2
  have hWX : W ≤ X := conjugateSpanBy_le (hZT.trans hTX) X.le_normalizer
  have hlocal := original_pair_local D m hTA hTB eA eB hne hindexA hindexB
  let : IsElementaryAbelian 2 Z := omegaOneCenterAmbient_elementaryAbelian _
  have hW : IsPReduced 2 (W.subgroupOf X) := reduced_conjugateSpan_of_sylow_central
    T X Z hTX hZT hZC (Chapter1.mem_He_iff.mp
      (Chapter1.lemma_1_1_4_6 T (h₀.qtke.evenCharacteristic T) hlocal))
  have hinter := intersection_eq_sylow hTA hTB eA eB hne
  have hg := pair_goldschmidt hTA hTB eA eB hne
  have homega : (omegaOneCenter ((A.subgroupOf X) ⊓ (B.subgroupOf X))).map X.subtype = Z := by
    change (omegaOneCenterAmbient ((A ⊓ B).subgroupOf X)).map X.subtype = _
    rw [hinter, ← omegaOneCenterAmbient_map_injective X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le hTX]
  have hseed : omegaOneCenter ((A.subgroupOf X) ⊓ (B.subgroupOf X)) ≤ W.subgroupOf X := by
    intro z hz
    exact le_conjugateSpanBy Z X (homega ▸ mem_map_of_mem X.subtype hz)
  have hmove (Y : Subgroup G) (hYX : Y ≤ X)
      (hi : (Z ⊓ centralizer (Y : Set G)).relIndex Z = 2) :
      ⁅Y.subgroupOf X, omegaOneCenter ((A.subgroupOf X) ⊓ (B.subgroupOf X))⁆ ≠ ⊥ := by
    intro hh
    have hm := congrArg (Subgroup.map X.subtype) hh
    rw [Subgroup.map_commutator, map_subgroupOf_eq_of_le hYX, homega, Subgroup.map_bot] at hm
    have hc : Z ≤ centralizer (Y : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hm)
    rw [inf_eq_left.mpr hc, relIndex_self] at hi
    omega
  obtain ⟨hA,hB,hT⟩ := reduced_seed_kernel hg hW hseed
    (hmove A le_sup_left hindexA) (hmove B le_sup_right hindexB)
  have hmap (Y : Subgroup G) (hYX : Y ≤ X)
      (hh : Y.subgroupOf X ⊓ centralizer (W.subgroupOf X : Set X) = pCore 2 X) :
      Y ⊓ centralizer (W : Set G) = X.pCoreIn 2 := by
    have hm := congrArg (Subgroup.map X.subtype) hh
    rw [← map_inf_centralizer_of_injective X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le hYX, map_subgroupOf_eq_of_le hWX] at hm
    exact hm
  refine ⟨hW,hmap A le_sup_left hA,hmap B le_sup_right hB,?_⟩
  apply hmap (T : Subgroup G) hTX
  change (A ⊓ B).subgroupOf X ⊓ _ = _ at hT
  rwa [hinter] at hT

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
