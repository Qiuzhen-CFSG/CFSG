module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ActionKernel
public import CFSG.Quasithin.ChapterF.Section06.Elementary.ActionPrimeComparison
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.ComponentGeometry

/-!
# Actual components in the nonsolvable amalgam branch

F.6.8 makes the full action kernel solvable from its exact intersections
with the two vertices. A C-component therefore cannot centralize the
reduced omega span. The intrinsic omega-module criterion gives
faithful-local membership. Earlier 13.3.2 supplies Sylow invariance and
maximality; the SQTK component orbit bound then proves relative normality
in the join, since an index-two normalizer would contain a Sylow two-subgroup.

Nonsolvability supplies an actual C-component, so the existential endpoint
constructs its local-family memberships, normality and nontrivial action.
This supplies the component-selection step of 13.4.7 for every applicable
original pair. The model comparison, module alternatives and original-L₂
exclusions remain separate mathematical obligations. The earlier
Source1332OneTwo premise retains discharge with the source assembly.

Source: Aschbacher–Smith 13.4.5(1) and 13.4.7, pp.898–900; F.6.8, p.305.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open ChapterF Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource Chapter1.Section02.Adequate
variable {G : Type*} [Group G] [Finite G]

/-- F.6.8 makes a full normal kernel solvable when both vertex intersections
are exactly the ambient two-core. -/
theorem kernel_solvable_of_vertex_intersections {A B : Subgroup G}
    (hg : IsGoldschmidtTriple A B) (N : Subgroup G) [N.Normal]
    (hA : A ⊓ N = pCore 2 G) (hB : B ⊓ N = pCore 2 G) :
    Group.IsSolvable N := by
  let f := QuotientGroup.mk' N
  have hk (Y : Subgroup G) (hy : Y ⊓ N = pCore 2 G) :
      IsPGroup 2 (f.subgroupMap Y).ker := by
    have he : (f.subgroupMap Y).ker = (pCore 2 G).subgroupOf Y := by
      rw [ker_subgroupMap,QuotientGroup.ker_mk']
      ext y
      change (y:G) ∈ N ↔ (y:G) ∈ pCore 2 G
      rw [←hy]
      exact (and_iff_right y.property).symm
    rw [he]
    exact pCore_isPGroup.comap_subtype
  have hs := hg.action_kernel_solvable f (hk A hA) (hk B hB)
  rwa [QuotientGroup.ker_mk'] at hs

private theorem local_sqtk (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {H : Subgroup G} (hH : H ∈ Chapter1.H G) : IsSQTK KnownSimple.IsKnownSimple H := by
  let R := H.pCoreIn 2
  let N := normalizer (R : Set G)
  have hHN : H ≤ N := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hN : IsTwoLocal N := ⟨R,hH,isPGroup_pCoreIn 2 H,rfl⟩
  have hh := (hG.twoLocal_sqtk hN).subgroup (H.subgroupOf N)
  exact ⟨hh.stronglyQuasithin.of_injective
    (subgroupOfEquivOfLe hHN).symm.toMonoidHom (subgroupOfEquivOfLe hHN).symm.injective,
    hh.isKGroup.of_injective
      (subgroupOfEquivOfLe hHN).symm.toMonoidHom (subgroupOfEquivOfLe hHN).symm.injective⟩

/-- Every actual component of the original pair moves its reduced omega span,
and earlier 13.3.2 makes it relatively normal and faithful-local maximal. -/
theorem original_pair_component_geometry {T : Sylow 2 G} {L V A B : Subgroup G}
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent) :
    let X := A ⊔ B
    let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    K.Normal ∧ K.map X.subtype ∈ MainForward.faithfulLocalComponents T ∧
      K.map X.subtype ∈ Chapter1.LStar G T ∧
      (T : Subgroup G) ≤ normalizer (K.map X.subtype : Set G) ∧
      ⁅W,K.map X.subtype⁆ ≠ ⊥ := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z X
  let U := W.subgroupOf X
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  have hZX : Z ≤ X := by
    intro z hz
    exact hTX (((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
  have hWX : W ≤ X := conjugateSpanBy_le hZX X.le_normalizer
  have hlocal := original_pair_local D m hTA hTB eA eB hne hindexA hindexB
  obtain ⟨hred,hkerA,hkerB,_⟩ := original_pair_action_kernel h₀ D m
    hTA hTB eA eB hne hindexA hindexB
  let := hred.normal
  let N := centralizer (U : Set X)
  have hk (Y : Subgroup G) (hYX : Y ≤ X)
      (hy : Y ⊓ centralizer (W : Set G) = X.pCoreIn 2) :
      (Y.subgroupOf X) ⊓ N = pCore 2 X := by
    apply map_injective X.subtype_injective
    rw [←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le hYX,map_subgroupOf_eq_of_le hWX]
    exact hy
  have hs := kernel_solvable_of_vertex_intersections
    (pair_goldschmidt hTA hTB eA eB hne) N
    (hk A le_sup_left hkerA) (hk B le_sup_right hkerB)
  let : Group.IsSolvable N := hs
  have hm : ⁅U,K⁆ ≠ ⊥ := by
    intro hh
    have hKN : K ≤ N := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh)
    exact hK.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := inclusion hKN) (inclusion_injective hKN))
  let := hred.elementary
  have hU : U ≤ omegaOneCenterAmbient (pCore 2 X) := by
    intro u hu
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hred.le_pCore hu,elemPow_eq_one_of_isElementaryAbelian u hu,
        hred.le_centralizer_pCore hu⟩
  have hf : K.map X.subtype ∈ MainForward.faithfulLocalComponents T :=
    (mem_faithfulLocalComponents_iff T _).mpr
      (Section03.Noncentrality.source_component_faithful_local T X hTX hlocal.1
        (Chapter1.lemma_1_1_4_6 T (h₀.qtke.evenCharacteristic T) hlocal) K U hK hU hm)
  have hTK := (h1332 _ hf).1
  have hnormal : K.Normal := by
    rcases Chapter1.Section02.component_normal_or_index_two_source
      (local_sqtk h₀.qtke hlocal.1) hK with hn | hi
    · exact hn
    have hTN : (T : Subgroup G).subgroupOf X ≤ normalizer (K : Set X) := by
      have he : (K.map X.subtype).subgroupOf X = K :=
        comap_map_eq_self_of_injective X.subtype_injective K
      rw [←he,←subgroupOf_normalizer_eq (map_subtype_le K)]
      exact comap_mono hTK
    have hd := index_dvd_of_le hTN
    rw [hi] at hd
    exact ((T.subtype hTX).not_dvd_index hd).elim
  refine ⟨hnormal,hf,Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hf,hTK,?_⟩
  intro hh
  apply hm
  apply (map_eq_bot_iff_of_injective _ X.subtype_injective).mp
  rwa [map_commutator,map_subgroupOf_eq_of_le hWX]

/-- Nonsolvability constructs the actual component used in the source branch.
Its family memberships, relative normality and nontrivial action are proved
for the same subgroup of the same join. -/
theorem exists_original_pair_component {T : Sylow 2 G} {L V A B : Subgroup G}
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hnonsolv : ¬ Group.IsSolvable (A ⊔ B : Subgroup G)) :
    let X := A ⊔ B
    let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn X ∧
      K ∈ MainForward.faithfulLocalComponents T ∧ K ∈ Chapter1.LStar G T ∧
      X ≤ normalizer (K : Set G) ∧ (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ⁅W,K⁆ ≠ ⊥ := by
  let X := A ⊔ B
  obtain ⟨K,hK⟩ := exists_isCComponent_of_not_isSolvable hnonsolv
  obtain ⟨hn,hf,hstar,hTK,hm⟩ := original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  have hrestrict : (K.map X.subtype).subgroupOf X = K :=
    comap_map_eq_self_of_injective X.subtype_injective K
  have hc : ((K.map X.subtype).subgroupOf X).IsCComponent := hrestrict.symm ▸ hK
  have hn' : ((K.map X.subtype).subgroupOf X).Normal := hrestrict.symm ▸ hn
  exact ⟨K.map X.subtype,⟨map_subtype_le _,hc⟩,hf,hstar,
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp hn',hTK,hm⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
