module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FivePointCharacteristic.Covered
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.ControlSource
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.NaturalSource
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.RankOneComparison
public import Theory.SpecificGroups.SymmetricFive.TwoKernelSylow
public import Theory.GroupTheory.PrimeRankCyclicSylow
/-!
# A characteristic subgroup in the five-point C.1.26 application

Assume no nontrivial characteristic subgroup of the Sylow is normal. Its
characteristic-normalizer closure then lies in the unique maximal overgroup.
The canonical omega-center span is reduced and genuinely moved by the Thompson
subgroup. B.6.9 constructs its actual natural moved-section marking. Cyclic
Sylow three-groups exclude the two-factor row; the uniform C.1.18 linear row
and covered C.1.23 five-point row make the residual short, a contradiction.
No marking of the whole canonical module is assumed.
Source: Aschbacher–Smith C.1.26, p.132; 14.7.68(2), pp.1071–1072.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.FivePointCharacteristic
open ChapterB Chapter1.Section02 GlaubermanNiles FiveBlockSource ChapterB.QuasisimpleSource
open ChiProduct.SelectedRankOne
universe u v
variable {G : Type u} [Group G] [Finite G]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary
private theorem control_le_of_no_characteristic
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hno : ¬ ∃ A : Subgroup T, A.Characteristic ∧ A ≠ ⊥ ∧
      (A.map (T : Subgroup G).subtype).Normal) :
    (T : Subgroup G).characteristicNormalizerClosure ≤ minimalParabolicMax T hP := by
  apply (characteristicNormalizerClosure_le_iff _ _).mpr
  intro A hA hne
  let := hA
  have hn : normalizer (A.map (T : Subgroup G).subtype : Set G) ≠ ⊤ := by
    intro h
    exact hno ⟨A,hA,hne,normalizer_eq_top_iff.mp h⟩
  obtain ⟨M,hM,hNM⟩ := (eq_top_or_exists_le_coatom _).resolve_left hn
  have hTN : (T : Subgroup G) ≤ normalizer (A.map (T : Subgroup G).subtype : Set G) := by
    have := A.normal_of_characteristic
    exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le A)).mp (by
      simpa only [subgroupOf, comap_map_eq_self_of_injective (T : Subgroup G).subtype_injective] using
        (inferInstance : A.Normal))
  exact hNM.trans_eq (minimalParabolicMax_unique T hP hM (hTN.trans hNM))

theorem exists_normal_characteristic
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hfit : generalizedFitting G = pCore 2 G)
    (hc : (pResidual 2 G).IsCComponent)
    (eL : ((pResidual 2 G) ⧸ pCore 2 (pResidual 2 G)) ≃* alternatingGroup (Fin 5))
    (f : G →* Equiv.Perm (Fin 5)) (hf : IsPGroup 2 f.ker)
    (hshort : ¬ IsShort (pResidual 2 G)) :
    ∃ A : Subgroup T, A.Characteristic ∧ A ≠ ⊥ ∧
      (A.map (T : Subgroup G).subtype).Normal := by
  classical
  by_contra hno
  let M := minimalParabolicMax T hP
  have hM : M ≠ ⊤ := (minimalParabolicMax_spec T hP).1.1
  have hcpu := control_le_of_no_characteristic T hP hno
  have hTne : (T : Subgroup G) ≠ ⊥ := by
    intro hz
    apply hP.2
    rw [hz]
    exact le_normalizer_of_normal
  let U := normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G)
  have hU : IsPReduced 2 U := omegaCenter_normalClosure_reduced T
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit)
  let := hU.normal
  let := hU.elementary
  have hJ := thompson_moves_omega_closure_of_control T hTne U rfl M hcpu hM
  have hs : ¬ Group.IsSolvable G := by
    intro h
    let := h
    exact hc.not_isSolvable inferInstance
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = C := QuotientGroup.ker_mk' C
  let ρ := NormalElementaryQuotient.representation U q hq hk
  let P : Sylow 3 G := Classical.choice inferInstance
  have hcy := SymmetricFive.cyclic_three_sylow_of_two_kernel f hf P
  have hr : primeRank 3 (offenderSubgroup ρ) ≤ 1 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 (offenderSubgroup ρ).subtype
      (offenderSubgroup ρ).subtype_injective).trans
      (P.primeRank_le_one_of_surjective hcy q hq)
  rcases reduced_nonsolvable_natural_source hG T hP U hU hs hJ with
    ⟨hqs,c,⟨F,hn⟩ | ⟨e⟩⟩ | ⟨c,_,_⟩
  · have h := quasisimple_linear_outside_of_control T hP U q hq hk hqs c.sectionData
      F hn rfl hfit M hcpu hM
    exact hshort h.2.1.1.short
  · obtain ⟨e⟩ := e
    have h := five_marked_residual T hP U hU hJ q hq hk hqs c.sectionData e
      hfit hc eL M hcpu hM
    exact hshort h.2.1.1.short
  · have hh : 2 ≤ primeRank 3 (offenderSubgroup ρ) := c.two_le_three_rank
    omega
end CFSG.Quasithin.ChapterC.RankOne.FivePointCharacteristic
