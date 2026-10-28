module
public import CFSG.Quasithin.ChapterB.Section02.BaumannFrattini
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPair
public import CFSG.Quasithin.Chapter14.Section01.AlternatingThree.Centralizer
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.ReducedModule
public import CFSG.Quasithin.MainForward.SourceReduction

/-!
# The original uniform pair and the centralizing branch of 14.1.11

The full C.1.18 source constructs one pair on Baum(T) before every maximal
local overgroup M. The first member's central restriction is nontrivial
and has its full ambient centralizer in the distinguished Mc. For each M
whose actual localModule is centralized by J(T), the proved Frattini
argument gives precisely M = C_M(V(M)) N_M(C₂) for this same pair.

All pair-existence, elementary-module and Frattini inputs are derived
from the original simple QTKE geometry. The noncentral branch still needs
the original fixed-pair C.1.28 local selection and block lift; the stronger
full characteristic-normalizer control is not assumed here.
Source: Aschbacher–Smith 14.1.11, printed p.978, and 15.1.3, p.1086.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
open ChapterB ChapterC.GlaubermanNiles ChapterB.BaumannFrattini
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Literal localModule factorization in the source centralizing branch. -/
theorem source_centralizing_factorization
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (C : Subgroup (baumann (T : Subgroup G))) [C.Characteristic] :
    M = (M ⊓ centralizer (localModule T M : Set G)) ⊔
      (M ⊓ normalizer (C.map (baumann (T : Subgroup G)).subtype : Set G)) := by
  have hH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1,hM.2⟩
  let : IsElementaryAbelian 2 (localModule T M) := localModule_elementary_from_source hG T hH
  let := (localModule_reduced_from_source hG T hH).normal
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  exact centralizing_characteristic_factorization T M (localModule T M) hM.2
    (conjugateSpanBy_le_self (fun z hz => hM.2 ((mem_omegaOneCenterAmbient_iff _ z).mp hz).1)) (le_inf (hJT.trans hM.2) hJ) C

/-- One source pair controls every original centralizing local overgroup. -/
theorem source_uniform_pair
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G) :
    ∃ D : CharacteristicPair (baumann (T : Subgroup G)),
      D.Universal.{u,u} ∧ ChapterC.RankOne.ChiProduct.FixedPair.firstSeed T D ≠ ⊥ ∧
      ∀ M ∈ maximalTwoLocalOvergroups (T : Subgroup G),
        elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) →
        M = (M ⊓ centralizer (localModule T M : Set G)) ⊔
          (M ⊓ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G)) := by
  obtain ⟨D,hD,hseed⟩ := ChapterC.RankOne.ChiProduct.FixedPair.exists_uniform_pair.{u,u}
    T (MainForward.sylow_ne_bot hG T)
  refine ⟨D,hD,hseed,?_⟩
  intro M hM hJ
  let : D.second.Characteristic := D.second_characteristic
  exact source_centralizing_factorization hG T hM hJ D.second

/-- The same central restriction has its full centralizer in the unique Mc. -/
theorem firstSeed_centralizer_le_partner
    (T : Sylow 2 G) (D : CharacteristicPair (baumann (T : Subgroup G))) {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    centralizer (ChapterC.RankOne.ChiProduct.FixedPair.firstSeed T D : Set G) ≤ Mc := by
  let C := ChapterC.RankOne.ChiProduct.FixedPair.firstSeed T D
  let : Nontrivial C := (nontrivial_iff_ne_bot C).mpr (ChapterC.RankOne.ChiProduct.FixedPair.firstSeed_ne_bot T D)
  obtain ⟨z,hne⟩ := exists_ne (1 : C)
  exact (centralizer_le (Set.singleton_subset_iff.mpr z.property)).trans
    (Chapter14.AlternatingThree.central_involution_centralizer_le_partner T hu z.property.1
      (fun he => hne (Subtype.ext he)))

end CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
