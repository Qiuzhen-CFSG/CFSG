module
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.BinaryUpper.CompatibleFlags
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.HigherUpper.SolvableKernel
public import Theory.GroupTheory.PrimeRankNormalKernel
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Inputs
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.SpecificGroups.SL2.SmallOddComparisons

/-!
# Generation one for the invariant binary linear rows

The two compatible flag overgroups generate and contain the full original
Sylow subgroup. Their actual local structures give generation one: the
outer flag is solvable, and the middle flag is solvable or has a normal
two-kernel with simple PSL₃(2) generalized Fitting quotient. E-generation
lifts through that kernel. Restricting the literal two-core quotient to
the original C-component gives the application to I joined with T.

Source: Aschbacher--Smith E.1.12--14, p.214, applied in 10.3.3, pp.756--757.
The argument includes the actual graph extensions in the retained
Aut(L₄(2)) and Aut(L₅(2)) quotient rows. No splitting is imposed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
open ChapterE ChapterE.ValuesEvenClassical
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

theorem sqtk_quotient_of_two_kernel (hH : IsSQTK κ H)
    (Q : Subgroup H) [Q.Normal] (hQ : IsPGroup 2 Q) : IsSQTK κ (H ⧸ Q) := by
  refine ⟨?_, hH.isKGroup.quotient Q⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho Q hQ).trans
    (hH.stronglyQuasithin p hp ho)

theorem isEGenerated_of_binary_middle_section (hH : IsSQTK κ H)
    (hm : BinaryUpper.HasBinaryMiddleSection H) : IsEGenerated 1 H := by
  obtain ⟨Q, hQ, hp, hs, ⟨e⟩, S, hgen⟩ := hm
  let := hQ
  let := hs
  apply IsEGenerated.of_normal_two_subgroup Q hp
  exact RankTwoUpper.LinearThree.isEGenerated_of_source
    (sqtk_quotient_of_two_kernel hH Q hp) e S (by decide) (by simp) hgen

theorem isEGenerated_of_binary_flags (hH : IsSQTK κ H)
    {k : ℕ} (hk : k = 4 ∨ k = 5) (K : Subgroup H) [K.Normal]
    (S : Sylow 2 H) (e : K ≃* BinaryUpper.PSL k)
    (hgen : K ⊔ (S : Subgroup H) = ⊤) : IsEGenerated 1 H := by
  obtain ⟨e', _, hout, hmid, hS, hg⟩ :=
    BinaryUpper.exists_sylowAligned_structured_generating_flags hk K S e hgen
  have hmiddle : IsEGenerated 1 (BinaryUpper.ambientFlag K S e' (BinaryUpper.middleRoots k)) := by
    rcases hmid with ⟨_, hs⟩ | ⟨_, hm⟩
    · let := hs
      exact isEGenerated_one_of_solvable
    · exact isEGenerated_of_binary_middle_section (hH.subgroup _) hm
  apply IsEGeneratedAt.isEGenerated (T := S)
  intro Ω hΩ
  apply top_unique
  change ⊤ ≤ ChiefOrbit.generationTarget 1 S Ω
  rw [← hg]
  apply sSup_le
  intro P hP
  apply ChiefOrbit.overgroup_le_generationTarget S P (hS P hP) hΩ
  rcases hP with rfl | hP
  · let := hout
    exact isEGenerated_one_of_solvable
  · obtain rfl := hP
    exact hmiddle

theorem isEGenerated_of_normal_binary_component (hH : IsSQTK κ H)
    (S : Sylow 2 H) (K : Subgroup H) [K.Normal] (hK : K.IsCComponent)
    (hgen : K ⊔ (S : Subgroup H) = ⊤)
    {k : ℕ} (hk : k = 4 ∨ k = 5)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) k 2) : IsEGenerated 1 H := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let a : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := K.map q
  let b := cComponentTwoCoreQuotientEquiv hK
  let eB : B ≃* BinaryUpper.PSL k := b.symm.trans (e.trans (Atlas.fieldEquivPSL k a))
  let : B.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let S' := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hBS : B ⊔ (S' : Subgroup (H ⧸ pCore 2 H)) = ⊤ := by
    change K.map q ⊔ (S : Subgroup H).map q = ⊤
    rw [← Subgroup.map_sup, hgen, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  apply IsEGenerated.of_normal_two_subgroup (pCore 2 H) pCore_isPGroup
  exact isEGenerated_of_binary_flags (sqtk_quotient_of_two_kernel hH _ pCore_isPGroup)
    hk B S' eB hBS

variable {G : Type u} [Group G] [Finite G]

theorem invariant_binary_component_isEGenerated
    (hG : IsSimpleQTKE κ G) (T : Sylow 2 G) {M I : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hI : I ∈ Chapter1.cComponentsIn M)
    (hn : (T : Subgroup G) ≤ normalizer (I : Set G))
    {k : ℕ} (hk : k = 4 ∨ k = 5)
    (hm : ClassicalGroup.IsPSL (I ⧸ pCore 2 I) k 2) :
    IsEGenerated 1 (componentOrbit I (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G) := by
  rw [componentOrbit_sup]
  let Y := I ⊔ (T : Subgroup G)
  have hYM : Y ≤ M := sup_le hI.1 hTM
  have hY : IsSQTK κ Y := (IsSQTK.equiv (subgroupOfEquivOfLe hYM)).mp
    ((hG.twoLocal_sqtk hM.1).subgroup _)
  let K := I.subgroupOf Y
  let S := T.subtype (show (T : Subgroup G) ≤ Y from le_sup_right)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (sup_le I.le_normalizer hn)
  have hK : K.IsCComponent := hI.2.subgroupOf_of_le le_sup_left hYM
  let a := subgroupOfEquivOfLe (show I ≤ Y from le_sup_left)
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hKS : K ⊔ (S : Subgroup Y) = ⊤ := by
    change I.subgroupOf Y ⊔ (T : Subgroup G).subgroupOf Y = ⊤
    rw [← subgroupOf_sup (show I ≤ Y from le_sup_left) (show (T : Subgroup G) ≤ Y from le_sup_right)]
    exact subgroupOf_self Y
  exact isEGenerated_of_normal_binary_component hY S K hK hKS hk (hm.of_mulEquiv b)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
