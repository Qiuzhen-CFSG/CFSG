module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Transport
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Filters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.G2NativeApplication
public import Theory.SpecificGroups.G2.LocalAutomorphismCores
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.LongCore

/-!
# Original A5-pair core control in the reduced G₂ row

A binary short parabolic is solvable, so either orientation of the original
A5 pair forces a nonbinary field. Both full native parabolic cores lie in
their concrete solvable residuals. The unchanged reduced cores and
residuals therefore identify the original factors with the original
parabolic residuals, without assuming their perfectness.

Native restoration preserves the full Borel and both endpoint maps. Its
residual markings now mark the actual original factors, and the native
quotient-action calculation controls both literal joins with S. The
one-normalized-Borel argument then places S in both original factors.
No complement, original marking or core equality is an input.

Source: DGS (15.2), pp.226–228; Aschbacher–Smith F.1.12(I)(3) and
its proof, pp.262–264. The native model facts are from the licensed
ATLAS port, reused through their existing imports.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.A5PairCatalogue.G2
open Subgroup Theory.GroupTheory RankTwoAmalgam
open DGS85.OriginalExtension
open Chapter6.Source.RankOneGeneric.Global.OriginalG2
open Atlas.G2 Atlas.G2.LieParabolicSetup
variable (F : Type) [Field F] [Finite F] [CharP F 2]

private theorem model_core_le_residual (hq : 2 < Nat.card F) (b : Bool) :
    pCore 2 (G2Native.endpoint F b) ≤ solvableResidual (G2Native.endpoint F b) := by
  cases b
  · change pCore 2 (parabolic₂ (F := F)) ≤ solvableResidual (parabolic₂ (F := F))
    apply (map_le_map_iff_of_injective parabolic₂.subtype_injective).mp
    rw [HigherFieldResiduals.parabolic₂_residual hq]
    change (parabolic₂ (F := F)).pCoreIn 2 ≤ local₂
    rw [EvenLocal.parabolic₂_pCoreIn]
    exact radical₂_le_local₂
  · change pCore 2 (parabolic₁ (F := F)) ≤ solvableResidual (parabolic₁ (F := F))
    apply (map_le_map_iff_of_injective parabolic₁.subtype_injective).mp
    rw [HigherFieldResiduals.parabolic₁_residual hq]
    change (parabolic₁ (F := F)).pCoreIn 2 ≤ local₁
    rw [parabolic₁_pCore, ←local₁_pCore]
    exact map_subtype_le _

private theorem core_eq {X : Type*} [Group X] (hq : 2 < Nat.card F)
    (K U : Subgroup X) (hn : U ≤ normalizer (K : Set X))
    (f : X →* MulAut (Model F)) (hf : Function.Injective f) (b : Bool)
    (hK : K.map f = (localFactor F b).map MulAut.conj) :
    (K ⊔ U).pCoreIn 2 = K.pCoreIn 2 := by
  apply map_injective hf
  rw [map_pCoreIn_of_injective 2 _ _ hf,map_pCoreIn_of_injective 2 _ _ hf,
    Subgroup.map_sup,hK]
  apply LocalAutomorphismCores.join_core hq b (U.map f)
  change U.map f ≤ normalizer ((localFactor F b).map MulAut.conj : Set _)
  rw [←hK]
  exact (map_mono hn).trans (le_normalizer_map f)

private theorem original_local_core
    {G : Type*} [Group G] [Finite G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (i : Fin 2)
    (a : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))
    (hq : 2 < Nat.card F) (b : Bool)
    (e : parabolic L (SuzukiContainment.reducedSylow L S) i ≃* G2Native.endpoint F b)
    (f : parabolic L S i →* MulAut (Model F)) (hf : Function.Injective f)
    (hr : (solvableResidual (parabolic L S i)).map f = (localFactor F b).map MulAut.conj) :
    twoCore (L i ⊔ S) = twoCore (L i) := by
  let P := parabolic L S i
  have hLP : L i ≤ P := le_sup_left.trans le_sup_left
  have hSP : S ≤ P := le_sup_right.trans le_sup_left
  have he : (L i).subgroupOf P = solvableResidual P := by
    apply map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le hLP]
    exact local_eq_residual_of_reduced_equiv h i a e (model_core_le_residual F hq b)
  have hmark : ((L i).subgroupOf P).map f = (localFactor F b).map MulAut.conj := by
    rw [he]
    exact hr
  have hnorm : S.subgroupOf P ≤ normalizer ((L i).subgroupOf P : Set P) := by
    rw [←subgroupOf_normalizer_eq hLP]
    exact comap_mono (h.S_normalizes i)
  have hh := congrArg (map P.subtype) (core_eq F hq ((L i).subgroupOf P)
    (S.subgroupOf P) hnorm f hf b hmark)
  rw [map_pCoreIn_of_injective 2 _ _ P.subtype_injective,
    map_pCoreIn_of_injective 2 _ _ P.subtype_injective,Subgroup.map_sup,
    map_subgroupOf_eq_of_le hLP,map_subgroupOf_eq_of_le hSP] at hh
  exact hh

variable {G : Type*} [Group G] [Finite G] {K R S : Subgroup G}

omit [Finite G] in
private theorem parameter
    (a : ∀ i, Nonempty ((![K,R] i ⧸ pCore 2 (![K,R] i)) ≃* alternatingGroup (Fin 5)))
    (b : Bool) (e : Iso (reducedAmalgam ![K,R] S) (G2Native.amalgam F b)) :
    2 < Nat.card F := by
  by_contra hgt
  have htwo : Nat.card F = 2 := by have := Finite.one_lt_card (α := F); omega
  let := Chapter6.Source.RankOneGeneric.Global.G2Short.parabolic_solvable_of_card_two htwo
  cases b
  · let j : _ ≃* parabolic₁ (F := F) := e.right
    exact overgroup_not_solvable 1 (a 1).some (le_sup_left.trans le_sup_left)
      (Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective)
  · let j : _ ≃* parabolic₁ (F := F) := e.left
    exact overgroup_not_solvable 0 (a 0).some (le_sup_left.trans le_sup_left)
      (Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective)

/-- A reduced G₂ comparison controls both original join cores and both
containments. Original perfectness and factor markings are derived, and
only one original Borel is required to normalize S. -/
theorem core_and_containment (h : HypothesisF11 ![K,R] S)
    (a : ∀ i, Nonempty ((![K,R] i ⧸ pCore 2 (![K,R] i)) ≃* alternatingGroup (Fin 5)))
    (hnorm : ∃ j, borel (![K,R] j) S ≤ normalizer (S : Set G))
    (b : Bool) (e : Iso (reducedAmalgam ![K,R] S) (G2Native.amalgam F b)) :
    (∀ i, twoCore (![K,R] i ⊔ S) = twoCore (![K,R] i)) ∧
      (∀ i, S ≤ ![K,R] i) := by
  have hq := parameter F a b e
  obtain ⟨f⟩ := exists_original_g2_marking_of_reduced_iso h F hq b e
  have hc : ∀ i, twoCore (![K,R] i ⊔ S) = twoCore (![K,R] i) := by
    intro i
    fin_cases i
    · exact original_local_core F h 0 (a 0).some hq b e.left
        f.left f.left_injective f.left_residual
    · exact original_local_core F h 1 (a 1).some hq (!b) e.right
        f.right f.right_injective f.right_residual
  exact ⟨hc,h.a5_pair_containment_of_core_eq a hnorm hc⟩

end CFSG.Quasithin.ChapterF.Source.A5PairCatalogue.G2
