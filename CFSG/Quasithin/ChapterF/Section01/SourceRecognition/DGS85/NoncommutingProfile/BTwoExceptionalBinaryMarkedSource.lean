module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalParabolicsSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.MarkedRestoration
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalRigidity.G2
public import Theory.GroupTheory.Amalgam.ParabolicRecognition
public import Theory.GroupTheory.Amalgam.RestrictionProduct
public import Theory.GroupTheory.Amalgam.Reversal

/-!
# Compatible binary exceptional amalgams

The already proved binary parabolic equivalence identifies both endpoint
orders and the whole Borel with the native G₂(2)′ groups. Injectivity of the
original inclusions then makes that Borel Sylow in both endpoints. Sylow
alignment leaves a single overlap twist. The certified native theorem that
every overlap automorphism extends across the first endpoint removes this
twist and gives both commuting inclusion squares.

The original Borel is its two-core, so the reduced Borel is the original
Borel. The starred endpoint supplements identify the two reduced endpoints
with the original ones. These literal equalities transport the same marked
isomorphism to the reduced amalgam needed for the source graph. Binary path
parameters remain a separate obligation.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(10.9), printed p.163. The imported native overlap certificate retains its
ATLAS attribution in `LICENSES/ATLAS.txt`.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open Noncommuting DGS85.Reduction Theory.GroupTheory
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance binaryMarkedAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] :
    Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2

/-- The original binary exceptional amalgam with both overlap squares. -/
theorem original_bTwo_exceptional_binary_iso
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 2) :
    Nonempty (RankTwoAmalgam.Iso
      (OriginalExtension.originalAmalgam L S).reverse
      Atlas.G2.BinaryParabolicPair.derivedAmalgam) := by
  obtain ⟨eP⟩ := original_bTwo_exceptional_binary_parabolic_equiv
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  have hs : RankTwoAmalgam.SylowEmbedded 2 Atlas.G2.BinaryParabolicPair.derivedAmalgam :=
    RankTwoAmalgam.sylowEmbedded_ofSubgroups
      Atlas.G2.BinaryParabolicPair.derivedSylow _ _ _ _ _ rfl
  exact RankTwoAmalgam.iso_of_twist_factorization
    (hs.of_parabolicEquiv eP (inclusion_injective (commonBorel_le_parabolic 1))
      (inclusion_injective (commonBorel_le_parabolic 0))) hs eP
    GreenBook.ExceptionalRigidity.G2.simple_factorsThrough

/-- The same compatible binary marking on the literal reduced source amalgam. -/
theorem original_bTwo_exceptional_binary_reduced_iso
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 2) :
    Nonempty (RankTwoAmalgam.Iso
      (OriginalExtension.reducedAmalgam L S).reverse
      Atlas.G2.BinaryParabolicPair.derivedAmalgam) := by
  obtain ⟨eP⟩ := original_bTwo_exceptional_binary_iso
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  obtain ⟨_,hB,_⟩ := original_bTwo_exceptional_binary_full_endpoints
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  have hB₀ : B₀ L S = commonBorel L S :=
    le_antisymm (B₀_le h) (hB ▸ le_sup_right)
  have hP₀ (i : Fin 2) : P₀ L S i = parabolic L S i := by
    change starredParabolic L S i ⊔ B₀ L S = _
    rw [hB₀,h.starredParabolic_supplement i]
  let f : RankTwoAmalgam.Iso (OriginalExtension.reducedAmalgam L S)
      (OriginalExtension.originalAmalgam L S) := {
    left := MulEquiv.subgroupCongr ((P₀_eq_source h 0).symm.trans (hP₀ 0))
    middle := MulEquiv.subgroupCongr ((B₀_eq_source h).symm.trans hB₀)
    right := MulEquiv.subgroupCongr ((P₀_eq_source h 1).symm.trans (hP₀ 1))
    left_commutes := fun _ => by apply Subtype.ext; rfl
    right_commutes := fun _ => by apply Subtype.ext; rfl }
  exact ⟨f.reverse.trans eP⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
