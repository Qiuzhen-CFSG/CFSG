module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherSymplectic

/-!
# Higher symplectic exclusion for the actual seed image

The original core quotient covers the actual normalizer-action image with
its full central kernel. The native symplectic cover theorem makes this
specific map bijective, so the already proved full-core source exclusion
applies to the same L. No C.2.7-star/image identification is made.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]

/-- The actual normalizer image of the original component has no
higher-field symplectic-four row. -/
theorem PreparedChosenModule.raw_component_normalizer_not_higher_symplectic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (houtM : ¬L ≤ M)
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let H := L ⊔ (S ⊓ normalizer (L : Set G))
    let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    let I := (L.subgroupOf H).map (QuotientGroup.mk' (centralizer (W : Set H)))
    I ≃* Sp F → False := by
  dsimp only
  intro e
  obtain ⟨_,f0,_,_,_,hf0,hk,_⟩ := h.raw_component_normalizer_quotient
    hG T hM hJ hu hZ hZne hL hi.quasisimple hi.fitting hi.outside houtM
  let f := e.toMonoidHom.comp f0
  have hf : Function.Surjective f := e.surjective.comp hf0
  have hker : f.ker ≤ center (L ⧸ pCore 2 L) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact hk
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn
  let ec := MulEquiv.ofBijective f
    (raw_local_symplectic_cover_bijective hi.quasisimple hfour f hf hker)
  exact h.raw_constrained_not_higher_symplectic_core hG T hempty hM hJ hu
    hZ hZne hL hi hF hn ec

end CFSG.Quasithin.Chapter15.Section01
