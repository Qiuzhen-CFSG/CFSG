module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherSymplectic

/-!
# Excluding the higher symplectic C.2.7 star row

Native perfect central-cover recognition makes the actual core-to-star map
faithful. The full core exclusion then applies to the same original component,
with its marked intersection and both residual placements intact.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]

/-- The original C.2.7 star cannot be a higher-field symplectic-four group. -/
theorem PreparedChosenModule.raw_constrained_not_higher_symplectic_star
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : starImage L ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2) L ≃* Sp F) : False := by
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  let f := e.toMonoidHom.comp (coreToStar hi.normalizes)
  have hf : Function.Surjective f := e.surjective.comp (coreToStar_surjective hi.normalizes)
  have hk : f.ker ≤ center (L ⧸ pCore 2 L) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact coreToStar_ker_central_from_source hi
  let ec := MulEquiv.ofBijective f
    (raw_local_symplectic_cover_bijective hi.quasisimple hfour f hf hk)
  exact h.raw_constrained_not_higher_symplectic_core hG T hempty hM hJ hu hZ hZne hL hi hF hn ec

end CFSG.Quasithin.Chapter15.Section01
