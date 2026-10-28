module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherG2
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawStar

/-!
# Higher G₂ star exclusion at the original raw component

The literal C.2.7 core-to-star map composes with the supplied native marking.
Its universal covering kernel is a two-group, hence vanishes in the actual
full two-core quotient. Both native residuals then force original marked
placement of this same L, contradicting the C.2.7 outside condition.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Atlas.G2
variable {G : Type*} [Group G] [Finite G]

/-- The actual C.2.7 star cannot be a higher-field G₂ group. -/
theorem PreparedChosenModule.raw_constrained_not_higherG2_star
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
    (e : starImage L ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2) L ≃* Model F) : False := by
  let := hi.quasisimple
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  let : Fact (2 < Nat.card F) := ⟨by omega⟩
  let c : Covering (L ⧸ pCore 2 L) (Model F) :=
    ⟨e.toMonoidHom.comp (coreToStar hi.normalizes),
      e.surjective.comp (coreToStar_surjective hi.normalizes)⟩
  have hinj : Function.Injective c.toMonoidHom :=
    (FiniteCover.cover_isUniversal F).injective_of_pGroup_kernel
      (FiniteCover.universalKernel_isPGroup_of_card_pow hF hn) c
      (pCore_quotient_pCore_eq_bot 2)
  let ec := MulEquiv.ofBijective c.toMonoidHom ⟨hinj,c.surjective⟩
  exact hi.outside (h.raw_higherG2_core_le_marked hG T hempty hM hJ hu hZ hZne hL hF hn ec)

end CFSG.Quasithin.Chapter15.Section01
