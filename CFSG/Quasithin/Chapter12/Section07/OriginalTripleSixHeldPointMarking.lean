module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldSylowComplement
public import Theory.SpecificGroups.BinaryLinear.AffineFourSplitMarking
public import Theory.GroupTheory.Recognition.TransvectionFive.Marking
import all Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.ElementarySixteenComplement

/-! The actual original Sylow complement reconstructs a full marked
centralizer from its supplied invariant elementary sixteen. All subgroup
transport retains the original A and original point z. -/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Construct the entire marked transvection centralizer once the actual
invariant elementary sixteen has been extracted from the original square action. -/
theorem original_tripleSix_escaping_point_marking
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (z : G) (hz : z ≠ 1) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hzA : z ∈ A) (hA : Nat.card A = 16)
    (hAT : A ≤ (T : Subgroup G))
    (hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hCA : centralizer ({z} : Set G) ≤ normalizer (A : Set G))
    (hself : centralizer ({z} : Set G) ⊓ centralizer (A : Set G) ≤ A)
    (hC : Nat.card (centralizer ({z} : Set G)) = 21504) :
    ∃ F : TransvectionFive.MarkedCentralizer z, A = F.column := by
  let C := centralizer ({z} : Set G)
  let S := T.subtype hTC
  obtain ⟨L, hL⟩ := original_tripleSix_escaping_sylow_complement
    h structural D a t ht heven hout A hA hAT (hTC.trans hCA)
    ((inf_le_inf_right _ hTC).trans hself)
  let e : S ≃* T := subgroupOfEquivOfLe hTC
  have heA : ((A.subgroupOf C).subgroupOf S) =
      (A.subgroupOf T).comap e.toMonoidHom := by
    ext x
    rfl
  have hsplit : ∃ L' : Subgroup S, ((A.subgroupOf C).subgroupOf S).IsComplement' L' := by
    refine ⟨L.comap e.toMonoidHom, ?_⟩
    rw [heA]
    exact Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.ElementarySixteenComplement.complement_comap
      e (A.subgroupOf T) L hL
  obtain ⟨M⟩ := BinaryLinear.Affine.exists_pointMarking_of_sylow_split_sixteen
    z hz A hzA hA (hAT.trans hTC) hCA hself hC S hsplit
  exact ⟨TransvectionFive.markingOfAffine M hz, TransvectionFive.markingOfAffine_column M hz⟩

end CFSG.Quasithin.Chapter12.Section07
