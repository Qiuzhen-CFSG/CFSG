module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.MaximalSpan
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.SylowLift
import Mathlib.Tactic

/-!
# The S₅ natural-quotient source conclusions

The original reduced normal module, faithful centralizer quotient and natural
quotient by the residual fixed space determine the Thompson and Baumann
images as transposition four-groups. The original Baumann subgroup lies with
index two in a Sylow subgroup of its product with the two-residual. This
Sylow subgroup lies in the span of its conjugates under the residual part of
the original unique maximal overgroup.

Source: Aschbacher–Smith, C.1.24, E.2.3 and 3.1.7, printed pp.130–131,
216–217 and 575–576. No image-Sylow or placement conclusion is assumed.
-/

public section

open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.SymmetricFive
open ChapterB BinaryPermutation BinaryPermutation.FiveCentralExtension
variable {H : Type*} [Group H] [Finite H]
variable (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (q : H →* Sym) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set H))
    (p : Additive U →ₗ[ZMod 2] core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hker g v) =
      coreRepresentation (Fin 5) g (p v))
    (hk : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hker g v = v)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup H) ≤ centralizer (U : Set H))
include hP hU hp he hk hJ

theorem source_index_two_sylow :
    ∃ S₁ : Subgroup H,
      IsSylowSubgroupIn S₁ (pResidual 2 H ⊔ baumann (T : Subgroup H)) ∧
      baumann (T : Subgroup H) ≤ S₁ ∧
      ((baumann (T : Subgroup H)).subgroupOf S₁).index = 2 ∧
      S₁ ≤ conjugateSpanBy (baumann (T : Subgroup H))
        (pResidual 2 H ⊓ minimalParabolicMax T hP) := by
  let S := baumann (T : Subgroup H)
  let I := conjugateSpanBy S (pResidual 2 H ⊓ minimalParabolicMax T hP)
  have hUT : U ≤ T := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
  obtain ⟨_, hcard, a, ha⟩ := source_thompson_baumann U T hUT q hq hker p hp he hk hJ
  have him : I.map q = pointFour.map (MulAut.conj a).toMonoidHom :=
    source_conjugate_span_image T hP q hq S inf_le_left a ha
  have hIcard : Nat.card (I.map q) = 24 := by
    rw [him, card_map_of_injective (MulAut.conj a).injective, pointFour_card]
  have hIL : I ≤ pResidual 2 H ⊔ S := conjugateSpanBy_le le_sup_right
    ((inf_le_left.trans le_sup_left).trans (pResidual 2 H ⊔ S).le_normalizer)
  have hsat := (source_alpha_and_saturation T hP U hU q hq hker p hp he hk hJ).2.2
  rw [← hker] at hsat
  exact sylow_extension_of_local_image q S (pResidual 2 H ⊔ S) I
    (T.isPGroup'.to_le inf_le_left) (le_conjugateSpanBy _ _) hIL hcard hIcard hsat

omit hk in
/-- The actual natural quotient by the residual fixed space gives both the
E.2.3 four-group image and the index-two Sylow subgroup used in 3.1.7. -/
theorem source_natural_quotient_conclusions
    (hpk : p.ker = fixedSpace (NormalElementaryQuotient.representation U q hq hker)
      ((pResidual 2 H).map q)) :
    (elementaryAbelianMaxJ (T : Subgroup H)).map q = (baumann (T : Subgroup H)).map q ∧
      Nat.card ((baumann (T : Subgroup H)).map q) = 4 ∧
      (∃ a : Sym, (baumann (T : Subgroup H)).map q =
        (ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom) ∧
      ∃ S₁ : Subgroup H,
        IsSylowSubgroupIn S₁ (pResidual 2 H ⊔ baumann (T : Subgroup H)) ∧
        baumann (T : Subgroup H) ≤ S₁ ∧
        ((baumann (T : Subgroup H)).subgroupOf S₁).index = 2 ∧
        S₁ ≤ conjugateSpanBy (baumann (T : Subgroup H))
          (pResidual 2 H ⊓ minimalParabolicMax T hP) := by
  have hk' : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hker g v = v := by
    intro v hv g hg
    have hh : v ∈ fixedSpace (NormalElementaryQuotient.representation U q hq hker)
        (alternatingGroup (Fin 5)) := by
      rw [← source_residual_image q hq, ← hpk]
      exact hv
    exact hh ⟨g, hg⟩
  have hUT : U ≤ T := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
  have hfour := source_thompson_baumann U T hUT q hq hker p hp he hk' hJ
  exact ⟨hfour.1, hfour.2.1, hfour.2.2,
    source_index_two_sylow T hP U hU q hq hker p hp he hk' hJ⟩
end CFSG.Quasithin.ChapterC.SymmetricFive
