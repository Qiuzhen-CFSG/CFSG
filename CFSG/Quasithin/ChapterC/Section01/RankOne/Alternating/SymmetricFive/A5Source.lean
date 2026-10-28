module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.IndexTwo
public import Theory.Representation.BinaryPermutation.FiveCentralExtension.OuterCompatibility
import Mathlib.Tactic

/-!
# The S₅ source conclusion from its original A₅ marking

The two-residual maps onto the actual alternating subgroup. Its natural
quotient marking and exact fixed-space kernel therefore meet the lower
outer-compatibility theorem. This removes full S₅-equivariance as an input
to the Thompson/Baumann image and index-two Sylow placement conclusions.
Every original group, quotient map, module, Sylow subgroup and maximal
overgroup is retained.

Source: Aschbacher–Smith, C.1.24, E.2.3 and 3.1.7, printed pp.130–131,
216–217 and 575–576. This is the single-image S₅ case.
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
    (he : ∀ g ∈ alternatingGroup (Fin 5), ∀ v,
      p (NormalElementaryQuotient.representation U q hq hker g v) =
        coreRepresentation (Fin 5) g (p v))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup H) ≤ centralizer (U : Set H))

include hp he
/-- The exact original residual fixed kernel upgrades the natural A₅ marking
on this quotient to equivariance for the whole S₅ image. -/
theorem source_equivariant_of_alternating
    (hpk : p.ker = fixedSpace (NormalElementaryQuotient.representation U q hq hker)
      ((pResidual 2 H).map q)) :
    ∀ g v, p (NormalElementaryQuotient.representation U q hq hker g v) =
      coreRepresentation (Fin 5) g (p v) := by
  apply equivariant_of_alternating_fixed_kernel _ p hp he
  simpa only [source_residual_image q hq] using hpk

include hP hU hJ
/-- The source natural A₅ quotient alone gives the Thompson/Baumann image
and the actual index-two Sylow extension in the original conjugate span. -/
theorem source_alternating_quotient_conclusions
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
  have he' := source_equivariant_of_alternating U q hq hker p hp he hpk
  exact source_natural_quotient_conclusions T hP U hU q hq hker p hp he' hJ hpk


omit he in
/-- The same conclusions when the marking is given only on the literal
original two-residual, before passage through its image A₅. -/
theorem source_residual_quotient_conclusions
    (heK : ∀ k ∈ pResidual 2 H, ∀ v,
      p (NormalElementaryQuotient.representation U q hq hker (q k) v) =
        coreRepresentation (Fin 5) (q k) (p v))
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
  have he' : ∀ g ∈ alternatingGroup (Fin 5), ∀ v,
      p (NormalElementaryQuotient.representation U q hq hker g v) =
        coreRepresentation (Fin 5) g (p v) := by
    intro g hg v
    obtain ⟨k, hk, rfl⟩ : ∃ k ∈ pResidual 2 H, q k = g :=
      (source_residual_image q hq ▸ hg : g ∈ (pResidual 2 H).map q)
    exact heK k hk v
  exact source_alternating_quotient_conclusions T hP U hU q hq hker p hp he' hJ hpk

end CFSG.Quasithin.ChapterC.SymmetricFive
