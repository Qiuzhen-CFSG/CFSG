module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Baumann
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.ResidualGeometry
public import CFSG.Quasithin.ChapterB.Section02.Baumann.ActionQuotient
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.FrattiniSource
public import Theory.SpecificGroups.SymmetricTwoResidual
import Mathlib.Tactic


/-!
# The actual S₅ application of Baumann's argument

The previously constructed Thompson four-group and an actual even five-cycle
lift supply two residual conjugates generating the action image. Their fixed
codimensions are two and two, while the residual codimension is four. The
natural quotient comparison excludes strong offenders. The universal genuine
minimal-parabolic Frattini theorem discharges the remaining B.2.18 premise,
giving the alpha decomposition and Sylow saturation in the actual centralizer.

Source: Aschbacher–Smith, B.2.18, C.1.24 and E.2.3, pp.81, 130–131 and216–217.
-/

public section

open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.SymmetricFive
open ChapterB BinaryPermutation BinaryPermutation.FiveCentralExtension
variable {H : Type*} [Group H] [Finite H]

theorem source_residual_image (q : H →* Sym) (hq : Function.Surjective q) :
    (pResidual 2 H).map q = alternatingGroup (Fin 5) := by
  rw [map_pResidual_of_surjective 2 q hq, Equiv.Perm.twoResidual_eq_alternating]

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

theorem source_alpha_and_saturation :
    (pCore 2 (pResidual 2 H)).map (pResidual 2 H).subtype ≤ baumann (T : Subgroup H) ∧
      thompsonAlpha (T : Subgroup H) =
        (thompsonAlpha (T : Subgroup H) ⊓ centralizer (pResidual 2 H : Set H)) ⊔
          (U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup H) : Set H)) ∧
      IsSylowSubgroupIn (baumann (T : Subgroup H) ⊓ centralizer (U : Set H))
        ((pResidual 2 H ⊔ baumann (T : Subgroup H)) ⊓ centralizer (U : Set H)) := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hUT : U ≤ T := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
  have hc : ∀ A, fixedCodim ρ A = fixedCodim (coreRepresentation (Fin 5)) A :=
    source_fixedCodim U T hUT q hq hker p hp he hk hJ
  have hno : ¬ IsStrongFFModule ρ := by
    rintro ⟨A, hA⟩
    exact ChapterB.Offenders.Odd.not_isStrongOffender_core (Or.inl rfl) A
      ⟨hA.1, (hc A) ▸ hA.2⟩
  have hno' := BaumannArgument.noStrong_of_centralizer_quotient U q hq hker hno (T : Subgroup H)
  obtain ⟨a, ha⟩ := source_thompson_conjugate U T hUT q hq hker p hp he hk hJ
  have hK := source_residual_image q hq
  obtain ⟨g, hg, hqg⟩ : ∃ g ∈ pResidual 2 H, q g = a * fiveCycle * a⁻¹ := by
    exact (hK ▸ conjugate_fiveCycle_even a : a * fiveCycle * a⁻¹ ∈ (pResidual 2 H).map q)
  have himage : ((elementaryAbelianMaxJ (T : Subgroup H)).map (MulAut.conj g).toMonoidHom).map q =
      ((elementaryAbelianMaxJ (T : Subgroup H)).map q).map (MulAut.conj (q g)).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]
  have hgen : (pResidual 2 H).map q ≤ (elementaryAbelianMaxJ (T : Subgroup H)).map q ⊔
      ((elementaryAbelianMaxJ (T : Subgroup H)).map (MulAut.conj g).toMonoidHom).map q := by
    rw [himage, ha, hqg, two_conjugate_four_groups_generate]
    exact le_top
  have hcod : 2 * BaumannArgument.fixedCodim U (elementaryAbelianMaxJ (T : Subgroup H)) ≤
      BaumannArgument.fixedCodim U (pResidual 2 H) := by
    rw [BaumannArgument.fixedCodim_eq_centralizer_quotient U q hq hker,
      BaumannArgument.fixedCodim_eq_centralizer_quotient U q hq hker,
      hc, hc, ha, fixedCodim_map_conj, hK, fixedCodim_alternating,
      ChapterB.Offenders.Odd.fixedCodim_core_disjointTranspositions (Or.inl rfl) le_rfl]
  exact RankOneBaumann.two_conjugate_alpha_and_saturation T hP U hU hJ q hker
    (RankOneBaumann.residual_centralizer_le_coreFrattini T hP U hU hJ) hno' g hg hgen hcod
end CFSG.Quasithin.ChapterC.SymmetricFive
