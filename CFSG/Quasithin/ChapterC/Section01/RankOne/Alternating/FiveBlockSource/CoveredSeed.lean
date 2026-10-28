module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.CubicSeed
public import Theory.Representation.BinaryPermutation.FiveCentralExtension
/-!
# A fixed seed through the original S₅ central cover

The natural quotient has a proved equivariant section, constructed by the
cubic class-sum projector. The fixed pair-vector lifts into the original
omega center, and the selected cubic moves its image. This retains the
original central kernel instead of assuming a split module.
Source: C.1.21(4), C.1.23(1), printed pp.129–130; I.1.6(1).
-/
public section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
open Theory.SpecificGroups.SymmetricFive Theory.SpecificGroups.SymmetricFive.CubicSelection
variable {H : Type*} [Group H] [Finite H]
/-- The original central-cover projection supplies an actual noncentral
omega-center seed, through its proved equivariant section. -/
theorem selected_covered_omega_seed (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* Sym) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H)) (L P : Subgroup H)
    (hL : L.map q = alternatingGroup (Fin 5))
    (hP : P.map q = OuterFourGeometry.four) (hUP : U ≤ P)
    (p : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (p v))
    (hfix : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hk g v = v) :
    ⁅omegaOneCenterAmbient P,selectedResidual q L⁆ ≠ ⊥ := by
  let ρ := NormalElementaryQuotient.representation U q hq hk
  obtain ⟨s,hs,hse,_⟩ := BinaryPermutation.FiveCentralExtension.exists_section ρ p hp he hfix
  obtain ⟨v,hv,hm⟩ := cubic_moves_four_fixed
  let u : Additive U := s v
  have hu : p u = v := hs v
  have hz : (u.toMul : H) ∈ omegaOneCenterAmbient P := by
    apply (mem_omegaOneCenterAmbient_iff P _).mpr
    refine ⟨hUP u.toMul.property,?_,?_⟩
    · exact elemPow_eq_one_of_isElementaryAbelian (p:=2) (u.toMul : H) u.toMul.property
    · intro a ha
      have hf : ρ (q a) u = u := by
        change ρ (q a) (s v) = s v
        rw [←hse]
        exact congrArg s (hv ⟨q a,hP ▸ mem_map_of_mem q ha⟩)
      have hh := congrArg (fun w : Additive U => (w.toMul : H)) hf
      rw [NormalElementaryQuotient.representation_apply] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨y,hy,hyq⟩ := (selectedResidual_image q L hL ▸ cycle_mem : cycle ∈ (selectedResidual q L).map q)
  intro hc
  have hzC := (commutator_eq_bot_iff_le_centralizer.mp hc) hz
  have hf : ρ (q y) u = u := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (hzC y hy)
  have hh := he (q y) u
  rw [hf,hu,hyq] at hh
  exact hm hh.symm
end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
