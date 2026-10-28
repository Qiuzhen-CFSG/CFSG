module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.CubicSelection
public import Theory.Representation.NormalElementaryQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.Setup
/-!
# The selected cubic moves an original omega-center vector

The natural S₅ fixed pair-vector pulls back to an involution centralizing
the selected two-group P. It belongs to Ω₁Z(P), and a lift of the selected
three-cycle moves it. This supplies the noncentral seed in C.1.21(4), on
literal original coordinates, without a fixed-point or movement premise.
Source: Aschbacher–Smith C.1.23(1), printed p.130.
-/
public section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
open Theory.SpecificGroups.SymmetricFive Theory.SpecificGroups.SymmetricFive.CubicSelection
variable {H : Type*} [Group H] [Finite H]
/-- The marked fixed pair-vector is an actual noncentral omega-center seed
in the original selected two-group. -/
theorem selected_omega_seed (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* Sym) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H)) (L P : Subgroup H)
    (hL : L.map q = alternatingGroup (Fin 5))
    (hP : P.map q = OuterFourGeometry.four) (hUP : U ≤ P)
    (e : Additive U ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5))
    (he : ∀ g v, e (NormalElementaryQuotient.representation U q hq hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (e v)) :
    ⁅omegaOneCenterAmbient P,selectedResidual q L⁆ ≠ ⊥ := by
  let ρ := NormalElementaryQuotient.representation U q hq hk
  obtain ⟨v,hv,hm⟩ := cubic_moves_four_fixed
  let u : Additive U := e.symm v
  have hu : e u = v := e.apply_symm_apply v
  have hz : (u.toMul : H) ∈ omegaOneCenterAmbient P := by
    apply (mem_omegaOneCenterAmbient_iff P _).mpr
    refine ⟨hUP u.toMul.property,?_,?_⟩
    · exact elemPow_eq_one_of_isElementaryAbelian (p:=2) (u.toMul : H) u.toMul.property
    · intro p hp
      have hf : ρ (q p) u = u := by
        apply e.injective
        rw [he,hu]
        exact hv ⟨q p,hP ▸ mem_map_of_mem q hp⟩
      have hh := congrArg (fun w : Additive U => (w.toMul : H)) hf
      rw [NormalElementaryQuotient.representation_apply] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨y,hy,hyq⟩ := (selectedResidual_image q L hL ▸ cycle_mem : cycle ∈ (selectedResidual q L).map q)
  intro hc
  have hzC := (commutator_eq_bot_iff_le_centralizer.mp hc) hz
  have hfix : ρ (q y) u = u := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (hzC y hy)
  have hh := he (q y) u
  rw [hfix,hu,hyq] at hh
  exact hm hh.symm

end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
