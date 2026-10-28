module

public import CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry.FlagFactorization
public import Theory.Representation.G2BinaryIsotropicThree.IntrinsicPoint


/-!
# Local changes of the unitary three-space marking fix its point

The intrinsic octonion point transports through the original automizer map.
Consequently N_G(V)∩N_G(R) centralizes the literal marked involution whenever
R has the standard three-space coordinates. This retains the original
normalizer and the original elementary subgroup, and controls local changes
of marking in the conjugator adjustment.

Source: Aschbacher–Smith 13.3.12(4), printed p.890.
-/

public section

open Subgroup Module Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open Atlas.G2.Natural.BinaryIsotropicThree
variable {G : Type*} [Group G] {V R : Subgroup G} [IsElementaryAbelian 2 V]

theorem local_normalizer_three_fixes_point
    (E : Additive V≃ₗ[ZMod 2] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hR : (ambientSpace (V:=V) R).map E.toLinearMap=target false)
    (g : normalizer (V:Set G)) (hgR : g.val∈normalizer (R:Set G)) :
    Commute g.val (E.symm firstVector).toMul.val := by
  let a : Automizer V := V.normalizerMonoidHom.rangeRestrict g
  have hinv : ∀v∈target false,rho (f a) v∈target false := by
    intro v hv
    rw [←hR] at hv ⊢
    obtain ⟨w,hw,rfl⟩ := hv
    change rho (f a) (E w)∈(ambientSpace (V:=V) R).map E.toLinearMap
    rw [←he]
    refine ⟨automizerRepresentation V a w,?_,rfl⟩
    change (V.normalizerMonoidHom g w.toMul).val∈R
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp hgR w.toMul.val).mp hw
  have hp := point_fixed_of_target_invariant (f a) hinv
  have heq : automizerRepresentation V a (E.symm firstVector)=E.symm firstVector := by
    apply E.injective
    rw [he,E.apply_symm_apply,hp]
  have hv := congrArg (fun v : Additive V=>v.toMul.val) heq
  change (V.normalizerMonoidHom g (E.symm firstVector).toMul).val=(E.symm firstVector).toMul.val at hv
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hv
  exact mul_inv_eq_iff_eq_mul.mp hv

theorem local_normalizer_three_le_point_centralizer
    (E : Additive V≃ₗ[ZMod 2] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hR : (ambientSpace (V:=V) R).map E.toLinearMap=target false) :
    normalizer (V:Set G)⊓normalizer (R:Set G)≤
      centralizer ({(E.symm firstVector).toMul.val}:Set G) := by
  intro g hg
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (local_normalizer_three_fixes_point E f he hR ⟨g,hg.1⟩ hg.2).eq
end CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
