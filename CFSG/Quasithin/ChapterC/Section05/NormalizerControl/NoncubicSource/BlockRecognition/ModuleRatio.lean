module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.ImageAction
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.Transport
public import Theory.Representation.BinaryOffender.CubicSection
/-!
# The source ratio on the intrinsic noncentral block module

Dualizing the full moved-action equivalence transports the source cubic
bound. The dual of U(L)/C_U(L) injects into the dual of U(L), so the same
bound holds on the actual irreducible block module. The proof preserves
the original core quotient and central projection.
Source: Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
open ExceptionalRestrictions ChapterB.QuasisimpleSource
private theorem cubicRatio_le_of_injection {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) G W}
    (i : ρ.IntertwiningMap σ) (hi : Function.Injective i)
    (h : cubicRatio σ ≤ 2) : cubicRatio ρ ≤ 2 := by
  obtain ⟨A,hA,hc,hd⟩ := (cubicRatio_le_nat_iff σ 2).mp h
  refine (cubicRatio_le_nat_iff ρ 2).mpr ⟨A,hA,?_,?_⟩
  · have he (g : G) (v : V) : i (displacement ρ g v) = displacement σ g (i v) := by
      simp only [displacement,LinearMap.sub_apply,LinearMap.id_apply,map_sub,
        IntertwiningMap.isIntertwining]
    intro a ha b hb c hca v
    apply hi
    rw [map_zero,he,he,he,hc a ha b hb c hca]
  · have hfix : (fixedSpace σ A).comap i.toLinearMap = fixedSpace ρ A := by
      ext v
      constructor
      · intro hv a
        apply hi
        exact (IntertwiningMap.isIntertwining _ _ i a v).trans (hv a)
      · intro hv a
        exact (IntertwiningMap.isIntertwining _ _ i a v).symm.trans (congrArg i (hv a))
    let q := (fixedSpace ρ A).mapQ (fixedSpace σ A) i.toLinearMap (le_of_eq hfix.symm)
    apply le_trans (LinearMap.finrank_le_finrank_of_injective (f := q) ?_) hd
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mapQ,hfix,Submodule.mkQ_map_self]

theorem blockModule_dual_cubic_le_of_image {L H W : Type*} [Group L] [Group H] [Finite H]
    [AddCommGroup W] [Module (ZMod 2) W]
    (h : IsShort L) (ρ : Representation (ZMod 2) H W) :
    letI := h.elementary
    letI := h.module_elementary
    ActionEquiv (uRepresentation h) ρ → cubicRatio ρ.dual ≤ 2 →
      cubicRatio (moduleRepresentation h).dual ≤ 2 := by
  let := h.finite
  let := h.elementary
  let := h.module_elementary
  change ActionEquiv (uRepresentation h) ρ → cubicRatio ρ.dual ≤ 2 →
    cubicRatio (moduleRepresentation h).dual ≤ 2
  intro E hc
  have he (g : H) (φ : Module.Dual (ZMod 2) W) :
      E.linearEquiv.dualMap (ρ.dual g φ) =
        (uRepresentation h).dual (E.groupEquiv.symm g) (E.linearEquiv.dualMap φ) := by
    ext u
    change φ (ρ g⁻¹ (E.linearEquiv u)) = φ (E.linearEquiv (uRepresentation h ((E.groupEquiv.symm g)⁻¹) u))
    rw [E.intertwines,E.groupEquiv.map_inv,E.groupEquiv.apply_symm_apply]
  have hu : cubicRatio (uRepresentation h).dual ≤ 2 :=
    ChapterK.Exceptional.cubicRatio_le_nat_of_equivariant ρ.dual (uRepresentation h).dual
      E.groupEquiv.symm.toMonoidHom E.groupEquiv.symm.injective E.linearEquiv.dualMap he 2 hc
  let d : (moduleRepresentation h).dual.IntertwiningMap (uRepresentation h).dual :=
    ⟨(moduleProjection (L := L)).dualMap,fun g => by
      ext φ u
      change φ (moduleRepresentation h g⁻¹ (moduleProjection u)) =
        φ (moduleProjection (uRepresentation h g⁻¹ u))
      rw [moduleProjection_equivariant]⟩
  exact cubicRatio_le_of_injection d
    (LinearMap.dualMap_injective_of_surjective moduleProjection_surjective) hu
end CFSG.Quasithin.ChapterC
