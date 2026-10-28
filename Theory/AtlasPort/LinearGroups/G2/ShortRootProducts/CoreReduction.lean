module

public import Theory.AtlasPort.LinearGroups.G2.ShortRootProducts

/-!
# Reduction to the short-root centralizer core calculation

The sole additional premise here identifies the intrinsic two-core of the
short-root centralizer residual with the concrete long-root plane. Once
that identity is proved for the pinned curve C, equivariance extends it to
all genuinely marked short-root elements. The explicit product and all
long-root/two-central assertions are proved in `ShortRootProducts`.

This is a conditional reduction for case (a) on Aschbacher–Smith printed
pp.1202–1203, not a proof of the missing centralizer-core identity.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace Atlas.G2.ShortRootProducts
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

theorem core_products_of_rootC_core
    (hcore : ∀ a : F, a ≠ 0 → centralizerResidualCore (rootC a) = longRootLocal)
    {v : Model F} (hv : IsShortRootElement v) :
    (∀ w ∈ centralizerResidualCore v, w ≠ 1 →
      IsLongRootElement w ∧ IsSylowCentralInvolution w) ∧
    ∃ l : Model F, v * MulAut.conj l v ≠ 1 ∧
      v * MulAut.conj l v ∈ centralizerResidualCore v := by
  obtain ⟨a, ha, g, rfl⟩ := hv
  have hW : centralizerResidualCore (MulAut.conj g (rootC a)) =
      longRootLocal.map (MulAut.conj g).toMonoidHom := by
    rw [← map_centralizerResidualCore, hcore a ha]
  constructor
  · intro w hw hne
    rw [hW] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    have hxne : x ≠ 1 := by
      intro h
      exact hne (by simp [h])
    obtain ⟨b, hb, k, rfl⟩ := longRootLocal_isLong hx hxne
    have hlong : IsLongRootElement ((MulAut.conj g).toMonoidHom (MulAut.conj k (rootA b))) := by
      refine ⟨b, hb, g*k, ?_⟩
      simp [map_mul, MulAut.mul_apply]
    exact ⟨hlong, hlong.twoCentral⟩
  · let l := MulAut.conj g (rootD (1 : F))
    have h : MulAut.conj g (rootC a) * MulAut.conj l (MulAut.conj g (rootC a)) =
        MulAut.conj g (rootA a) := by
      have hh := congrArg (MulAut.conj g) (product_rootC_conjugate a (1 : F))
      simpa [l, MulAut.conj_apply, mul_assoc] using hh
    refine ⟨l, ?_, ?_⟩
    · rw [h]
      intro he
      have hA : rootA a = 1 := (MulAut.conj g).injective (he.trans (map_one _).symm)
      exact ha (rootA_injective (hA.trans rootA_zero.symm))
    · rw [h, hW]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom (rootA_mem_longRootLocal a)

end Atlas.G2.ShortRootProducts
