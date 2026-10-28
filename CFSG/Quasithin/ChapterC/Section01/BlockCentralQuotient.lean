module
public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupAction.PPerfectCentralQuotientFixed

/-!
# Block modules through central two-group quotients

A surjection with two-group kernel identifies the two-core quotients and
maps the commutator layer U onto the target's U. When the kernel is central
and the domain is two-perfect, an element central modulo the kernel is
already central: its displacement homomorphism into the kernel is trivial.
Thus the fixed subgroup has exactly the required preimage, and the induced
isomorphism of U/C_U(K) respects the actual conjugation action.

This preserves a `BlockModuleModel`, including both its actor isomorphism
and its equivariance. It assumes neither a splitting nor a model of the
quotient group. The application is the checked central quotient in the
last step of Aschbacher–Smith 13.6.18, printed p.931 (PDF p.948); the block
module conventions are those of C.1.7, printed p.123.
-/

public section
namespace CFSG.Quasithin.ChapterC
open Subgroup
variable {K D A V : Type*} [Group K] [Group D] [Group A] [Group V]
  [Finite K] [Finite D]

omit [Finite K] [Finite D] in
private theorem central_comap (f : K →* D) (hf : Function.Surjective f)
    (hp : IsPPerfect 2 K) (hker : IsPGroup 2 f.ker) (hc : f.ker ≤ center K) :
    (center D).comap f = center K := by
  ext x
  constructor
  · intro hx
    have htop : IsPPerfect 2 (⊤ : Subgroup K) :=
      hp.of_surjective (topEquiv : (⊤ : Subgroup K) ≃* K).symm.toMonoidHom
        (topEquiv : (⊤ : Subgroup K) ≃* K).symm.surjective
    have hh := MulAut.fixed_of_fixed_mod_central_p_kernel f (MulAut.conj x) ⊤
      htop hker hc (by
        intro y _
        change f (x * y * x⁻¹) = f y
        rw [map_mul, map_mul, map_inv,
          ← mem_center_iff.mp hx (f y), mul_inv_cancel_right])
    apply mem_center_iff.mpr
    intro y
    exact (mul_inv_eq_iff_eq_mul.mp (hh y (mem_top y))).symm
  · intro hx
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y, rfl⟩ := hf y
    simpa only [map_mul] using congrArg f (mem_center_iff.mp hx y)

private theorem map_core (f : K →* D) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) : (pCore 2 K).map f = pCore 2 D := by
  rw [← f.comap_pCore_of_ker_isPGroup hf hker, map_comap_eq_self_of_surjective hf]

private theorem map_u (f : K →* D) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) : (blockU K).map f = blockU D := by
  rw [blockU, map_commutator, map_core f hf hker,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top_of_surjective f hf]
  rfl

private def uMap (f : K →* D) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) : blockU K →* blockU D where
  toFun u := ⟨f u, (map_u f hf hker) ▸ mem_map_of_mem f u.property⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' u w := Subtype.ext (map_mul f (u : K) (w : K))

private theorem uMap_surjective (f : K →* D) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) : Function.Surjective (uMap f hf hker) := by
  intro u
  have hu : (u : D) ∈ (blockU K).map f := by
    rw [map_u f hf hker]
    exact u.property
  obtain ⟨w, hw, he⟩ := hu
  exact ⟨⟨w, hw⟩, Subtype.ext he⟩

private theorem fixed_comap (f : K →* D) (hf : Function.Surjective f)
    (hp : IsPPerfect 2 K) (hker : IsPGroup 2 f.ker) (hc : f.ker ≤ center K) :
    (blockFixed D).comap (uMap f hf hker) = blockFixed K := by
  ext u
  change f (u : K) ∈ center D ↔ (u : K) ∈ center K
  change (u : K) ∈ (center D).comap f ↔ _
  rw [central_comap f hf hp hker hc]

/-- Central two-group quotients of two-perfect groups preserve the genuine
block module model, including its quotient actor and conjugation action. -/
theorem BlockModuleModel.exists_of_central_two_quotient (f : K →* D) (hf : Function.Surjective f)
    (hp : IsPPerfect 2 K) (hker : IsPGroup 2 f.ker) (hc : f.ker ≤ center K)
    (ρ : A →* MulAut V) (m : BlockModuleModel K ρ) :
    Nonempty (BlockModuleModel D ρ) := by
  let eQ := f.pCoreQuotientEquiv hf hker
  let eM := QuotientGroup.equivOfSurjectiveComap (uMap f hf hker)
    (uMap_surjective f hf hker) (blockFixed K) (blockFixed D) (fixed_comap f hf hp hker hc)
  have hQ (k : K) : eQ.symm (QuotientGroup.mk' (pCore 2 D) (f k)) =
      QuotientGroup.mk' (pCore 2 K) k := by
    apply eQ.injective
    simp only [MulEquiv.apply_symm_apply]
    rfl
  have hM (u : blockU K) : eM.symm (QuotientGroup.mk' (blockFixed D) (uMap f hf hker u)) =
      QuotientGroup.mk' (blockFixed K) u := by
    apply eM.injective
    simp only [MulEquiv.apply_symm_apply]
    rfl
  refine ⟨{ quotientIso := eQ.symm.trans m.quotientIso
            moduleIso := eM.symm.trans m.moduleIso
            intertwining := ?_ }⟩
  intro d u
  obtain ⟨k, rfl⟩ := hf d
  obtain ⟨w, rfl⟩ := uMap_surjective f hf hker u
  have hconj : blockConjugate D (f k) (uMap f hf hker w) =
      uMap f hf hker (blockConjugate K k w) := by
    apply Subtype.ext
    simp only [blockConjugate, uMap, MonoidHom.coe_mk, OneHom.coe_mk,
      map_mul, map_inv]
  change m.moduleIso (eM.symm _) = ρ (m.quotientIso (eQ.symm _)) (m.moduleIso (eM.symm _))
  rw [hconj, hM, hQ, hM]
  exact m.intertwining k w
end CFSG.Quasithin.ChapterC
