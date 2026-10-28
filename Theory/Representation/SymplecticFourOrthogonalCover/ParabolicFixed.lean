module
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedLifting
public import Theory.SpecificGroups.SymplecticFour.NaturalScalarCubic
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Local fixed-space commutators in the orthogonal cover of Sp₄(4)

The two-core of the point local fixes the natural point, and that of the plane
local fixes the natural plane. The orthogonal lift has zero quadratic correction
on these spaces under their respective local groups. Thus their action
differences have zero central coordinate. Conjugating gives a complementary
coordinate subspace for every conjugate local.

Every finite binary cover is a quotient of the orthogonal model over its
original natural projection. A core-fixed vector has core-fixed lifts through
that projection. A locally moved vector which is globally fixed therefore lifts
to both the central radical and the complementary coordinate subspace, and is
zero. This applies directly to a fully moved subspace inside the fixed space of
the literal local two-core.

Source: Aschbacher--Smith, Proposition 9.4.1, printed p.735/PDF p.752 of
`refs/quasithin.pdf`, the Sp₄(4) fixed-space splitting argument; the cover itself
is I.2.3(1), printed p.413. The subgroup is the actual point or plane local,
including its own two-core, throughout.
-/

public section

open Matrix Subgroup Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
namespace Representation.SymplecticFourOrthogonalCover.ParabolicFixed
variable {F : Type*} [Field F] [Finite F] [CharP F 2]


private theorem local_displacement_snd_eq_zero (hF : Nat.card F = 4) (B : Subgroup (Sp F))
    (hB : B = pointLocal ∨ B = planeLocal)
    (b : Sp F) (hb : b ∈ B) (w : Space (K := F))
    (hw : ∀ q ∈ B.pCoreIn 2, fullAction q w = w) :
    (fullAction b w - w).2 = 0 := by
  have hc : correction b w.1 = 0 := by
    rcases hB with rfl | rfl
    · have hcore : (pointLocal (F := F)).pCoreIn 2 = pointRadicalAmbient := by
        unfold Subgroup.pCoreIn
        rw [pointLocal_core_eq (n := 2) hF (by decide)]
      have hv : w.1 ∈ point F := NaturalScalarCubic.point_radical_fixed w.1 (by
        intro q hq
        exact congrArg Prod.fst (hw q (hcore.symm ▸ hq)))
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hv
      apply SylowFlag.correction_eq_zero_of_fixed
      change b • w.1 = w.1
      rw [← hc]
      change toLinear b (c • e 0) = c • e 0
      rw [map_smul]
      exact congrArg (c • ·) ((mem_pointLocal_iff_fixed b).mp hb)
    · have hcore : (planeLocal (F := F)).pCoreIn 2 = planeRadicalAmbient := by
        unfold Subgroup.pCoreIn
        rw [planeLocal_core_eq (n := 2) hF (by decide)]
      have hv : w.1 ∈ plane F := NaturalScalarCubic.plane_radical_fixed w.1 (by
        intro q hq
        exact congrArg Prod.fst (hw q (hcore.symm ▸ hq)))
      have hbv : b • w.1 ∈ plane F :=
        (mem_stabilizer_iff (plane F) b).mp (planeLocal_le hb) w.1 hv
      have hq (v : Natural (K := F)) (hv : v ∈ plane F) : rowQuadratic v = 0 := by
        simp [rowQuadratic, hv 0, hv 1]
      have he := correction_square b w.1
      rw [← Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec] at he
      rw [hq w.1 hv, hq _ hbv, zero_add] at he
      exact (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp he.symm
  change w.2 + correction b w.1 - w.2 = 0
  simp [hc]

private theorem conjugate_action (g q : Sp F) (w : Space (K := F)) :
    fullAction ((MulAut.conj g) q) (fullAction g w) = fullAction g (fullAction q w) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  simp [MulAut.conj_apply, mul_assoc]

private theorem conjugate_local_displacement_snd_eq_zero (hF : Nat.card F = 4)
    (B : Subgroup (Sp F)) (g : Sp F)
    (hB : B.map (MulAut.conj g).toMonoidHom = pointLocal ∨
      B.map (MulAut.conj g).toMonoidHom = planeLocal)
    (b : Sp F) (hb : b ∈ B) (w : Space (K := F))
    (hw : ∀ q ∈ B.pCoreIn 2, fullAction q w = w) :
    (fullAction g (fullAction b w - w)).2 = 0 := by
  have hf : ∀ q ∈ (B.map (MulAut.conj g).toMonoidHom).pCoreIn 2,
      fullAction q (fullAction g w) = fullAction g w := by
    rw [← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
    rintro q ⟨r,hr,rfl⟩
    change fullAction ((MulAut.conj g) r) (fullAction g w) = fullAction g w
    rw [conjugate_action, hw r hr]
  have he := local_displacement_snd_eq_zero hF _ hB ((MulAut.conj g) b)
    (mem_map_of_mem (MulAut.conj g).toMonoidHom hb) (fullAction g w) hf
  rw [conjugate_action] at he
  simpa only [map_sub] using he


open Representation.BinaryOffender
variable [Algebra (ZMod 2) F]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) (L (K := F)) W}

/-- The fixed space of the literal residual core has no local commutators in
 the global fixed space, on every binary cover of the natural module. -/
theorem cover_core_fixed_commutator_disjoint (hF : Nat.card F = 4)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (B : Subgroup (L (K := F))) (g : Sp F)
    (hB : (B.map (commutator (Sp F)).subtype).map (MulAut.conj g).toMonoidHom = pointLocal ∨
      (B.map (commutator (Sp F)).subtype).map (MulAut.conj g).toMonoidHom = planeLocal) :
    Disjoint (subspaceCommutator σ (fixedSpace σ (B.pCoreIn 2)) B) (fixed σ) := by
  obtain ⟨f,hf,hpf⟩ := exists_cover_quotient p hp
  let D : Submodule (ZMod 2) (Space (K := F)) :=
    ((LinearMap.snd (ZMod 2) (Natural (K := F)) F).comp
      ((fullAction g).restrictScalars (ZMod 2))).ker
  have hmove : subspaceCommutator σ (fixedSpace σ (B.pCoreIn 2)) B ≤
      D.map f.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b,hb,w,hw,rfl⟩
    obtain ⟨x,rfl⟩ := hf w
    refine ⟨binaryAction b x-x,?_,?_⟩
    · change (fullAction g (fullAction b.val x-x)).2=0
      apply conjugate_local_displacement_snd_eq_zero hF
        (B.map (commutator (Sp F)).subtype) g hB b.val
        (mem_map_of_mem _ hb) x
      rw [← map_pCoreIn_of_injective 2 _ _ (commutator (Sp F)).subtype_injective]
      rintro q ⟨r,hr,rfl⟩
      have he : binaryNatural r (binaryProjection x) = binaryProjection x := by
        have hrfix : σ r (f x) = f x := hw ⟨r,hr⟩
        rw [← hpf x, ← p.isIntertwining, hrfix]
      exact cover_fixed_of_projection_fixed binaryProjection binaryProjection_isCover r x he
    · change f (binaryAction b x-x) = σ b (f x)-f x
      rw [map_sub, f.isIntertwining]
  apply Disjoint.mono_left hmove
  rw [Submodule.disjoint_def]
  rintro w ⟨x,hx,rfl⟩ hw
  have hfst : x.1 = 0 := by
    have he : p (f x) = 0 := (cover_fixed_kernel p hp).le hw
    exact (hpf x).symm.trans he
  have hsnd : x.2 = 0 := by
    have he : (fullAction g x).2 = 0 := hx
    simpa only [fullAction_apply, hfst, map_zero, add_zero] using he
  have hx0 : x = 0 := Prod.ext hfst hsnd
  simp only [hx0, map_zero]

/-- Application to a fully moved subspace fixed by the literal local core. -/
theorem cover_moved_subspace_disjoint (hF : Nat.card F = 4)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (B : Subgroup (L (K := F))) (g : Sp F)
    (hB : (B.map (commutator (Sp F)).subtype).map (MulAut.conj g).toMonoidHom = pointLocal ∨
      (B.map (commutator (Sp F)).subtype).map (MulAut.conj g).toMonoidHom = planeLocal)
    (A : Submodule (ZMod 2) W) (hA : A ≤ fixedSpace σ (B.pCoreIn 2))
    (hm : subspaceCommutator σ A B = A) : Disjoint A (fixed σ) := by
  have hle : A ≤ subspaceCommutator σ (fixedSpace σ (B.pCoreIn 2)) B := by
    rw [← hm]
    apply Submodule.span_mono
    rintro _ ⟨b,hb,w,hw,rfl⟩
    exact ⟨b,hb,w,hA hw,rfl⟩
  exact (cover_core_fixed_commutator_disjoint hF p hp B g hB).mono_left hle


/-- The central point in a fully moved core-fixed subspace must be zero. -/
theorem cover_fixed_eq_zero_of_moved_subspace (hF : Nat.card F = 4)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (B : Subgroup (L (K := F))) (g : Sp F)
    (hB : (B.map (commutator (Sp F)).subtype).map (MulAut.conj g).toMonoidHom = pointLocal ∨
      (B.map (commutator (Sp F)).subtype).map (MulAut.conj g).toMonoidHom = planeLocal)
    (A : Submodule (ZMod 2) W) (hA : A ≤ fixedSpace σ (B.pCoreIn 2))
    (hm : subspaceCommutator σ A B = A)
    (v : W) (hv : v ∈ A) (hfixed : v ∈ fixed σ) : v = 0 :=
  Submodule.disjoint_def.mp (cover_moved_subspace_disjoint hF p hp B g hB A hA hm)
    v hv hfixed

end Representation.SymplecticFourOrthogonalCover.ParabolicFixed
