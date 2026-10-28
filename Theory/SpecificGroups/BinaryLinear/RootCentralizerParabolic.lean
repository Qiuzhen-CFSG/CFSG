module
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Transvections
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# A proper parabolic containing a binary root centralizer

For the transvection x ↦ x + f(x)w, the fixed space is ker(f).
Every commuting linear map preserves that space. Since w is nonzero,
f is nonzero, and f(w)=0, it is a nonzero proper subspace, whose
stabilizer is a proper geometric parabolic.

This proves the centralizer containment used for the PSL₄(2) and PSL₅(2)
root rows of Aschbacher–Smith, *The Classification of Quasithin Groups*,
16.1.4(1), printed p.1171. The chapter adapter retains the ambient embeddings
in the resulting equality O²(C_L(r)) = O²(C_P(r)).
-/

public section
namespace BinaryLinear.RootCentralizer
open Subgroup OuterCyclic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem transvection_fix_iff {w : V} {f : V →ₗ[ZMod 2] ZMod 2}
    (hw : w ≠ 0) (hfw : f w = 0) (v : V) :
    transvection w f hfw v = v ↔ f v = 0 := by
  change v + f v • w = v ↔ f v = 0
  rw [add_eq_left, smul_eq_zero]
  simp [hw]

/-- The centralizer of a nonidentity transvection stabilizes its fixed hyperplane. -/
theorem centralizer_le_parabolic_ker {w : V} {f : V →ₗ[ZMod 2] ZMod 2}
    (hw : w ≠ 0) (hfw : f w = 0) :
    (MulAut.conj (transvection w f hfw)).fixedSubgroup ≤ parabolic f.ker := by
  intro g hg v
  have hcomm : transvection w f hfw * g = g * transvection w f hfw := by
    exact mul_inv_eq_iff_eq_mul.mp ((MulAut.mem_fixedSubgroup _ _).mp hg)
  have hfix : transvection w f hfw (g v) = g (transvection w f hfw v) :=
    congrArg (fun a : BinaryLinear.GL V => a v) hcomm
  change f (g v) = 0 ↔ f v = 0
  rw [← transvection_fix_iff hw hfw, ← transvection_fix_iff hw hfw, hfix]
  exact g.injective.eq_iff

/-- A root involution has its full centralizer in a proper geometric parabolic. -/
theorem transvection_proper_parabolic {t : BinaryLinear.GL V} (ht : IsTransvection t) :
    ∃ W : Submodule (ZMod 2) V, W ≠ ⊥ ∧ W ≠ ⊤ ∧
      parabolic W ≠ ⊤ ∧ (MulAut.conj t).fixedSubgroup ≤ parabolic W := by
  obtain ⟨w, f, hw, hf, hfw, rfl⟩ := ht
  have hW0 : f.ker ≠ ⊥ := by
    intro h
    have hm : w ∈ f.ker := hfw
    rw [h, Submodule.mem_bot] at hm
    exact hw hm
  have hW1 : f.ker ≠ ⊤ := by
    intro h
    apply hf
    ext v
    exact (show v ∈ f.ker from h ▸ Submodule.mem_top)
  exact ⟨f.ker, hW0, hW1, FourParabolicAction.parabolic_ne_top hW0 hW1,
    centralizer_le_parabolic_ker hw hfw⟩

end BinaryLinear.RootCentralizer
