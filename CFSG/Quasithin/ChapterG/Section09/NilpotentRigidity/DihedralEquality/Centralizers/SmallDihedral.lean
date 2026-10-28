module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.Centralizers.Linear
public import Theory.GroupTheory.OddInvolutionEndpointModels

/-!
# Centralizers of the two minimal dihedral modules

For a faithful binary S₃-module of dimension two or D₁₀-module of dimension
four, the A.1.44 splitting and the rotation orbit congruence show that the
rotation has no nonzero fixed vector. Hence every nonzero invariant
subspace has faithful dihedral action. The one-factor degree bounds force
that subspace to have the full dimension. In particular a commuting
involution is the identity.

The splitting theorem remains an explicit input; neither an equality
classification nor a centralizer conclusion is assumed. These are the
small dihedral cases used in Aschbacher--Smith G.9.2, printed pp.351--353.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality

open DihedralDegree DihedralGroup

universe v

variable {G : Type*} [Group G] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

private theorem single_injective {p : ℕ} {M : Type*} [Monoid M]
    (hp : p.Prime) (ho : Odd p) (f : DihedralGroup p →* M)
    (hr : f (r 1) ≠ 1) : Function.Injective f := by
  let e := MulEquiv.piUnique (fun _ : Unit => DihedralGroup p)
  have hf := injective_of_rotations_ne_one (ι := Unit) (p := fun _ => p)
    (fun _ => hp) (fun _ => ho) (f.comp e.toMonoidHom) (fun i => by simpa [e] using hr)
  intro x y h
  have he : e.symm x = e.symm y := hf (by simpa using h)
  exact e.symm.injective he

theorem small_dihedral_rotation_fixed_free [FiniteDimensional (ZMod 2) W]
    (split : DihedralSplittingTheorem.{v}) {p : ℕ} (hp : p = 3 ∨ p = 5)
    (σ : Representation (ZMod 2) (DihedralGroup p) W) (hf : Function.Injective σ)
    (hd : Module.finrank (ZMod 2) W = p-1) :
    ∀ w, σ (r 1) w = w → w = 0 := by
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  have hodd : Odd p := by rcases hp with rfl | rfl <;> decide
  obtain ⟨hW, hM, hpos⟩ := split_dimensions σ split hprime hodd hf
  have hmod := rotationMoved_card_modEq σ hprime (split W p hprime hodd σ hf).1.disjoint
  rw [hM] at hmod
  have hC : rotationFixed σ = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    rcases hp with rfl | rfl
    · omega
    · have hn : Module.finrank (ZMod 2) (reflectionHalf σ) ≠ 1 := by
        intro he
        rw [he] at hmod
        norm_num at hmod
      omega
  intro w hw
  have hh := (mem_rotationFixed σ w).mpr hw
  rwa [hC, Submodule.mem_bot] at hh

theorem small_dihedral_involution_centralizer [FiniteDimensional (ZMod 2) W]
    (split : DihedralSplittingTheorem.{v}) {p : ℕ} (hp : p = 3 ∨ p = 5)
    (σ : Representation (ZMod 2) (DihedralGroup p) W) (hf : Function.Injective σ)
    (hd : Module.finrank (ZMod 2) W = p-1)
    (t : Module.End (ZMod 2) W) (ht : t*t=1) (hc : ∀ g, Commute t (σ g)) : t=1 := by
  apply involution_eq_one_of_subspace_bound σ _ t ht hc
  intro U hU hstable
  let τ := σ.subrepresentation U hstable
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  have hodd : Odd p := by rcases hp with rfl | rfl <;> decide
  have hτ : Function.Injective τ := by
    apply single_injective hprime hodd
    intro he
    apply hU
    apply bot_unique
    intro w hw
    change w = 0
    apply small_dihedral_rotation_fixed_free split hp σ hf hd
    exact congrArg Subtype.val (congrArg (fun f : Module.End (ZMod 2) U => f ⟨w, hw⟩) he)
  obtain ⟨hb, hne, _⟩ := single_factor_bounds τ split hprime hodd hτ
  rcases hp with rfl | rfl
  · omega
  · have := hne (by decide)
    omega

theorem dihedral_model_involution_centralizer [FiniteDimensional (ZMod 2) W]
    (split : DihedralSplittingTheorem.{v}) {p : ℕ} (hp : p = 3 ∨ p = 5)
    (σ : Representation (ZMod 2) G W) (hf : Function.Injective σ)
    (e : G ≃* DihedralGroup p) (hd : Module.finrank (ZMod 2) W = p-1)
    (t : Module.End (ZMod 2) W) (ht : t*t=1) (hc : ∀ g, Commute t (σ g)) : t=1 :=
  small_dihedral_involution_centralizer split hp (σ.comp e.symm.toMonoidHom)
    (hf.comp e.symm.injective) hd t ht (fun g => hc (e.symm g))

theorem symmetricThree_involution_centralizer [FiniteDimensional (ZMod 2) W]
    (split : DihedralSplittingTheorem.{v})
    (σ : Representation (ZMod 2) G W) (hf : Function.Injective σ)
    (e : G ≃* Equiv.Perm (Fin 3)) (hd : Module.finrank (ZMod 2) W = 2)
    (t : Module.End (ZMod 2) W) (ht : t*t=1) (hc : ∀ g, Commute t (σ g)) : t=1 := by
  obtain ⟨E⟩ := Theory.GroupTheory.nonempty_dihedralThreeEquivPerm
  exact dihedral_model_involution_centralizer split (Or.inl rfl) σ hf
    (e.trans E.symm) hd t ht hc

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality
