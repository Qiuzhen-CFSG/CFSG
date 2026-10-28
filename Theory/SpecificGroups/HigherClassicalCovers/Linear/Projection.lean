module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# The literal degree-four linear covering and its scalar kernel

Elementary transvections are commutators and generate SL₄. The projective
transvection action proves simplicity of PSL₄, so the actual scalar quotient
is a covering of finite quasisimple groups. Its kernel is the cyclic group of
fourth roots of unity: it is C₂ over a three-element field and C₄ over a field
of Fermat prime order greater than three.

These are the lower bounds for Aschbacher–Smith I.1.4(1),(3), printed p.408.
Universality additionally requires upper bounds for arbitrary perfect central
coverings. It is not a consequence of this scalar calculation. The elementary
generation, simplicity and center count reuse the attributed ATLAS port.
-/

@[expose] public section

namespace Theory.SpecificGroups.HigherClassicalCovers.Linear

open Theory.GroupTheory
open scoped MatrixGroups

variable (F : Type*) [Field F]

instance sl4_isQuasisimple : IsQuasisimple SL(4, F) where
  toIsPerfect := Atlas.sl_perfect 4 (by decide)
  simple := Atlas.psl_simple_high_rank 4 (by decide)

instance psl4_isQuasisimple : IsQuasisimple PSL(4, F) where
  toIsPerfect := Atlas.psl_perfect 4 (by decide)
  simple := by
    let : IsSimpleGroup PSL(4, F) := Atlas.psl_simple_high_rank 4 (by decide)
    have hz : Subgroup.center PSL(4, F) = ⊥ :=
      Group.IsPerfect.center_quotient_center_eq_bot SL(4, F)
    exact ((QuotientGroup.quotientMulEquivOfEq hz).trans
      QuotientGroup.quotientBot).isSimpleGroup

/-- The actual central quotient, with the coefficient field retained. -/
def projection : SL(4, F) →* PSL(4, F) :=
  QuotientGroup.mk' (Subgroup.center SL(4, F))

theorem projection_surjective : Function.Surjective (projection F) :=
  QuotientGroup.mk'_surjective _

theorem projection_ker : (projection F).ker = Subgroup.center SL(4, F) :=
  QuotientGroup.ker_mk' _

/-- The actual kernel, as a multiplicative group of scalar parameters. -/
noncomputable def projectionKernelEquivRoots :
    (projection F).ker ≃* rootsOfUnity 4 F :=
  (MulEquiv.subgroupCongr (projection_ker F)).trans
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := F) (0 : Fin 4))

instance projectionKernel_isCyclic : IsCyclic (projection F).ker :=
  (projectionKernelEquivRoots F).isCyclic.mpr inferInstance

/-- Perfectness makes lifts through a central kernel unique. -/
theorem projection_lift_unique {E : Type*} [Group E]
    (f : E →* PSL(4, F)) (hc : f.ker ≤ Subgroup.center E)
    {s t : SL(4, F) →* E}
    (hs : f.comp s = projection F) (ht : f.comp t = projection F) : s = t :=
  PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq f hc s t (hs.trans ht.symm)

/-- Any compatible lift to a perfect central extension is surjective. -/
theorem projection_lift_surjective {E : Type*} [Group E] [Group.IsPerfect E]
    (f : E →* PSL(4, F)) (hc : f.ker ≤ Subgroup.center E)
    (s : SL(4, F) →* E) (hs : f.comp s = projection F) : Function.Surjective s :=
  PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    f s (hs ▸ projection_surjective F) hc

variable [Finite F]

/-- The literal scalar quotient, in the finite quasisimple covering API. -/
def projectionCovering : Covering SL(4, F) PSL(4, F) where
  toMonoidHom := projection F
  surjective := projection_surjective F

@[simp] theorem projectionCovering_toMonoidHom :
    (projectionCovering F).toMonoidHom = projection F := rfl

@[simp] theorem projectionCovering_apply (x : SL(4, F)) :
    projectionCovering F x = projection F x := rfl

theorem card_projectionKernel :
    Nat.card (projection F).ker = Nat.gcd 4 (Nat.card F - 1) := by
  rw [projection_ker]
  exact Atlas.ExceptionalSupport.card_sl_center

/-- The structure of the actual projection kernel, not merely its order. -/
noncomputable def projectionKernelEquivCyclic :
    (projection F).ker ≃* Multiplicative (ZMod (Nat.gcd 4 (Nat.card F - 1))) :=
  mulEquivOfCyclicCardEq (by
    change Nat.card (projection F).ker = Nat.card (ZMod (Nat.gcd 4 (Nat.card F - 1)))
    rw [card_projectionKernel, Nat.card_zmod])

theorem card_projectionKernel_three (hF : Nat.card F = 3) :
    Nat.card (projection F).ker = 2 := by
  rw [card_projectionKernel, hF]
  norm_num

noncomputable def projectionKernelEquivTwo (hF : Nat.card F = 3) :
    (projection F).ker ≃* Multiplicative (ZMod 2) :=
  mulEquivOfCyclicCardEq (by
    change Nat.card (projection F).ker = Nat.card (ZMod 2)
    rw [card_projectionKernel_three F hF, Nat.card_zmod])

theorem card_projectionKernel_four (hF : Nat.card F % 4 = 1) :
    Nat.card (projection F).ker = 4 := by
  rw [card_projectionKernel, Nat.gcd_eq_left_iff_dvd]
  exact Nat.dvd_of_mod_eq_zero (by omega)

noncomputable def projectionKernelEquivFour (hF : Nat.card F % 4 = 1) :
    (projection F).ker ≃* Multiplicative (ZMod 4) :=
  mulEquivOfCyclicCardEq (by
    change Nat.card (projection F).ker = Nat.card (ZMod 4)
    rw [card_projectionKernel_four F hF, Nat.card_zmod])

/-- Fermat numbers greater than three are one modulo four. This arithmetic
step does not require primality. -/
theorem fermat_mod_four {p : ℕ} (hp : 3 < p)
    (hfermat : ∃ m : ℕ, p = 2 ^ (2 ^ m) + 1) : p % 4 = 1 := by
  obtain ⟨m, rfl⟩ := hfermat
  have hm : m ≠ 0 := by
    intro hm
    subst m
    norm_num at hp
  have he : 2 ≤ 2 ^ m := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.one_le_iff_ne_zero.mpr hm)
  have hd : 4 ∣ 2 ^ (2 ^ m) := by
    exact (show (2 : ℕ) ^ 2 ∣ 2 ^ (2 ^ m) from pow_dvd_pow 2 he)
  omega

/-- Application to the exact Fermat parameter of source I.1.4(3). -/
noncomputable def projectionKernelEquivFour_of_fermat {p : ℕ}
    (hF : Nat.card F = p) (hp : 3 < p)
    (hfermat : ∃ m : ℕ, p = 2 ^ (2 ^ m) + 1) :
    (projectionCovering F).toMonoidHom.ker ≃* Multiplicative (ZMod 4) :=
  projectionKernelEquivFour F (hF ▸ fermat_mod_four hp hfermat)

end Theory.SpecificGroups.HigherClassicalCovers.Linear
