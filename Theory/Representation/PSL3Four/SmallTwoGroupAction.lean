module
public import Theory.Representation.PSL3Four.SmallDegree
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section
public import Theory.GroupAction.PerfectFrattiniAction
public import Theory.Representation.FrattiniAction

/-!
# Small two-groups fixed by perfect PSL₃(4) sections

A nontrivial action of a perfect group has a nontrivial irreducible binary
section. Its two-core acts trivially on that section, so an actual PSL₃(4)
two-core quotient forces degree at least nine. A nontrivial action on a
two-group survives on its Frattini quotient; consequently a two-group of
order below 512 admits only the trivial action of this perfect actor.

The quotient marking is the full two-core quotient, not its central
quotient. The original representation and the entire two-group are retained.
Source: the PSL₃(4) tensor-word degree classification cited in SmallDegree,
and Burnside's Frattini automorphism-kernel theorem.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
namespace Representation.PSL3Four
variable {H F V : Type*} [Group H] [Finite H] [Group.IsPerfect H]
  [Field F] [Finite F]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Nontrivial perfect actions retain the degree-nine bound through the two-core. -/
theorem perfect_core_quotient_finrank_ge_nine
    (e : (H ⧸ pCore 2 H) ≃* PSL(3,F)) (hF : Nat.card F = 4)
    (ρ : Representation (ZMod 2) H V) (hnt : ∃ h, ρ h ≠ 1) :
    9 ≤ Module.finrank (ZMod 2) V := by
  let : Group.IsPerfect (⊤ : Subgroup H) := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := H)).symm.toMonoidHom) (topEquiv (G := H)).symm.surjective
  have hne : ¬ (⊤ : Subgroup H) ≤ ρ.ker := by
    intro h
    obtain ⟨g,hg⟩ := hnt
    exact hg (h (mem_top g))
  obtain ⟨U,N,hi,hN⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect
    (ρ := ρ) (⊤ : Subgroup H) hne
  let := hi
  let σ := N.quotientRepresentation
  have hk : pCore 2 H ≤ σ.ker := normal_p_subgroup_le_ker σ _ pCore_isPGroup
  let τ := quotientOfLEKer σ (pCore 2 H) hk
  let : IsIrreducible τ := (quotientOfLEKer_irreducible_iff σ _ hk).mpr inferInstance
  have hntτ : ∃ g, τ g ≠ 1 := by
    by_contra! he
    apply hN
    intro g _
    change σ g = 1
    simpa only [τ,quotientOfLEKer_apply] using he (QuotientGroup.mk' (pCore 2 H) g)
  exact (finrank_ge_nine_of_equiv hF e τ hntτ).trans
    ((Submodule.finrank_quotient_le _).trans (Submodule.finrank_le U.toSubmodule))

variable {P : Type*} [Group P] [Finite P]

/-- The full action on a two-group of order below 512 is trivial. -/
theorem action_eq_one_of_card_lt_512
    (e : (H ⧸ pCore 2 H) ≃* PSL(3,F)) (hF : Nat.card F = 4)
    (hp : IsPGroup 2 P) (hcard : Nat.card P < 512)
    (a : H →* MulAut P) : a = 1 := by
  by_contra ha
  let : Fact (IsPGroup 2 P) := ⟨hp⟩
  let W := P ⧸ frattini P
  let : IsElementaryAbelian 2 W := isElementaryAbelian_quotient_frattini
  let b := (quotientAut (frattini P)).comp a
  have hbne : b ≠ 1 := a.frattini_comp_ne_one_of_isPerfect hp ha
  obtain ⟨x,hx⟩ : ∃ x, b x ≠ 1 := by
    by_contra! hh
    exact hbne (MonoidHom.ext hh)
  let ρ := FrattiniAction.ofAutomorphismHom b
  have hr : ∃ x, ρ x ≠ 1 := by
    by_contra! hh
    exact FrattiniAction.ofAutomorphismHom_ne_one b x hx (MonoidHom.ext hh)
  have hl := perfect_core_quotient_finrank_ge_nine (V := Additive W) e hF ρ hr
  have hw : Nat.card W = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
    change Nat.card (Additive W) = _
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W))
  have hlow : 512 ≤ Nat.card W := by
    rw [hw]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hl
  have hup : Nat.card W ≤ Nat.card P := Nat.card_le_card_of_surjective
    (QuotientGroup.mk' (frattini P)) (QuotientGroup.mk'_surjective _)
  omega
end Representation.PSL3Four
