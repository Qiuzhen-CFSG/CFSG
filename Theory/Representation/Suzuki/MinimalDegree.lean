module

public import Theory.Representation.Suzuki.BinaryDegree
public import Theory.Representation.SubspaceQuotient
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import BenderSuzuki.MatrixGroups.SuzukiZero
public import Theory.Representation.BinaryFourQuintic

/-!
# Irreducibility in the smallest faithful Suzuki degree

Write q = 2^(2m+1). The existing faithful degree bound is 4(2m+1).
For m > 0, simplicity makes every nontrivial representation faithful.
In that degree a proper nonzero invariant subspace and its quotient must
both have trivial actions. The resulting action is abelian, contradicting
faithfulness and nonsolvability. Thus every nontrivial binary module of
order at most q⁴ is irreducible of order q⁴, without a semisimplicity
assumption. For m = 0, faithfulness and the order-five subgroup give the
same conclusion in dimension four.

This supplies the small-module step in DGS85, *Groups and Graphs*, Part II,
(12.6), p.183, and the two irreducible layers of (12.9)(c2), p.186.
The degree bound uses the primitive-prime-divisor argument in BinaryDegree.
The nonbinary formulation needs only a nontrivial action; the binary one
retains faithfulness because a nontrivial Sz(2) action can factor through C₄.
-/

public noncomputable section
open Subgroup Representation
open BenderSuzuki.MatrixGroups
namespace Representation.Suzuki

private theorem faithful_of_nontrivial {m : ℕ} (hm : 1 ≤ m)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V) (hne : ρ ≠ 1) :
    Function.Injective ρ := by
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
  exact ρ.ker_eq_bot_iff.mp (ρ.normal_ker.eq_bot_or_eq_top.resolve_right
    (fun hk => hne (MonoidHom.ker_eq_top_iff.mp hk)))

private theorem trivial_of_small_degree {m : ℕ} (hm : 1 ≤ m)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V)
    (hsmall : Module.finrank (ZMod 2) V < 4 * (2 * m + 1)) : ρ = 1 := by
  by_contra hne
  exact (not_lt_of_ge (Representation.Suzuki.finrank_ge hm ρ
    (faithful_of_nontrivial hm ρ hne))) hsmall

/-- A nontrivial nonbinary Suzuki action of degree at most 4 log₂(q) is irreducible and has that degree. -/
theorem irreducible_of_small_degree {m : ℕ} (hm : 1 ≤ m)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V) (hne : ρ ≠ 1)
    (hsmall : Module.finrank (ZMod 2) V ≤ 4 * (2 * m + 1)) :
    ρ.IsIrreducible ∧ Module.finrank (ZMod 2) V = 4 * (2 * m + 1) := by
  have hf := faithful_of_nontrivial hm ρ hne
  have hd := le_antisymm hsmall (Representation.Suzuki.finrank_ge hm ρ hf)
  have : Nontrivial V := by
    by_contra! hs
    let : Subsingleton V := hs
    exact hne (by ext g v; exact Subsingleton.elim _ _)
  refine ⟨⟨?_⟩, hd⟩
  intro W
  by_contra! hw
  have hb : W.toSubmodule ≠ ⊥ := fun h => hw.1 (Subrepresentation.toSubmodule_injective h)
  have ht : W.toSubmodule ≠ ⊤ := fun h => hw.2 (Subrepresentation.toSubmodule_injective h)
  have hp : 0 < Module.finrank (ZMod 2) W.toSubmodule :=
    Nat.pos_of_ne_zero (fun hz => hb (Submodule.finrank_eq_zero.mp hz))
  have hlt := Submodule.finrank_lt ht
  have hsum := Submodule.finrank_quotient_add_finrank W.toSubmodule
  have hW : W.toRepresentation = 1 :=
    trivial_of_small_degree hm W.toRepresentation (by omega)
  have hQ : W.quotientRepresentation = 1 :=
    trivial_of_small_degree hm W.quotientRepresentation (by omega)
  have hfix (g : SuzukiMatrixGroup m) (v : V) (hv : v ∈ W) : ρ g v = v :=
    congrArg Subtype.val (DFunLike.congr_fun (DFunLike.congr_fun hW g) (⟨v, hv⟩ : W))
  have hdiff (g : SuzukiMatrixGroup m) (v : V) : ρ g v - v ∈ W := by
    apply (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp
    change W.toSubmodule.mkQ (ρ g v - v) = 0
    rw [map_sub, ← W.quotientRepresentation_mk]
    exact sub_eq_zero.mpr
      (DFunLike.congr_fun (DFunLike.congr_fun hQ g) (W.toSubmodule.mkQ v))
  apply BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m (by omega)
  apply Group.isSolvable_of_comm
  intro g k
  apply hf
  rw [map_mul, map_mul]
  ext v
  have hg := hfix g (ρ k v - v) (hdiff k v)
  have hk := hfix k (ρ g v - v) (hdiff g v)
  simp only [map_sub] at hg hk
  change ρ g (ρ k v) = ρ k (ρ g v)
  rw [sub_eq_iff_eq_add] at hg hk
  rw [hg, hk]
  abel

/-- A nontrivial nonbinary Suzuki module of order at most q⁴ is irreducible of order q⁴. -/
theorem irreducible_of_small_card {m : ℕ} (hm : 1 ≤ m)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V) (hne : ρ ≠ 1)
    (hsmall : Nat.card V ≤ (2 ^ (2 * m + 1)) ^ 4) :
    ρ.IsIrreducible ∧ Nat.card V = (2 ^ (2 * m + 1)) ^ 4 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
  rw [Nat.card_zmod] at hc
  have hd : Module.finrank (ZMod 2) V ≤ 4 * (2 * m + 1) := by
    rw [hc, ← pow_mul, Nat.mul_comm (2 * m + 1) 4] at hsmall
    exact (Nat.pow_le_pow_iff_right (by decide)).mp hsmall
  obtain ⟨hi, he⟩ := irreducible_of_small_degree hm ρ hne hd
  refine ⟨hi, ?_⟩
  rw [hc, he, ← pow_mul, Nat.mul_comm (2 * m + 1) 4]

/-- The faithful formulation also includes Sz(2), using its subgroup of order five. -/
theorem irreducible_of_faithful_small_card {m : ℕ}
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V) (hf : Function.Injective ρ)
    (hsmall : Nat.card V ≤ (2 ^ (2 * m + 1)) ^ 4) :
    ρ.IsIrreducible ∧ Nat.card V = (2 ^ (2 * m + 1)) ^ 4 := by
  by_cases hm : m = 0
  · subst m
    have h5 : 5 ∣ Nat.card (SuzukiMatrixGroup 0) := by rw [suzukiZero_card]; decide
    have hlow := Representation.BinaryPrimeDegree.orderOf_le_finrank ρ hf
      (by decide : Nat.Prime 5) (by decide : 5 ≠ 2) h5
    rw [Representation.BinaryPrimeDegree.orderOf_two_mod_five] at hlow
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [Nat.card_zmod] at hc
    have hdim : Module.finrank (ZMod 2) V = 4 := by
      have hu : 2 ^ Module.finrank (ZMod 2) V ≤ 2 ^ 4 := by simpa [hc] using hsmall
      have hd := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hu
      omega
    refine ⟨Representation.binary_four_irreducible_of_five_dvd ρ hf hdim h5, ?_⟩
    simp [hc, hdim]
  · have hm' : 1 ≤ m := by omega
    have hn : ρ ≠ 1 := by
      intro he
      let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
      obtain ⟨g, hg⟩ := exists_ne (1 : SuzukiMatrixGroup m)
      exact hg (hf (by simp only [he, MonoidHom.one_apply]))
    exact irreducible_of_small_card hm' ρ hn hsmall

end Representation.Suzuki
