module
public import Theory.Representation.G2.NaturalScalarCubic

/-!
# Arbitrary-prime natural scalars for the two G₂ local subgroups

The short and long local radicals have explicit fixed spaces in the natural
six-dimensional module. Diagonal torus elements act there by a field scalar
or its square. In characteristic two both move every nonzero fixed vector
when the parameter is nonidentity. Their commutators lie in the actual local
two-core, and Cauchy supplies every prime dividing the field-unit order.

Source: Aschbacher--Smith, 10.2.9, printed p.751. The proof extends the cubic
calculation to the prime selected by the original component's outer order.
-/

@[expose] public section
open Subgroup Atlas.G2 Atlas.G2.Explicit Atlas.G2.LieParabolicSetup
open scoped commutatorElement MatrixGroups
namespace Atlas.G2.NaturalScalars
open NaturalScalarCubic
variable {F : Type*} [Field F] [CharP F 2]
omit [CharP F 2] in
private def scalarTorus (n : ℕ) : Fˣ →* Model F :=
  torusHom.comp ((powMonoidHom n).prod (MonoidHom.id _))

omit [CharP F 2] in
private theorem scalarTorus_apply (n : ℕ) (s : Fˣ) : scalarTorus (F := F) n s = torus (s ^ n) s := rfl

omit [CharP F 2] in
private theorem scalarTorus_injective (n : ℕ) : Function.Injective (scalarTorus (F := F) n) := by
  intro s t h
  exact congrArg Prod.snd (torusHom_injective h)

private theorem scalar_moves {s : Fˣ} (hs : s ≠ 1) {v : Natural.Space F} (hv : v ≠ 0)
    {x : Model F} (ha : Natural.action F x v = (s : F) • v) :
    Natural.action F x v ≠ v := by
  intro he
  have hz : ((s : F) - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← ha, he, sub_self]
  exact hs (Units.ext (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hv)))

variable [Finite F]

/-- A prime-order scalar centralizes the short local section and moves any specified nonzero
natural vector fixed by its actual two-core. -/
theorem short_prime_moves_fixed {p : ℕ} [Fact p.Prime] (hp : p ∣ Nat.card F - 1)
    (v : Natural.Space F) (hv : v ≠ 0)
    (hfix : ∀ q ∈ (local₁ (F := F)).pCoreIn 2, Natural.action F q v = v) :
    ∃ x : Model F, orderOf x = p ∧ x ∈ normalizer (local₁ (F := F) : Set (Model F)) ∧
      (∀ (b : Model F) (_ : b ∈ local₁), ⁅x,b⁆ ∈ local₁.pCoreIn 2) ∧ Natural.action F x v ≠ v := by
  have hcore : (local₁ (F := F)).pCoreIn 2 = radical₁ := local₁_pCore
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by
    simpa only [Nat.card_units] using hp)
  have hne : s ≠ 1 := by
    intro he
    rw [he,orderOf_one] at hs
    exact (Fact.out : p.Prime).ne_one hs.symm
  refine ⟨torus s s, ?_, torus_normalizes_local₁ ⟨(s,s),rfl⟩, ?_, ?_⟩
  · have ho := (orderOf_injective (scalarTorus 1) (scalarTorus_injective 1) s).trans hs
    simpa only [scalarTorus_apply, pow_one] using ho
  · rw [hcore]
    exact short_commutators s
  · exact scalar_moves (x := torus s s) hne hv
      (short_scalar_action s v (by rwa [hcore] at hfix))

/-- A prime-order scalar centralizes the long local section and moves any specified nonzero
natural vector fixed by its actual two-core. -/
theorem long_prime_moves_fixed {p : ℕ} [Fact p.Prime] (hp : p ∣ Nat.card F - 1)
    (v : Natural.Space F) (hv : v ≠ 0)
    (hfix : ∀ q ∈ (local₂ (F := F)).pCoreIn 2, Natural.action F q v = v) :
    ∃ x : Model F, orderOf x = p ∧ x ∈ normalizer (local₂ (F := F) : Set (Model F)) ∧
      (∀ (b : Model F) (_ : b ∈ local₂), ⁅x,b⁆ ∈ local₂.pCoreIn 2) ∧ Natural.action F x v ≠ v := by
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by
    simpa only [Nat.card_units] using hp)
  have hne : s ≠ 1 := by
    intro he
    rw [he,orderOf_one] at hs
    exact (Fact.out : p.Prime).ne_one hs.symm
  refine ⟨torus (s^2) s, ?_,
    borel_le_normalizer_local₂ (mem_sup_right ⟨(s^2,s),rfl⟩), ?_, ?_⟩
  · exact (orderOf_injective (scalarTorus 2) (scalarTorus_injective 2) s).trans hs
  · rw [local₂_pCoreIn]
    exact long_commutators s
  · exact scalar_moves (x := torus (s^2) s) (by
        intro he
        apply hne
        apply Units.ext
        apply CharTwo.sq_injective
        simpa only [Units.val_pow_eq_pow_val,Units.val_one,pow_two,Units.val_mul,one_mul] using
          congrArg (fun u : Fˣ => (u : F)) he) hv
      (long_scalar_action s v (by rwa [local₂_pCoreIn] at hfix))

end Atlas.G2.NaturalScalars
