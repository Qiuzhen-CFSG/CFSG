module

public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary

/-!
# Coordinate root groups in the actual projective quotient

The elementary matrices give injectively parametrized root groups in
SL₃(F)/Z(SL₃(F)). Their three-index relation survives this quotient, and
Gaussian elimination shows that homomorphisms are determined on these groups.
Over a prime field, the value on xᵢⱼ(1) determines the entire root action.
No lift of a projective automorphism is used.

These are coordinate inputs for the odd-prime case of GLS3, Theorem 2.5.12(a),
and the matrix description in §2.7, `refs/KGroup/GLS3/chapter2.tex`,
lines 1111–1115. Arbitrary-automorphism normalization is a separate obligation.
-/

@[expose] public section

open scoped MatrixGroups commutatorElement
open Matrix
namespace Matrix.PSL3.OuterSolvable.OddPrimeCoverage
variable {F : Type*} [Field F]

def rootElement {i j : Fin 3} (hij : i ≠ j) (a : F) : PSL(3,F) :=
  QuotientGroup.mk (SpecialLinearGroup.transvection hij a)

@[simp] theorem rootElement_zero {i j : Fin 3} (hij : i ≠ j) :
    rootElement hij (0 : F) = 1 := by
  simp [rootElement]

theorem rootElement_add {i j : Fin 3} (hij : i ≠ j) (a b : F) :
    rootElement hij (a + b) = rootElement hij a * rootElement hij b := by
  simp only [rootElement, SpecialLinearGroup.transvection_add, QuotientGroup.mk_mul]

theorem rootElement_eq_one_iff {i j : Fin 3} (hij : i ≠ j) (a : F) :
    rootElement hij a = 1 ↔ a = 0 := by
  exact (QuotientGroup.eq_one_iff _).trans
    (SpecialLinearGroup.transvection_mem_center_iff hij a)

def rootHom {i j : Fin 3} (hij : i ≠ j) : Multiplicative F →* PSL(3,F) where
  toFun a := rootElement hij a.toAdd
  map_one' := rootElement_zero hij
  map_mul' a b := rootElement_add hij a.toAdd b.toAdd

theorem rootElement_injective {i j : Fin 3} (hij : i ≠ j) :
    Function.Injective (rootElement (F := F) hij) := by
  have h : Function.Injective (rootHom (F := F) hij) := by
    apply (injective_iff_map_eq_one (rootHom (F := F) hij)).mpr
    intro a ha
    exact (rootElement_eq_one_iff hij a.toAdd).mp ha
  exact h

def rootGroup {i j : Fin 3} (hij : i ≠ j) : Subgroup PSL(3,F) :=
  (rootHom (F := F) hij).range

theorem rootElement_mem {i j : Fin 3} (hij : i ≠ j) (a : F) :
    rootElement hij a ∈ rootGroup hij := ⟨Multiplicative.ofAdd a, rfl⟩

theorem rootElement_chain {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : F) :
    rootElement hij a * rootElement hjk b =
      rootElement hjk b * rootElement hik (a * b) * rootElement hij a := by
  simpa only [rootElement, QuotientGroup.mk_mul] using congrArg
    (QuotientGroup.mk : SL(3,F) → PSL(3,F))
    (Representation.OneCohomology.SLHigherNatural.transvection_chain hij hjk hik a b)

theorem hom_ext {G : Type*} [Group G] (f g : PSL(3,F) →* G)
    (h : ∀ (i j : Fin 3) (hij : i ≠ j) a, f (rootElement hij a) = g (rootElement hij a)) :
    f = g := by
  apply MonoidHom.ext
  intro x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) x
  apply Representation.OneCohomology.SLHigherNatural.transvection_induction
    (fun x : SL(3,F) => f (QuotientGroup.mk x) = g (QuotientGroup.mk x)) h
    (fun x y hx hy => by simp only [QuotientGroup.mk_mul, map_mul, hx, hy]) x

theorem exists_natCast [Finite F] {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p) (a : F) :
    ∃ n : ℕ, (n : F) = a := by
  let :=  Fintype.ofFinite F
  let : NeZero p := ⟨hp.ne_zero⟩
  let e := ZMod.ringEquivOfPrime F hp (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective x
  exact ⟨n, (map_natCast e n).symm⟩

theorem rootElement_natCast {i j : Fin 3} (hij : i ≠ j) (n : ℕ) :
    rootElement hij (n : F) = rootElement hij (1 : F) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, rootElement_add, ih, pow_succ]

theorem rootElement_natCast_mul {i j : Fin 3} (hij : i ≠ j) (n : ℕ) (c : F) :
    rootElement hij ((n : F) * c) = rootElement hij c ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, rootElement_add, ih, pow_succ]

theorem map_rootElement_of_one [Finite F] {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p)
    (α : MulAut PSL(3,F)) {i j : Fin 3} (hij : i ≠ j) (c : F)
    (hc : α (rootElement hij 1) = rootElement hij c) (a : F) :
    α (rootElement hij a) = rootElement hij (a * c) := by
  obtain ⟨n, rfl⟩ := exists_natCast hp hF a
  rw [rootElement_natCast, map_pow, hc, rootElement_natCast_mul]

end Matrix.PSL3.OuterSolvable.OddPrimeCoverage
