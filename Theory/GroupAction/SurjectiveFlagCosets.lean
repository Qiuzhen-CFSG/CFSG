module

public import Theory.GroupAction.TypedCosetGeometry.Residues.Quotient
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Flag coordinates through literal surjective quotient maps

A surjection sending a subgroup onto a point stabilizer identifies the
original cosets with the transitive point orbit. With two such subgroups,
flag transitivity identifies common coset representatives with the given
incidence relation. The formulas retain the original homomorphism and
representatives, allowing source residue actions to be transported exactly.
-/

@[expose] public noncomputable section
namespace MulAction
open Subgroup
variable {H K X Y : Type*} [Group H] [Group K]
variable [MulAction K X] [IsPretransitive K X]

def surjectiveCosetEquiv (P : Subgroup H) (f : H →* K)
    (hf : Function.Surjective f) (hk : f.ker ≤ P) (x : X)
    (hP : P.map f = stabilizer K x) : (H ⧸ P) ≃ X :=
  (CosetGeometry.QuotientTransport.cosetEquiv P f hf hk).trans
    ((quotientEquivOfEq hP).trans
      (Equiv.ofBijective (ofQuotientStabilizer K x)
        ⟨injective_ofQuotientStabilizer K x, fun y => by
          obtain ⟨g, hg⟩ := exists_smul_eq K x y
          exact ⟨(g : K ⧸ stabilizer K x), hg⟩⟩))

theorem surjectiveCosetEquiv_mk (P : Subgroup H) (f : H →* K)
    (hf : Function.Surjective f) (hk : f.ker ≤ P) (x : X)
    (hP : P.map f = stabilizer K x) (a : H) :
    surjectiveCosetEquiv P f hf hk x hP (a : H ⧸ P) = f a • x := rfl

theorem surjectiveCosetEquiv_smul (P : Subgroup H) (f : H →* K)
    (hf : Function.Surjective f) (hk : f.ker ≤ P) (x : X)
    (hP : P.map f = stabilizer K x) (a : H) (q : H ⧸ P) :
    surjectiveCosetEquiv P f hf hk x hP (a • q) =
      f a • surjectiveCosetEquiv P f hf hk x hP q := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
  change f (a * b) • x = f a • (f b • x)
  rw [map_mul, mul_smul]

variable [MulAction K Y] [IsPretransitive K Y]

theorem surjectiveCosetEquiv_incident (P L : Subgroup H) (f : H →* K)
    (hf : Function.Surjective f) (hkP : f.ker ≤ P) (hkL : f.ker ≤ L)
    (x : X) (y : Y) (hP : P.map f = stabilizer K x) (hL : L.map f = stabilizer K y)
    (R : X → Y → Prop) (hxy : R x y)
    (hact : ∀ (g : K) u v, R (g • u) (g • v) ↔ R u v)
    (hflag : ∀ u v, R u v → ∃ g : K, g • x = u ∧ g • y = v)
    (q : H ⧸ P) (r : H ⧸ L) :
    (∃ a : H, (a : H ⧸ P) = q ∧ (a : H ⧸ L) = r) ↔
      R (surjectiveCosetEquiv P f hf hkP x hP q)
        (surjectiveCosetEquiv L f hf hkL y hL r) := by
  constructor
  · rintro ⟨a, rfl, rfl⟩
    exact (hact (f a) x y).mpr hxy
  · intro h
    obtain ⟨g, hg, hg'⟩ := hflag _ _ h
    obtain ⟨a, rfl⟩ := hf g
    exact ⟨a, (surjectiveCosetEquiv P f hf hkP x hP).injective hg,
      (surjectiveCosetEquiv L f hf hkL y hL).injective hg'⟩

end MulAction
