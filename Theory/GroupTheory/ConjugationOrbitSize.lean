module
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Conjugacy orbit sizes under a subgroup

Normalizer conjugation identifies the subgroup orbits. When a point's
full centralizer lies in the subgroup, orbit-stabilizer uses that same
full centralizer. These are the counting steps in Aschbacher--Smith
12.2.16, printed pp.799--800.
-/

public noncomputable section
namespace Subgroup
variable {G : Type*} [Group G]
/-- The actual conjugacy orbit under a specified subgroup. -/
@[expose] def conjugacyOrbit (A : Subgroup G) (x : G) : Set G :=
  Set.range fun a : A => (a : G) * x * (a : G)⁻¹

/-- Normalizing the actor preserves its conjugacy-orbit sizes. -/
theorem conjugacyOrbit_normalizer (A : Subgroup G) (x m : G)
    (hm : m ∈ normalizer (A : Set G)) :
    (conjugacyOrbit A (m * x * m⁻¹)).ncard = (conjugacyOrbit A x).ncard := by
  have hi : (MulAut.conj m) '' conjugacyOrbit A x =
      conjugacyOrbit A (m * x * m⁻¹) := by
    ext y
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      refine ⟨⟨m * a * m⁻¹,(hm a).mp a.property⟩,?_⟩
      simp [MulAut.conj_apply,mul_assoc]
    · rintro ⟨a,rfl⟩
      have ha : m⁻¹ * (a : G) * m ∈ A := by
        simpa using ((normalizer (A : Set G)).inv_mem hm a).mp a.property
      refine ⟨(m⁻¹ * (a : G) * m) * x * (m⁻¹ * (a : G) * m)⁻¹,
        ⟨⟨_,ha⟩,rfl⟩,?_⟩
      simp [MulAut.conj_apply,mul_assoc]
  rw [← hi,Set.ncard_image_of_injective _ (MulAut.conj m).injective]

/-- Orbit-stabilizer with the full centralizer contained in the actor. -/
theorem conjugacyOrbit_mul_centralizer [Finite G]
    (N : Subgroup G) (x : G) (hx : centralizer ({x} : Set G) ≤ N) :
    (conjugacyOrbit N x).ncard * Nat.card (centralizer ({x} : Set G)) = Nat.card N := by
  let : MulAction N G := MulAction.compHom G
    (ConjAct.toConjAct.toMonoidHom.comp N.subtype)
  have hs : MulAction.stabilizer N x = (centralizer ({x} : Set G)).subgroupOf N := by
    ext n
    change (n : G) * x * (n : G)⁻¹ = x ↔ (n : G) ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_singleton_iff,mul_inv_eq_iff_eq_mul]
  have ho : MulAction.orbit N x = conjugacyOrbit N x := rfl
  have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup N x)
  rw [Nat.card_prod,hs,ho, Nat.card_congr (subgroupOfEquivOfLe hx).toEquiv] at hh
  exact hh


end Subgroup
