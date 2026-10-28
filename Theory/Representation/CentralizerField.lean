module

public import Theory.Representation.RepEnd
public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Linear centralizers and finite endomorphism fields

The centralizer in GL(V) of the actual image of a representation is
canonically the unit group of its intertwining endomorphism ring. For an
irreducible representation over a finite field, Schur's lemma makes that
ring a domain, and the finite division-ring theorem makes it a field.
In characteristic two its unit group is cyclic of odd order.

The field structure extends the existing endomorphism-ring operations;
it is not a separate field with an unproved identification.

Source: Schur's lemma and Wedderburn's little theorem; the application is
Aschbacher–Smith, *The Classification of Quasithin Groups*, A.1.41,
printed p.31 (1 March 2004 manuscript).
-/

@[expose] public section

open Representation
namespace Representation.CentralizerField
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- The actual image of the group in the general linear group. -/
abbrev actionImage : Subgroup (Module.End k V)ˣ := ρ.asGroupHom.range
/-- The linear centralizer of the actual action image. -/
abbrev linearCentralizer : Subgroup (Module.End k V)ˣ :=
  Subgroup.centralizer (actionImage ρ : Set (Module.End k V)ˣ)

/-- Centralizer membership is exactly equivariance of the underlying linear map. -/
theorem mem_linearCentralizer_iff (c : (Module.End k V)ˣ) :
    c ∈ linearCentralizer ρ ↔ ∀ g v, c.val (ρ g v) = ρ g (c.val v) := by
  constructor
  · intro hc g v
    have h := Subgroup.mem_centralizer_iff.mp hc (ρ.asGroupHom g) ⟨g, rfl⟩
    exact (congrArg (fun u : (Module.End k V)ˣ => u.val v) h).symm
  · intro hc
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨g, rfl⟩
    apply Units.ext
    apply LinearMap.ext
    intro v
    exact (hc g v).symm

/-- A centralizing linear automorphism, regarded as an intertwining map. -/
def centralizerIntertwiner (c : linearCentralizer ρ) : IntertwiningMap ρ ρ where
  toLinearMap := c.val.val
  isIntertwining' g := LinearMap.ext fun v =>
    (mem_linearCentralizer_iff ρ c.val).mp c.property g v

/-- The linear centralizer is canonically the units of the actual endomorphism ring. -/
def centralizerUnitsEquiv : linearCentralizer ρ ≃* (IntertwiningMap ρ ρ)ˣ where
  toFun c :=
    { val := centralizerIntertwiner ρ c
      inv := centralizerIntertwiner ρ c⁻¹
      val_inv := by
        apply IntertwiningMap.toLinearMap_injective ρ ρ
        exact c.val.val_inv
      inv_val := by
        apply IntertwiningMap.toLinearMap_injective ρ ρ
        exact c.val.inv_val }
  invFun u := ⟨
    { val := u.val.toLinearMap
      inv := (↑u⁻¹ : IntertwiningMap ρ ρ).toLinearMap
      val_inv := congrArg IntertwiningMap.toLinearMap u.val_inv
      inv_val := congrArg IntertwiningMap.toLinearMap u.inv_val },
    (mem_linearCentralizer_iff ρ _).mpr (u.val.isIntertwining)⟩
  left_inv c := by apply Subtype.ext; apply Units.ext; rfl
  right_inv u := by apply Units.ext; apply IntertwiningMap.toLinearMap_injective ρ ρ; rfl
  map_mul' c d := by apply Units.ext; apply IntertwiningMap.toLinearMap_injective ρ ρ; rfl

/-- Finite dimension over a finite field makes the endomorphism ring finite. -/
theorem end_finite [Finite k] [FiniteDimensional k V] : Finite (IntertwiningMap ρ ρ) :=
  Module.finite_of_finite k

variable [IsIrreducible ρ]

/-- Schur: the actual endomorphism ring of an irreducible representation is a domain. -/
theorem end_isDomain : IsDomain (IntertwiningMap ρ ρ) := by
  classical
  exact Function.Injective.isDomain (IntertwiningMap.equivAlgEnd ρ).toRingEquiv
    (IntertwiningMap.equivAlgEnd ρ).injective

/-- Schur and Wedderburn: the actual finite endomorphism ring is a field. -/
theorem end_isField [Finite k] [FiniteDimensional k V] : IsField (IntertwiningMap ρ ρ) := by
  let := end_isDomain ρ
  let := end_finite ρ
  exact Finite.isDomain_to_isField _

/-- The field structure on the original endomorphism ring, with its original operations. -/
@[instance_reducible] noncomputable def endField [Finite k] [FiniteDimensional k V] :
    Field (IntertwiningMap ρ ρ) :=
  (end_isField ρ).toField

/-- The endomorphism ring inherits the characteristic of the ground field. -/
theorem end_charP (p : ℕ) [CharP k p] : CharP (IntertwiningMap ρ ρ) p := by
  let := end_isDomain ρ
  exact charP_of_injective_algebraMap (algebraMap k (IntertwiningMap ρ ρ)).injective p

/-- The units of the finite endomorphism field form a cyclic group. -/
theorem units_isCyclic [Finite k] [FiniteDimensional k V] : IsCyclic (IntertwiningMap ρ ρ)ˣ := by
  let := endField ρ
  let := end_finite ρ
  infer_instance

/-- In characteristic two, the endomorphism field has an odd number of units. -/
theorem units_odd_card [Finite k] [FiniteDimensional k V] [CharP k 2] :
    Odd (Nat.card (IntertwiningMap ρ ρ)ˣ) := by
  let := endField ρ
  let := end_finite ρ
  let := end_charP ρ 2
  let := Fintype.ofFinite (IntertwiningMap ρ ρ)
  obtain ⟨n, _, hn⟩ := FiniteField.card (K := IntertwiningMap ρ ρ) 2
  rw [Nat.card_units, Nat.card_eq_fintype_card, hn]
  have he : Even (2 ^ (n : ℕ)) := even_two.pow_of_ne_zero n.ne_zero
  exact Nat.Even.sub_odd Nat.one_le_two_pow he odd_one

end Representation.CentralizerField
