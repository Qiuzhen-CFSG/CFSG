module

public import Theory.GroupAction.Quotient

/-!
# Homomorphisms between fixed subgroups

An equivariant homomorphism restricts to the literal fixed subgroups. For a
surjection with kernel of order prime to p, a p-group actor has a fixed
point in each fiber over a fixed point: each such fiber is a kernel coset.
Thus the restricted map is onto, without solvability of the ambient group.

The quotient specialization retains the original quotient map and the induced
action. Source: GLS II, Lemma 4.2(i), used in Proposition 5.19(iii).
-/

@[expose] public section
open Subgroup
namespace FixedPoints

variable {A G H : Type*} [Group A] [Group G] [Group H]
    [MulDistribMulAction A G] [MulDistribMulAction A H]

/-- Restriction of an equivariant homomorphism to the fixed subgroups. -/
def mapHom (f : G →* H) (he : ∀ (a : A) (x : G), f (a • x) = a • f x) :
    fixedPointSubgroup A G →* fixedPointSubgroup A H :=
  (f.comp (fixedPointSubgroup A G).subtype).codRestrict _ (fun x a => by
    change a • f (x : G) = f (x : G)
    rw [← he, x.property a])

/-- A p-group fixes a representative in each kernel coset of coprime order. -/
theorem mapHom_surjective_of_coprime_kernel [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : IsPGroup p A)
    (f : G →* H) (hf : Function.Surjective f)
    (he : ∀ (a : A) (x : G), f (a • x) = a • f x)
    (hk : ¬ p ∣ Nat.card f.ker) : Function.Surjective (mapHom f he) := by
  intro y
  obtain ⟨g, hg⟩ := hf y
  let T := {x : G // f x = (y : H)}
  let e : f.ker ≃ T := {
    toFun k := ⟨g * k, by rw [map_mul, MonoidHom.mem_ker.mp k.property, mul_one, hg]⟩
    invFun x := ⟨g⁻¹ * x, by
      rw [MonoidHom.mem_ker, map_mul, map_inv, x.property, hg, inv_mul_cancel]⟩
    left_inv k := Subtype.ext (by simp)
    right_inv x := Subtype.ext (by simp) }
  let : MulAction A T := {
    smul a x := ⟨a • (x : G), by rw [he, x.property, y.property a]⟩
    one_smul x := Subtype.ext (one_smul A (x : G))
    mul_smul a b x := Subtype.ext (mul_smul a b (x : G)) }
  have hT : ¬ p ∣ Nat.card T := by rwa [← Nat.card_congr e]
  obtain ⟨x, hx⟩ := hp.nonempty_fixed_point_of_prime_not_dvd_card T hT
  exact ⟨⟨x, fun a => congrArg Subtype.val (hx a)⟩, Subtype.ext x.property⟩

/-- The kernel is the intersection of the original kernel with the fixed subgroup. -/
theorem mapHom_ker (f : G →* H) (he : ∀ (a : A) (x : G), f (a • x) = a • f x) :
    (mapHom f he).ker = f.ker.comap (fixedPointSubgroup A G).subtype := by
  ext x
  exact Subtype.ext_iff

/-- Restricting to fixed subgroups cannot enlarge the kernel order. -/
theorem mapHom_ker_card_dvd (f : G →* H)
    (he : ∀ (a : A) (x : G), f (a • x) = a • f x) :
    Nat.card (mapHom f he).ker ∣ Nat.card f.ker := by
  rw [mapHom_ker]
  exact f.ker.card_comap_dvd_of_injective _ (fixedPointSubgroup A G).subtype_injective

/-- The original quotient map restricted to the fixed subgroups, using the induced action. -/
noncomputable def quotientMap (N : Subgroup G) [N.Normal] (hN : IsInvariant A G N) :
    letI : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
    fixedPointSubgroup A G →* fixedPointSubgroup A (G ⧸ N) := by
  letI : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
  exact mapHom (QuotientGroup.mk' N) (fun _ _ => rfl)

/-- The restriction has the original quotient map's value on every element. -/
theorem quotientMap_apply (N : Subgroup G) [N.Normal] (hN : IsInvariant A G N)
    (x : fixedPointSubgroup A G) :
    (quotientMap N hN x : G ⧸ N) = QuotientGroup.mk' N (x : G) := rfl
end FixedPoints
