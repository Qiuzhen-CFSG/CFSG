module

public import CFSG.Quasithin.ChapterA.Section02.OddAutomorphisms
public import Theory.GroupTheory.PrimePowerCosetReplacement
public import Theory.SpecificGroups.SL2.Affine.NoncentralCore
public import Theory.SpecificGroups.Triality.OddGraphCosetReduction

/-!
# Verified reductions and source obstructions for A.2.6

Sources: Aschbacher–Smith, Notation A.2.5 and Corollary A.2.6,
printed pp.33–34 of `refs/quasithin.pdf`; GLS98 2.5.12 and 2.5.13,
`refs/KGroup/GLS3/chapter2.tex`, especially 2.5.13(c).

The source displays L/Z(L), whereas its proof works with L/O₂,Z(L).
Even when Z(L/O₂(L)) = 1, the natural projection is injective exactly
when O₂(L) is central. The imported affine calculation shows that this
extra condition fails for actual groups whose two-core quotient is SL₂(F).
No identification of these quotients is made here.

There is also a distinction between replacing an element inside its coset
and taking a power first. A coset contains a three-element exactly when its
image has three-power order. The imported prime Frobenius of ³D₄(32) has
outer order 15, so its coset modulo inner automorphisms contains no such
element. This refutes that intermediate assertion from odd automorphism
order and the model list alone; its ambient automorphism group is not
asserted to satisfy the SQTK hypotheses of the full corollary.

The power reduction below preserves failure of membership in a specified
automorphism subgroup when its quotient is a three-group. Multiplication
by an element of L also preserves that failure if the subgroup contains
the actual inner automorphisms. The concrete q-Frobenius graph representative
has order three and is outer, and is applied to the literal quotient action.
These are conditional reductions. Exhaustive inner-diagonal/field coverage,
ambient realization of the graph representative, and the interpretation of
the displayed quotient remain required for the source corollary.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section02.OddGraphReduction
open Subgroup

variable {G : Type*} [Group G]

/-- The exact missing condition for the displayed quotient after the source's
centerlessness conclusion has been established. -/
theorem source_projection_injective_iff (L : Type*) [Group L]
    (hc : center (L ⧸ pCore 2 L) = ⊥) :
    Function.Injective (centralQuotientProjection (pCore 2 L)) ↔
      pCore 2 L ≤ center L :=
  centralQuotientProjection_injective_iff_of_center_quotient_eq_bot _ hc

/-- The affine two-core quotient is genuinely SL₂(F), while the proposed
central-quotient identification fails. This includes F₄. -/
theorem affine_quotient_obstruction (F : Type*) [Field F] [Finite F] [CharP F 2] :
    Nonempty ((Matrix.SL2.Affine F ⧸ pCore 2 (Matrix.SL2.Affine F)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F) ∧
    ¬ Function.Injective (centralQuotientProjection (pCore 2 (Matrix.SL2.Affine F))) :=
  ⟨⟨Matrix.SL2.affineCoreQuotientEquiv F⟩,
    Matrix.SL2.affine_centralQuotientProjection_not_injective F⟩

/-- The source's replacement inside xL needs three-power order in G/L. -/
theorem source_coset_has_three_element_iff [Finite G]
    (L : Subgroup G) [L.Normal] (x : G) :
    (∃ y : G, QuotientGroup.mk' L y = QuotientGroup.mk' L x ∧
      ∃ a : ℕ, y ^ (3 ^ a) = 1) ↔
    ∃ b : ℕ, (QuotientGroup.mk' L x) ^ (3 ^ b) = 1 :=
  Theory.GroupTheory.exists_prime_power_coset_iff 3 (by decide) L x

/-- Right multiplication by an element of L preserves membership in any actual
automorphism subgroup containing the inner automorphisms. -/
theorem factorization_iff_mul_subgroup (L : Subgroup G) [L.Normal]
    (D : Subgroup (MulAut (L ⧸ twoCoreCenter L)))
    (hinner : MulAut.innerSubgroup (L ⧸ twoCoreCenter L) ≤ D)
    (x : G) (l : L) :
    normalQuotientAction L (twoCoreCenter L) (x * l) ∈ D ↔
      normalQuotientAction L (twoCoreCenter L) x ∈ D := by
  rw [map_mul, normalQuotientAction_inner]
  exact D.mul_mem_cancel_right (hinner ⟨_, rfl⟩)

/-- Taking the three-primary power preserves failure of the desired factorization
when the actual automorphism quotient is a three-group. The replacement stays
inside the original cyclic subgroup; it need not stay inside the original L-coset. -/
theorem three_power_preserves_failure [Finite G]
    (L : Subgroup G) [L.Normal]
    (D : Subgroup (MulAut (L ⧸ twoCoreCenter L))) [D.Normal]
    (hD : IsPGroup 3 ((MulAut (L ⧸ twoCoreCenter L)) ⧸ D))
    (x : G) (hx : normalQuotientAction L (twoCoreCenter L) x ∉ D) :
    ∃ k m : ℕ, Nat.Coprime 3 m ∧ orderOf (x ^ m) = 3 ^ k ∧
      normalQuotientAction L (twoCoreCenter L) (x ^ m) ∉ D := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact Theory.GroupTheory.exists_primary_power_outside 3 D hD
    (normalQuotientAction L (twoCoreCenter L)) x hx

/-- Apply the concrete q-Frobenius graph representative to the original quotient
action. The three-prime action-kernel hypothesis is precisely the separate
centralizer step in the source proof. -/
theorem triality_representative_order_and_outside [Finite G]
    (L : Subgroup G) [L.Normal] (n : ℕ) (hn : 0 < n)
    (e : L ⧸ twoCoreCenter L ≃* Triality.Standard.BinaryCarrier n hn)
    (x : G) (hxp : ∃ k : ℕ, x ^ (3 ^ k) = 1)
    (ha : normalQuotientAction L (twoCoreCenter L) x =
      MulAut.congr e.symm (Triality.Standard.OddGraphReduction.graphThree n hn))
    (hk : ¬ 3 ∣ Nat.card (normalQuotientAction L (twoCoreCenter L)).ker) :
    orderOf x = 3 ∧ x ∉ L := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  constructor
  · apply MonoidHom.orderOf_eq_prime_of_primePower_of_kernel
      (normalQuotientAction L (twoCoreCenter L)) hk x hxp
    rw [ha]
    exact Triality.Standard.OddGraphReduction.transported_graphThree_order n hn e.symm
  · apply not_mem_of_normalQuotientAction_outer L (twoCoreCenter L) x
    rw [ha]
    exact Triality.Standard.OddGraphReduction.transported_graphThree_not_inner n hn e.symm

end CFSG.Quasithin.ChapterA.Section02.OddGraphReduction
