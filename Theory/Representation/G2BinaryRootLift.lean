module
public import Theory.ElementaryAbelian.TwoConjugateNormalizer
public import Theory.Representation.G2BinaryPointOffenders

/-!
# Unique elementary lifts of the binary G₂ root eight

The long-root involution fixes exactly the same natural three-space as the
root eight. Thus it detects the full fixed subgroup in an elementary kernel
consisting of a natural module and a central factor. The elementary-lift
lemma then identifies any two self-centralizing elementary lifts with that
image. The actual component--Baumann core uses this in CoreConjugates.

Source: Aschbacher--Smith B.4.6(6), B.2.21, and 13.3.10(2), pp.82--83,888.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Atlas.G2.Natural.BinaryPointFlag
variable {G : Type*} [Group G]

/-- The long-root involution detects the fixed subgroup of the root eight
in every equivariant copy of the natural module. -/
theorem rootC_fixed_detector
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ g v, E (Additive.ofMul (MulAut.conjNormal g v)) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (q g) (E (Additive.ofMul v)))
    (A : Subgroup G) (hi : A.map q = Atlas.G2.BinaryCore.elementary)
    (a : G) (ha : a ∈ A) (hqa : q a = Atlas.G2.rootC (1 : F)) :
    V ⊓ centralizer (A : Set G) = V ⊓ centralizer ({a} : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr ha))
  · rintro v ⟨hv,hva⟩
    let w : V := ⟨v,hv⟩
    have hact : MulAut.conjNormal a w = w := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hva a (Set.mem_singleton a))
    have hf := he a w
    rw [hact,hqa] at hf
    have hw : E (Additive.ofMul w) ∈ seed := by
      rw [mem_seed]
      exact (Atlas.G2.NaturalOffenders.fixed_rootC_iff (1 : F) one_ne_zero _).mp hf.symm
    refine ⟨hv,?_⟩
    intro b hb
    have hqb : q b ∈ Atlas.G2.BinaryCore.elementary := hi ▸ mem_map_of_mem q hb
    have hfix := (Atlas.G2.Natural.BinaryPointOffenders.fixes_seed_iff (q b)).mpr hqb _ hw
    have heq := E.injective ((he b w).trans hfix)
    have hc : b * v * b⁻¹ = v :=
      congrArg (fun z : Additive V => (z.toMul : G)) heq
    exact mul_inv_eq_iff_eq_mul.mp hc

/-- The root-eight image has a unique self-centralizing elementary lift
over an elementary natural module times a central factor. -/
theorem root_eight_lift_unique
    (V Q C A B : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 Q] [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (q : G →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ g v, E (Additive.ofMul (MulAut.conjNormal g v)) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (q g) (E (Additive.ofMul v)))
    (hk : q.ker = Q) (hprod : Q = V ⊔ C) (hC : C ≤ center G)
    (hA : centralizer (A : Set G) ≤ A) (hB : centralizer (B : Set G) ≤ B)
    (hiA : A.map q = Atlas.G2.BinaryCore.elementary)
    (hiB : B.map q = Atlas.G2.BinaryCore.elementary) : B = A := by
  have hr : Atlas.G2.rootC (1 : F) ∈ A.map q := by
    rw [hiA,Atlas.G2.Natural.BinaryModelOffenders.elementary_eq]
    exact Atlas.G2.NaturalOffenders.rootC_mem_elementary 1
  obtain ⟨a,ha,hqa⟩ := hr
  apply elementary_lift_eq_of_self_centralizing Q A B q hk hA hB
    (hiA.trans hiB.symm) a ha
  rw [hprod]
  exact central_factor_fixed_detector V C A hC a ha
    (rootC_fixed_detector V q E he A hiA a ha hqa)
end Atlas.G2.Natural.BinaryPointFlag
