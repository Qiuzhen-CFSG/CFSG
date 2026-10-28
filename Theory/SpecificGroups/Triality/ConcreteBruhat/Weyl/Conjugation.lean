module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.MatrixRealization
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.RootConjugation

/-!
# Conjugation by every concrete Weyl matrix

The simple-generator calculation on all canonical integral root curves extends
to the entire generated split Weyl subgroup. Intertwining is closed under
products and inverses, and the faithful matrix/root equivalence identifies the
resulting permutation with the literal D₄ root action. Both positive and negative
roots retain their parameter in characteristic two, including q = 2.

Source: the split Weyl conjugation ingredient of GLS3 2.3.8(b) and 2.4.8(e)
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace Triality.Standard.ConcreteBruhat
open Parabolics
noncomputable section

private lemma intertwine_of_generators {G H I J T : Type*} [Group G] [Group H]
    (f : H →* G) (e : H →* Equiv.Perm I) (x : I → T → G)
    (s : J → H) (hs : Subgroup.closure (Set.range s) = ⊤)
    (hx : ∀ j r t, f (s j) * x r t = x (e (s j) r) t * f (s j))
    (w : H) : ∀ r t, f w * x r t = x (e w r) t * f w := by
  have hw : w ∈ Subgroup.closure (Set.range s) := by rw [hs]; trivial
  induction hw using Subgroup.closure_induction with
  | mem w hw => obtain ⟨j, rfl⟩ := hw; exact hx j
  | one => simp
  | mul u v _ _ hu hv =>
    intro r t
    simp only [map_mul, Equiv.Perm.mul_apply]
    calc
      (f u * f v) * x r t = f u * (f v * x r t) := mul_assoc _ _ _
      _ = f u * (x (e v r) t * f v) := by rw [hv]
      _ = (f u * x (e v r) t) * f v := (mul_assoc _ _ _).symm
      _ = (x (e u (e v r)) t * f u) * f v := by rw [hu]
      _ = _ := mul_assoc _ _ _
  | inv u _ hu =>
    intro r t
    simp only [map_inv]
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
    have h := hu ((e u)⁻¹ r) t
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h.symm

private lemma subtype_generators_dense {G I : Type*} [Group G]
    (H : Subgroup G) (s : I → H)
    (h : Subgroup.closure (Set.range (fun i => (s i).val)) = H) :
    Subgroup.closure (Set.range s) = ⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    ← Set.range_comp]
  exact h

private lemma split_dense (P : Parameters) :
    Subgroup.closure (Set.range (splitWeylGenerator P)) = ⊤ := by
  apply subtype_generators_dense
  change Subgroup.closure (Set.range (fun i => weylWord P i 1)) =
    Subgroup.closure {g | ∃ i, g = weylWord P i 1}
  congr 1
  ext g
  exact exists_congr (fun _ => eq_comm)

/-- Every split Weyl matrix acts on every canonical integral root curve by its
literal root permutation, with unchanged parameter in characteristic two. -/
theorem splitWeyl_rootCurveUnit_conjugation (P : Parameters) (hp : P.prime = 2)
    (w : splitWeylSubgroup P) (r : TypeDRootIndex 4) (t : ExtensionField P) :
    w.val.val *
        rootCurveUnit (integralChevalleyRootOperators (b := typeDRootPairing_base 2)) r t *
        w.val.val⁻¹ =
      rootCurveUnit (integralChevalleyRootOperators (b := typeDRootPairing_base 2))
        ((splitWeylEquiv P hp w).val r) t := by
  have h := intertwine_of_generators
    ((SplitGroup P).subtype.comp (splitWeylSubgroup P).subtype)
    (rootWeylGroup.subtype.comp (splitWeylEquiv P hp).toMonoidHom)
    (fun r (t : ExtensionField P) =>
      rootCurveUnit (integralChevalleyRootOperators (b := typeDRootPairing_base 2)) r t)
    (splitWeylGenerator P) (split_dense P) (fun i r t => by
      change (weylWord P i 1).val * _ =
        rootCurveUnit _ ((splitWeylEquiv P hp (splitWeylGenerator P i)).val r) t * _
      exact (RootConjugation.weylWord_rootCurveUnit_intertwine P hp i r t).trans
        (congrArg (fun v : rootWeylGroup =>
          rootCurveUnit (integralChevalleyRootOperators (b := typeDRootPairing_base 2))
            (v.val r) t * (weylWord P i 1).val)
          (splitWeylEquiv_generator P hp i)).symm) w r t
  exact (mul_inv_eq_iff_eq_mul).mpr h
end
end Triality.Standard.ConcreteBruhat
