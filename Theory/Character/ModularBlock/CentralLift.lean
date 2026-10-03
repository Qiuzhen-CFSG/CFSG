module

public import Theory.Character.ModularBlock.IdempotentTrace

/-!
# Lifting central group-algebra elements

For a finite group and a surjective map of commutative coefficient rings,
every central element of the target group algebra lifts to a central element
of the source group algebra. Choose one coefficient lift for each conjugacy
class, then make it constant across the class. This avoids division by class
sizes and imposes no characteristic, locality, or idempotence hypotheses.
The result supplies central lifts in the modular block reduction argument.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/CentralLift.lean` (revision `c3503435`).
-/

public section

noncomputable section

namespace ModularBlock

namespace CentralLift

universe u v w

attribute [local instance] Fintype.ofFinite

/- A coefficientwise lift of a central element along a surjective coefficient
   map.  Choosing one coefficient per conjugacy class avoids any averaging or
   division by class sizes. -/
theorem exists_monoidAlgebra_lift_mem_center
    {R : Type u} {S : Type v} {G : Type w}
    [CommRing R] [CommRing S] [Group G] [Finite G]
    (q : R →+* S) (hq : Function.Surjective q)
    (f : MonoidAlgebra S G) (hf : f ∈ Set.center (MonoidAlgebra S G)) :
    ∃ x : MonoidAlgebra R G,
      x ∈ Set.center (MonoidAlgebra R G) ∧
        MonoidAlgebra.mapRingHom G q x = f := by
  classical
  let lift : S → R := fun s => Classical.choose (hq s)
  have lift_spec (s : S) : q (lift s) = s :=
    Classical.choose_spec (hq s)
  let representative : ConjClasses G → G := fun c =>
    Classical.choose (ConjClasses.exists_rep c)
  have representative_spec (c : ConjClasses G) :
      ConjClasses.mk (representative c) = c :=
    Classical.choose_spec (ConjClasses.exists_rep c)
  let coeff : G → R := fun g => lift (f.coeff (representative (ConjClasses.mk g)))
  let x : MonoidAlgebra R G := MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm coeff)
  have x_apply (g : G) : x.coeff g = coeff g := rfl
  have x_class_constant {a b : G}
      (hab : ConjClasses.mk a = ConjClasses.mk b) : x.coeff a = x.coeff b := by
    rw [x_apply, x_apply]
    simp only [coeff, hab]
  have hxcenter : x ∈ Set.center (MonoidAlgebra R G) := by
    apply (Semigroup.mem_center_iff).2
    intro a
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add y z hy hz => simp [add_mul, mul_add, hy, hz]
    | single g r =>
        ext h
        simp only [MonoidAlgebra.coeff_single_mul_apply,
          MonoidAlgebra.coeff_mul_single_apply]
        have hconj :
            ConjClasses.mk (g⁻¹ * h) = ConjClasses.mk (h * g⁻¹) := by
          rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
          exact ⟨g, by group⟩
        rw [x_class_constant hconj, mul_comm]
  refine ⟨x, hxcenter, ?_⟩
  ext g
  rw [MonoidAlgebra.coeff_mapRingHom, x_apply, lift_spec]
  have hconj : IsConj g (representative (ConjClasses.mk g)) := by
    rw [← ConjClasses.mk_eq_mk_iff_isConj]
    exact (representative_spec (ConjClasses.mk g)).symm
  rcases isConj_iff.mp hconj with ⟨h, hh⟩
  exact (congrArg (fun g : G => f.coeff g) hh).symm.trans
    (CentralIdempotentSupport.coeff_conj_eq_of_mem_center
      (f : MonoidAlgebra S G) hf h g)

end CentralLift

end ModularBlock


