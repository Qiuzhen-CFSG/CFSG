import Submission.ZStar.CentralIdempotentSupport

noncomputable section

namespace Submission.ZStar

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
  let coeff : G → R := fun g => lift (f (representative (ConjClasses.mk g)))
  let x : MonoidAlgebra R G := Finsupp.equivFunOnFinite.symm coeff
  have x_apply (g : G) : x g = coeff g := rfl
  have x_class_constant {a b : G}
      (hab : ConjClasses.mk a = ConjClasses.mk b) : x a = x b := by
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
        simp only [MonoidAlgebra.single_mul_apply,
          MonoidAlgebra.mul_single_apply]
        have hconj :
            ConjClasses.mk (g⁻¹ * h) = ConjClasses.mk (h * g⁻¹) := by
          rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
          exact ⟨g, by group⟩
        rw [x_class_constant hconj, mul_comm]
  refine ⟨x, hxcenter, ?_⟩
  ext g
  rw [MonoidAlgebra.mapRingHom_apply, x_apply, lift_spec]
  have hconj : IsConj g (representative (ConjClasses.mk g)) := by
    rw [← ConjClasses.mk_eq_mk_iff_isConj]
    exact (representative_spec (ConjClasses.mk g)).symm
  rcases isConj_iff.mp hconj with ⟨h, hh⟩
  exact (congrArg (f : G → S) hh).symm.trans
    (CentralIdempotentSupport.coeff_conj_eq_of_mem_center
      (f : MonoidAlgebra S G) hf h g)

end CentralLift

end Submission.ZStar

