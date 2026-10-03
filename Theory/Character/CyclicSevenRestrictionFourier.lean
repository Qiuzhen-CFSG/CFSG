module

public import Theory.Character.CyclicSevenExceptional

/-!
# Fourier coefficients of order-seven normalizer rows

Frobenius reciprocity identifies each local orbit coefficient with pairing
against induction to the ambient group. Ambient conjugacy makes the coefficients
constant on complement orbits. Exhaustion of the six nonprincipal linear
characters then gives a three-term Fourier formula for every ambient class function.

Source: Fong (1967), printed p.75, citing Brauer (1942).
Adapted from `Theory.Character.CyclicThirteenRestrictionFourier`,
whose source is Alperin--Brauer--Gorenstein, III.8, pp.116--117.
-/

public section

noncomputable section
open scoped BigOperators IsMulCommutative
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace CyclicSevenNormalizer
variable {G : Type*} [Group G] [Finite G] {P : Subgroup G}

private theorem reciprocity_right {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (f : G → ℂ)
    (hf : IsClassFunction f) (g : H → ℂ) :
    scalarProduct G f (inducedClassFunction H g) =
      scalarProduct H (fun x => f x) g := by
  rw [← scalarProduct_conj, scalarProduct_inducedClassFunction H g hf,
    scalarProduct_conj]

/-- A representative Fourier coefficient is a multiplicity against the induced local row. -/
theorem Rows.coefficient_induction (s : Rows P) (f : G → ℂ)
    (hf : IsClassFunction f) (i : Fin 3) :
    scalarProduct P (fun u => f u) (s.linear i) =
      scalarProduct G f (inducedClassFunction (Normalizer P) (s.localClass i)) := by
  rw [reciprocity_right _ _ hf]
  have he : s.localClass i = inducedClassFunction (core P)
      ((s.linear i).comp (coreEquiv P).toMonoidHom) := funext (s.induction i)
  rw [he]
  have hfN : IsClassFunction (fun x : Normalizer P => f x) :=
    isClassFunction_comp_hom (Normalizer P).subtype hf
  rw [reciprocity_right (core P) _ hfN]
  exact (scalarProduct_comp_mulEquiv (coreEquiv P) (fun u : P => f u)
    (s.linear i)).symm

private theorem Rows.restriction_invariant (s : Rows P) (f : G → ℂ)
    (hf : IsClassFunction f) (a : Two) (u : P) : f (s.action a u) = f u := by
  let e : P ⋊[s.action] Two →* G := (Normalizer P).subtype.comp s.splitting.toMonoidHom
  have he (v : P) : e (SemidirectProduct.inl v) = (v : G) :=
    congrArg Subtype.val (s.splitting_inl v)
  rw [← he, SemidirectProduct.inl_aut, map_mul, map_mul]
  simpa only [map_inv, he] using hf (e (SemidirectProduct.inl u))
    (e (SemidirectProduct.inr a))

private theorem Rows.coefficient_orbit (s : Rows P) (f : G → ℂ)
    (hf : IsClassFunction f) (i : Fin 3) (a : Two) :
    scalarProduct P (fun u => f u) ((s.linear i).comp (s.action a).toMonoidHom) =
      scalarProduct P (fun u => f u) (s.linear i) := by
  have he : (fun u : P => f (s.action a u)) = fun u : P => f u :=
    funext (s.restriction_invariant f hf a)
  simpa only [he, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_def] using
    scalarProduct_comp_mulEquiv (s.action a) (fun u : P => f u) (s.linear i)

/-- Fourier inversion for an ambient class function, grouped into the three local orbits. -/
theorem Rows.fourier_restriction (s : Rows P) (hP : Nat.card P = 7)
    (f : G → ℂ) (hf : IsClassFunction f) (u : P) :
    f u = scalarProduct P (fun v => f v) 1 +
      ∑ i : Fin 3, scalarProduct P (fun v => f v) (s.linear i) *
        s.chi i (ConjClasses.mk (inclusion P u)) := by
  classical
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hP
  let X := {ψ : P →* ℂ // ψ ≠ 1}
  have hn (q : Fin 3 × Two) : (s.linear q.1).comp (s.action q.2).toMonoidHom ≠ 1 := by
    intro hh
    apply s.linear_ne_one q.1
    ext x
    simpa using DFunLike.congr_fun hh ((s.action q.2).symm x)
  let e : Fin 3 × Two ≃ X := Equiv.ofBijective (fun q => ⟨_, hn q⟩) (by
    constructor
    · intro q r hh
      exact s.orbit_injective (congrArg Subtype.val hh)
    · intro ψ
      obtain ⟨i,a,ha⟩ := s.orbit_covers ψ.val ψ.property
      exact ⟨(i,a), Subtype.ext ha⟩)
  let F (ψ : P →* ℂ) := scalarProduct P (fun v => f v) ψ * ψ u
  have hs := Fintype.sum_subtype_add_sum_subtype (fun ψ : P →* ℂ => ψ ≠ 1) F
  have hone : (∑ ψ : {ψ : P →* ℂ // ¬ψ ≠ 1}, F ψ.val) =
      scalarProduct P (fun v => f v) 1 := by
    have he : (fun ψ : {ψ : P →* ℂ // ¬ψ ≠ 1} => F ψ.val) = fun _ => F 1 := by
      funext ψ
      rw [not_not.mp ψ.property]
    rw [he]
    simp [F]
    congr 1
  have hexp : f u = ∑ ψ, F ψ := by
    convert AbelianLinearCharacters.expansion (fun v : P => f v) u using 1
    apply Finset.sum_congr rfl
    intro ψ _
    dsimp [F]
    congr 1
    congr 1
    exact Subsingleton.elim _ _
  rw [hexp]
  rw [← hs, hone, add_comm]
  congr 1
  rw [← e.sum_comp (fun ψ : X => F ψ.val), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ a : Two, scalarProduct P (fun v => f v)
    ((s.linear i).comp (s.action a).toMonoidHom) * s.linear i (s.action a u)) = _
  simp_rw [s.coefficient_orbit f hf]
  rw [← Finset.mul_sum, s.restriction]

end CyclicSevenNormalizer
