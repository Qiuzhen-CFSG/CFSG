module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.SL2Quadratic
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ComponentTensor.Refinement
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.QuadraticExclusion
/-!
# Normalizer-invariant quadratic form for a binary PSL₂ socle

An absolutely irreducible degree-four binary PSL₂ subgroup preserves a
quadratic refinement of the original symplectic form. Uniqueness of the
invariant refinement makes every element of its actual symplectic normalizer
preserve the same form. Thus the literal moving opposite pair cannot
normalize such a subgroup. This is the orthogonal-model exclusion in
Aschbacher--Smith G.4.1, printed p.342, applied to E.2.7.
-/

public section
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open Subgroup Matrix
variable {F K : Type*} [Field F] [CharP F 2] [Field K] [Finite K] [CharP K 2]

theorem exists_normalizer_quadratic_of_psl2_subgroup (N : Subgroup (Sp F))
    (ha : Representation.IsAbsolutelyIrreducible
      ((Representation.symplecticNatural 2).comp N.subtype))
    (e : N≃*Theory.PSL2.Group K) (f : ℕ) (hcard : Nat.card K=2^f) :
    ∃ Q : QuadraticForm F (Vector F), Q.polarBilin=form F ∧
      ∀g∈normalizer (N:Set (Sp F)),∀v,Q (g•v)=Q v := by
  obtain ⟨Q,hpolar,hQ⟩ := exists_quadratic_of_psl2_subgroup N ha e f hcard
  let ρ : Representation F N (Vector F) := (Representation.symplecticNatural 2).comp N.subtype
  let : ρ.IsAbsolutelyIrreducible := ha
  let : ρ.IsIrreducible :=
    Representation.IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible ρ
  let w : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩
  have hw : w≠1 := by
    intro he
    have hh := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) K=>x.val 0 0) he
    exact zero_ne_one hh
  let q := Theory.PSL2.sl2QuotientEquiv K
  let z : N := e.symm (q w)
  have hz : z≠1 := by
    intro he
    apply hw
    apply q.injective
    simpa only [z,MulEquiv.apply_symm_apply,map_one] using congrArg e he
  have hnon : ∃g v,ρ g v≠v := by
    by_contra! hh
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    have h := congrArg (fun v : Vector F=>v i) (hh z (Pi.single j 1))
    change ((z:Sp F).val *ᵥ (Pi.single j 1 : Vector F)) i=(Pi.single j 1 : Vector F) i at h
    simpa [Matrix.one_apply,Pi.single_apply,eq_comm] using h
  refine ⟨Q,hpolar,?_⟩
  intro g hg
  apply Representation.QuadraticRefinement.normalizer_preserves ρ hnon Q hQ
    (N.normalizerMonoidHom ⟨g,hg⟩) (toLinear g)
  · intro n v
    change g•((n:Sp F)•v)=(g*(n:Sp F)*g⁻¹)•(g•v)
    simp only [mul_smul,inv_smul_smul]
  · intro v w
    rw [hpolar]
    exact preserves_form g v w

open TwoConjugate DiagramAutomorphisms EvenBorelTorus

theorem moving_pair_excludes_psl2_socle [Finite F] (hq:2<Nat.card F)
    (a:ActorReduction.stabilizer (F:=F)) (ha:¬PreservesDiagram a.val)
    (V:Subgroup (Sp F)) (hV:V.map a.val.toMonoidHom=V)
    (hcent:V≤(CentralRootGeometry.parameter (F:=F)).range) (hr:2<Nat.card V)
    (N:Subgroup (Sp F))
    (hi:Representation.IsAbsolutelyIrreducible ((Representation.symplecticNatural 2).comp N.subtype))
    (hN:oppositePair V≤normalizer (N:Set (Sp F)))
    (e:N≃*Theory.PSL2.Group K) (f:ℕ) (hcard:Nat.card K=2^f) : False := by
  obtain ⟨Q,hQ,hQI⟩ := exists_normalizer_quadratic_of_psl2_subgroup N hi e f hcard
  exact oppositePair_not_preserves_quadratic_of_moving_actor hq a ha V hV hcent hr Q hQ
    (fun g hg=>hQI g (hN hg))
end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
