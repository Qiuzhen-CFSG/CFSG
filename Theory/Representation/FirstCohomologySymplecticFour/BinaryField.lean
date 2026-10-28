module

public import Theory.Representation.FirstCohomologySymplecticFour.Quadratic
public import Theory.Representation.FirstCohomologySymplecticFour.BinaryField.Generation
public import Theory.Representation.FirstCohomologySymplecticFour.BinaryField.ValueConstraints

/-!
# Spanning the binary natural derived symplectic cocycles

Every cocycle of the natural module for the actual group `Sp₄(K)'`, when
`K` has two elements, is a scalar multiple of the quadratic-defect cocycle
plus a principal cocycle.

Over `ZMod 2`, the generator-value calculation supplies a normal form on three
commutators. The zero set of the difference cocycle is a subgroup, so the
proved generation theorem extends this equality to the whole derived group.
A field isomorphism transports symplectic matrices and their commutator
subgroups surjectively. The square formula for the quadratic-defect cocycle
shows that this same normal form transports to any field of cardinality two.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(5), printed p.408 (PDF p.419).
-/

open Matrix
namespace Representation.OneCohomology.SymplecticFour.BinaryField

private lemma eq_of_generator_values
    (f q : cocycles (symplecticDerivedNatural (k := ZMod 2) 2))
    (hv : ∀ j, f.val (generator j) = q.val (generator j)) : f = q := by
  let d := f - q
  have h1 : d.val 1 = 0 := by
    have h := d.property 1 1
    simpa using h.symm
  let H : Subgroup (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) :=
    { carrier := {g | d.val g = 0}
      one_mem' := h1
      mul_mem' := by
        intro g h hg hh
        change d.val (g * h) = 0
        rw [d.property, hg, hh, map_zero, add_zero]
      inv_mem' := by
        intro g hg
        change d.val g = 0 at hg
        change d.val g⁻¹ = 0
        have h := d.property g⁻¹ g
        simpa only [inv_mul_cancel, h1, hg, map_zero, zero_add] using h.symm }
  have hle : Subgroup.closure (Set.range generator) ≤ H := by
    apply (Subgroup.closure_le H).2
    rintro g ⟨j, rfl⟩
    change f.val (generator j) - q.val (generator j) = 0
    exact sub_eq_zero.mpr (hv j)
  rw [closure_range_generator] at hle
  apply sub_eq_zero.mp
  apply Subtype.ext
  funext g
  exact hle (Subgroup.mem_top g)

/-- Every natural cocycle for the actual binary derived symplectic group is a
quadratic-defect cocycle modulo a principal cocycle. -/
public theorem exists_normal_form_zmod_two (f : cocycles (symplecticDerivedNatural (k := ZMod 2) 2)) :
    ∃ (t : ZMod 2) (v : (Fin 2 ⊕ Fin 2) → ZMod 2),
      f = t • derivedQuadraticCocycle + principal (symplecticDerivedNatural 2) v := by
  obtain ⟨t, v, hv⟩ := exists_generator_values f
  exact ⟨t, v, eq_of_generator_values f _ hv⟩

variable {K : Type*} [Field K] (e : ZMod 2 ≃+* K)

private def fieldMap : Matrix.symplecticGroup (Fin 2) (ZMod 2) →*
    Matrix.symplecticGroup (Fin 2) K where
  toFun g := ⟨g.val.map e, SymplecticGroup.map_mem g.property e⟩
  map_one' := Subtype.ext (Matrix.map_one _ (map_zero _) (map_one _))
  map_mul' _ _ := Subtype.ext Matrix.map_mul

private lemma fieldMap_surjective : Function.Surjective (fieldMap e) := by
  intro g
  refine ⟨⟨g.val.map e.symm, SymplecticGroup.map_mem g.property e.symm⟩, ?_⟩
  apply Subtype.ext
  ext i j
  exact e.apply_symm_apply _

private lemma fieldMap_commutator :
    (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).map (fieldMap e) =
      commutator (Matrix.symplecticGroup (Fin 2) K) := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (fieldMap_surjective e), commutator_def]

private def derivedFieldMap : commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) →*
    commutator (Matrix.symplecticGroup (Fin 2) K) where
  toFun g := ⟨fieldMap e g.val, by
    rw [← fieldMap_commutator e]
    exact ⟨g.val, g.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

private lemma derivedFieldMap_surjective : Function.Surjective (derivedFieldMap e) := by
  intro g
  have hg := (fieldMap_commutator e).ge g.property
  obtain ⟨h, hh, he⟩ := hg
  exact ⟨⟨h, hh⟩, Subtype.ext he⟩

private def pullback (f : cocycles (symplecticDerivedNatural (k := K) 2)) :
    cocycles (symplecticDerivedNatural (k := ZMod 2) 2) :=
  ⟨fun g i => e.symm (f.val (derivedFieldMap e g) i), by
    intro g h
    funext i
    dsimp only
    rw [map_mul, f.property]
    change e.symm ((∑ j, e (g.val.val i j) * f.val (derivedFieldMap e h) j) +
      f.val (derivedFieldMap e g) i) =
      (∑ j, g.val.val i j * e.symm (f.val (derivedFieldMap e h) j)) +
        e.symm (f.val (derivedFieldMap e g) i)
    simp only [map_add, map_sum, map_mul, e.symm_apply_apply]⟩

variable [Finite K] [CharP K 2]

private lemma quadratic_transport (g : commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))
    (i : Fin 2 ⊕ Fin 2) :
    e ((derivedQuadraticCocycle (K := ZMod 2)).val g i) =
      (derivedQuadraticCocycle (K := K)).val (derivedFieldMap e g) i := by
  apply CharTwo.sq_injective (R := K)
  dsimp only
  rw [← map_pow, derivedQuadraticCocycle_apply_sq, derivedQuadraticCocycle_apply_sq]
  change e (rowQuadratic (g.val.val i)) = rowQuadratic (fun j => e (g.val.val i j))
  simp only [rowQuadratic, map_add, map_mul]

include e in
private theorem spanning_of_ringEquiv (f : cocycles (symplecticDerivedNatural (k := K) 2)) :
    ∃ (t : K) (v : (Fin 2 ⊕ Fin 2) → K),
      f = t • derivedQuadraticCocycle + principal (symplecticDerivedNatural 2) v := by
  obtain ⟨t, v, hv⟩ := exists_normal_form_zmod_two (pullback e f)
  refine ⟨e t, fun i => e (v i), ?_⟩
  apply Subtype.ext
  funext g i
  obtain ⟨g, rfl⟩ := derivedFieldMap_surjective e g
  have h := congrArg (fun c : cocycles (symplecticDerivedNatural (k := ZMod 2) 2) =>
    e (c.val g i)) hv
  change e (e.symm (f.val (derivedFieldMap e g) i)) =
    e (t * (derivedQuadraticCocycle (K := ZMod 2)).val g i +
      ((∑ j, g.val.val i j * v j) - v i)) at h
  change f.val (derivedFieldMap e g) i =
    e t * (derivedQuadraticCocycle (K := K)).val (derivedFieldMap e g) i +
      ((∑ j, e (g.val.val i j) * e (v j)) - e (v i))
  simpa only [e.apply_symm_apply, map_add, map_sub, map_mul, map_sum,
    quadratic_transport] using h

/-- The binary cocycle normal form over any two-element characteristic-two field. -/
public theorem exists_normal_form (hcard : Nat.card K = 2)
    (f : cocycles (symplecticDerivedNatural (k := K) 2)) :
    ∃ (t : K) (v : (Fin 2 ⊕ Fin 2) → K),
      f = t • derivedQuadraticCocycle + principal (symplecticDerivedNatural 2) v := by
  let := Fintype.ofFinite K
  exact spanning_of_ringEquiv
    (ZMod.ringEquiv K (by simpa [Nat.card_eq_fintype_card] using hcard)) f

end Representation.OneCohomology.SymplecticFour.BinaryField
