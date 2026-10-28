module

public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic.NormNum

/-!
# The centralizer of a symmetric-three pair has no cubic elements

The pair has trivial centre, so its ambient centralizer meets it trivially.
Two coordinate three-cycles and a hypothetical centralizing cubic element
therefore embed an elementary abelian group of order 27. This contradicts
an ambient three-rank bound of two.

Source: the rank argument in Aschbacher–Smith, proof of 13.8.5,
combined manuscript of 1 March 2004, printed p.947 (PDF p.964).
-/

public section

open Subgroup
namespace Theory.GroupTheory.NormalSymmetricThreePairRank
local notation "S3" => Equiv.Perm (Fin 3)
variable {A : Type*} [Group A] (K : Subgroup A)

/-- The ambient centralizer meets a symmetric-three pair trivially. -/
theorem disjoint_centralizer (e : K ≃* (S3 × S3)) : Disjoint K (centralizer (K : Set A)) := by
  apply disjoint_def.mpr
  intro x hx hc
  let z : K := ⟨x, hx⟩
  have hcomm (y : S3 × S3) : y * e z = e z * y := by
    have hh := mem_centralizer_iff.mp hc (e.symm y) (e.symm y).property
    have ht : e.symm y * z = z * e.symm y := Subtype.ext hh
    simpa only [map_mul, e.apply_symm_apply] using congrArg e ht
  have hz : e z = 1 := by
    apply Prod.ext
    · apply symmetricThree_center_trivial
      intro y
      exact congrArg Prod.fst (hcomm (y, 1))
    · apply symmetricThree_center_trivial
      intro y
      exact congrArg Prod.snd (hcomm (1, y))
  exact congrArg Subtype.val (e.injective (hz.trans e.map_one.symm))

private def cubic : Subgroup S3 := zpowers (Equiv.swap 0 1 * Equiv.swap 1 2)
private theorem cubic_card : Nat.card cubic = 3 := by
  rw [cubic, Nat.card_zpowers]
  apply orderOf_eq_prime (p := 3) <;> decide +kernel

/-- A cubic element in the centralizer would extend the actual elementary nine
in the pair to an elementary group of order twenty-seven. -/
theorem three_not_dvd_card_centralizer (e : K ≃* (S3 × S3)) [Finite A] (hrank : primeRank 3 A ≤ 2) :
    ¬ 3 ∣ Nat.card (centralizer (K : Set A)) := by
  intro hd
  let C := centralizer (K : Set A)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 hd
  let P := zpowers c
  let : IsCyclic cubic := by unfold cubic; infer_instance
  let : CommGroup cubic := IsCyclic.commGroup
  let : CommGroup P := IsCyclic.commGroup
  have hP : Nat.card P = 3 := (Nat.card_zpowers c).trans hc
  let f : cubic × cubic →* A := (K.subtype.comp e.symm.toMonoidHom).comp
    (cubic.subtype.prodMap cubic.subtype)
  let g : P →* A := C.subtype.comp P.subtype
  have hf : Function.Injective f := by
    apply K.subtype_injective.comp
    apply e.symm.injective.comp
    intro x y h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have hg : Function.Injective g := C.subtype_injective.comp P.subtype_injective
  have hfK : f.range ≤ K := by rintro _ ⟨x, rfl⟩; exact (e.symm _).property
  have hgC : g.range ≤ C := by rintro _ ⟨x, rfl⟩; exact x.val.property
  have hcomm (x : cubic × cubic) (y : P) : Commute (f x) (g y) :=
    mem_centralizer_iff.mp (hgC ⟨y, rfl⟩) (f x) (hfK ⟨x, rfl⟩)
  let j := f.noncommCoprod g hcomm
  have hj : Function.Injective j := (MonoidHom.noncommCoprod_injective f g hcomm).mpr
    ⟨hf, hg, (disjoint_centralizer K e).mono hfK hgC⟩
  have hpow : ∀ x : (cubic × cubic) × P, x ^ 3 = 1 := by
    rintro ⟨⟨x, y⟩, z⟩
    simp only [Prod.pow_mk]
    apply Prod.ext
    · apply Prod.ext
      · simpa [cubic_card] using (pow_card_eq_one' (x := x))
      · simpa [cubic_card] using (pow_card_eq_one' (x := y))
    · change z ^ 3 = 1
      simpa only [hP] using (pow_card_eq_one' (x := z))
  have hcard : Nat.card ((cubic × cubic) × P) = 3 ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod, cubic_card, hP]
    norm_num
  have h := primeRank_ge_of_elementary_embedding hpow hcard j hj
  omega

end Theory.GroupTheory.NormalSymmetricThreePairRank
