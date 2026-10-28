module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.FieldActors.Centralizer.Descent
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.FieldActors.Centralizer.Counting
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.ElementaryAbelian.Quotient

/-!
# Elementary subgroup bounds in the natural field-involution centralizer

In the fixed coordinates supplied by semilinear descent, the actual action of
an elementary subgroup of C_L(a) has all matrix entries in the coefficient
fixed field. This gives a faithful matrix action over the field of order 2^s.
Each matrix has square one, so its determinant is one in characteristic two.
Projection to PSL₃ remains faithful: a scalar matrix with square one is identity.
The all-degree PSL₃ two-rank theorem therefore bounds the subgroup order by 2^(2s).

This discharges the component-bound premise of the literal-centralizer counting
lemmas. It yields m₂(C_G(a)) ≤ 2s+1 and the same bound for elementary actors
containing a, including applications to the recognized natural SourceInput.
The attaining subgroup and the final equality belong to the centralizer assembly.

Source: Aschbacher–Smith, K.3.2.1, printed pp.454–455 (PDF pp.465–466),
combined manuscript of 1 March 2004.
-/

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Theory.GroupTheory
namespace CFSG.Quasithin.ChapterK.Linear.Natural.FieldActors.Centralizer

private theorem scalar_square_one {k : Type*} [Field k] [CharP k 2]
    (x : k) (hx : x ^ 2 = 1) : x = 1 := by
  rcases sq_eq_one_iff.mp hx with h | h
  · exact h
  · simpa only [CharTwo.neg_eq] using h

private theorem projective_injective_on_elementary {k E : Type*} [Field k] [CharP k 2]
    [Group E] [IsElementaryAbelian 2 E]
    (f : E →* Matrix.SpecialLinearGroup (Fin 3) k) (hf : Function.Injective f) :
    Function.Injective
      ((QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) k))).comp f) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hc : f x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) k) :=
    (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hx2 : (f x) ^ 2 = 1 := by
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) x, map_one]
  have hr2 : r ^ 2 = 1 := by
    have hm := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) k => g.val 0 0) hx2
    simp only [pow_two, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq, ← hr] at hm
    simpa [Matrix.scalar, Matrix.mul_apply, Fin.sum_univ_three, pow_two] using hm
  have hr1 := scalar_square_one r hr2
  have hfx : f x = 1 := Subtype.ext (by simpa [hr1] using hr.symm)
  exact hf (hfx.trans (map_one f).symm)

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) (F : BinaryField)
  (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 3))

private theorem exists_fixedField_embedding
    (hf : Function.Injective ρ) (hs : IsSemilinearExtension ρ L F 3 e)
    (a : G) (ha : orderOf a = 2) (haL : a ∉ L)
    (B : Subgroup G) (hB : IsElementaryAbelian 2 B) (hBL : B ≤ L)
    (hBC : B ≤ Subgroup.centralizer ({a} : Set G)) :
    ∃ f : B →* Matrix.SpecialLinearGroup (Fin 3)
      (fixedField F (coefficientAction ρ L F e hs a)), Function.Injective f := by
  classical
  let K := fixedField F (coefficientAction ρ L F e hs a)
  obtain ⟨c, hc⟩ := exists_fixed_coordinates F ρ L e hf hs a ha haL
  let j := e.groupEquiv.toMonoidHom.comp (Subgroup.inclusion hBL)
  let t : B →* Module.End F.Carrier (Fin 3 → F.Carrier) :=
    Matrix.toLinAlgEquiv'.toMonoidHom.comp (Matrix.SpecialLinearGroup.coeMonoidHom.comp j)
  have ht (b : B) (v : Fin 3 → F.Carrier) :
      t b v = coordinateAction ρ L F e b v := by
    exact (coordinateAction_natural ρ L F e (⟨b, hBL b.property⟩ : L) v).symm
  let m : B →* Matrix (Fin 3) (Fin 3) F.Carrier :=
    LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp (c.conjRingEquiv.toMonoidHom.comp t)
  have hm (b : B) (i j : Fin 3) : m b i j ∈ K := by
    apply (matrix_mem_fixedField_iff_commutes F ρ L e hs a c hc (t b)).mpr
    intro v
    rw [ht, ht]
    change (coordinateAction ρ L F e b * coordinateAction ρ L F e a) v =
      (coordinateAction ρ L F e a * coordinateAction ρ L F e b) v
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_singleton_iff.mp (hBC b.property))]
  let k : B →* Matrix (Fin 3) (Fin 3) K := {
    toFun b i j := ⟨m b i j, hm b i j⟩
    map_one' := by
      ext i j
      change m 1 i j = ((1 : Matrix (Fin 3) (Fin 3) K) i j : F.Carrier)
      simp only [map_one, Matrix.one_apply]
      split_ifs <;> rfl
    map_mul' b d := by
      ext i j
      change m (b * d) i j = _
      simp only [map_mul, Matrix.mul_apply]
      rfl }
  have hkdet (b : B) : (k b).det = 1 := by
    apply scalar_square_one
    rw [← Matrix.det_pow, ← map_pow,
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hB.exponent_dvd_p b,
      map_one, Matrix.det_one]
  let f : B →* Matrix.SpecialLinearGroup (Fin 3) K := {
    toFun b := ⟨k b, hkdet b⟩
    map_one' := Subtype.ext (map_one k)
    map_mul' b d := Subtype.ext (map_mul k b d) }
  refine ⟨f, ?_⟩
  intro b d h
  have hm' : m b = m d := by
    ext i j
    exact congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) K => (g.val i j : F.Carrier)) h
  have ht' : t b = t d := c.conjRingEquiv.injective (LinearMap.toMatrixAlgEquiv'.injective hm')
  have hj : j b = j d := Subtype.ext (Matrix.toLinAlgEquiv'.injective ht')
  exact (Subgroup.inclusion_injective hBL) (e.groupEquiv.injective hj)

/-- Every elementary subgroup of the linear centralizer has order at most 2^(2s), for every s > 0. -/
theorem component_elementary_card_le
    (hf : Function.Injective ρ) (hs : IsSemilinearExtension ρ L F 3 e)
    (a : G) (ha : orderOf a = 2) (haL : a ∉ L)
    (s : ℕ) (hspos : 0 < s) (hdegree : F.degree = 2 * s)
    (B : Subgroup G) (hB : IsElementaryAbelian 2 B) (hBL : B ≤ L)
    (hBC : B ≤ Subgroup.centralizer ({a} : Set G)) : Nat.card B ≤ 2 ^ (2 * s) := by
  let K := fixedField F (coefficientAction ρ L F e hs a)
  let : IsElementaryAbelian 2 B := hB
  obtain ⟨f, hf'⟩ := exists_fixedField_embedding ρ L F e hf hs a ha haL B hB hBL hBC
  let p : B →* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K :=
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K))).comp f
  have hp : Function.Injective p := projective_injective_on_elementary f hf'
  have hE : IsElementaryAbelian 2 p.range :=
    IsElementaryAbelian.of_surjective p.rangeRestrict p.rangeRestrict_surjective
  have hK : Nat.card K = 2 ^ s := fixedField_card F _
    (outer_coefficient_orderOf ρ L F e hf hs a ha haL) s hdegree
  have hr : primeRank 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) ≤ 2 * s :=
    (Matrix.PSL3Even.two_rank K hspos hK).le
  have hb := (primeRank_le_iff_elementary_card_le _).mp hr p.range hE
  rwa [← Nat.card_congr (MonoidHom.ofInjective hp).toEquiv] at hb

/-- The literal ambient centralizer of the outer field involution has two-rank at most 2s+1. -/
theorem primeRank_centralizer_le
    (hf : Function.Injective ρ) (hs : IsSemilinearExtension ρ L F 3 e)
    (a : G) (ha : orderOf a = 2) (haL : a ∉ L)
    (s : ℕ) (hspos : 0 < s) (hdegree : F.degree = 2 * s) :
    primeRank 2 (Subgroup.centralizer ({a} : Set G)) ≤ 2 * s + 1 :=
  primeRank_le_of_component_bound ρ L F e hf hs a (2 * s)
    (component_elementary_card_le ρ L F e hf hs a ha haL s hspos hdegree)

/-- Every elementary actor containing the given outer involution has rank at most 2s+1. -/
theorem elementary_rank_le
    (hf : Function.Injective ρ) (hs : IsSemilinearExtension ρ L F 3 e)
    (a : G) (ha : orderOf a = 2) (haL : a ∉ L)
    (s : ℕ) (hspos : 0 < s) (hdegree : F.degree = 2 * s)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (haA : a ∈ A) :
    rank A ≤ 2 * s + 1 :=
  elementary_rank_le_of_component_bound ρ L F e hf hs a (2 * s)
    (component_elementary_card_le ρ L F e hf hs a ha haL s hspos hdegree) A hA haA

/-- The component estimate on the recognized natural source input, with all descent premises discharged. -/
theorem source_component_elementary_card_le {K : GroupClass}
    (h : SourceInput ρ L F 3 K) (a : G) (ha : orderOf a = 2) (haL : a ∉ L)
    (s : ℕ) (hspos : 0 < s) (hdegree : F.degree = 2 * s)
    (B : Subgroup G) (hB : IsElementaryAbelian 2 B) (hBL : B ≤ L)
    (hBC : B ≤ Subgroup.centralizer ({a} : Set G)) : Nat.card B ≤ 2 ^ (2 * s) :=
  component_elementary_card_le ρ L F h.natural h.faithful h.semilinear
    a ha haL s hspos hdegree B hB hBL hBC

/-- The upper half of the source centralizer-rank equality in K.3.2.1. -/
theorem source_primeRank_centralizer_le {K : GroupClass}
    (h : SourceInput ρ L F 3 K) (a : G) (ha : orderOf a = 2) (haL : a ∉ L)
    (s : ℕ) (hspos : 0 < s) (hdegree : F.degree = 2 * s) :
    primeRank 2 (Subgroup.centralizer ({a} : Set G)) ≤ 2 * s + 1 :=
  primeRank_centralizer_le ρ L F h.natural h.faithful h.semilinear
    a ha haL s hspos hdegree

/-- The source rank inequality for an elementary actor containing the specified outer involution. -/
theorem source_elementary_rank_le {K : GroupClass}
    (h : SourceInput ρ L F 3 K) (a : G) (ha : orderOf a = 2) (haL : a ∉ L)
    (s : ℕ) (hspos : 0 < s) (hdegree : F.degree = 2 * s)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (haA : a ∈ A) :
    rank A ≤ 2 * s + 1 :=
  elementary_rank_le ρ L F h.natural h.faithful h.semilinear
    a ha haL s hspos hdegree A hA haA

end CFSG.Quasithin.ChapterK.Linear.Natural.FieldActors.Centralizer
