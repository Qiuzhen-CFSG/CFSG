module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Stem
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Inputs to the principal eleven-block construction

The coefficient closure has the required prime-to-eleven roots. The actual
ordinary table is real, and its unique class of elements of order eleven
gives fusion inside the Sylow normalizer. These are inputs to the cyclic-defect
argument, not an existence proof for a Brauer tree or its modules.

Source: Feit, *The Representation Theory of Finite Groups*, VII.2.11,
VII.6.8 and VII.9.2; Janko (1966), as summarized in Gorenstein §16.6.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction

open Subgroup

/-- The literal coefficient field admits the root correspondence used by the stem. -/
public theorem exists_elevenRootLift :
    Nonempty (Representation.CyclicRootLift ElevenClosure 15960) := by
  let : NeZero (15960 : ElevenClosure) := ⟨by
    exact (CharP.cast_eq_zero_iff ElevenClosure 11 15960).not.mpr (by decide)⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ElevenClosure 15960
  exact ⟨⟨by decide, z, _, hz, Complex.isPrimitiveRoot_exp 15960 (by decide)⟩⟩

private theorem star_root_pow {z : ℂ} {n k : ℕ} (hz : IsPrimitiveRoot z n)
    (hn : n ≠ 0) (hk : k ≤ n) : star (z ^ k) = z ^ (n - k) := by
  have hnorm : ‖z ^ k‖ = 1 := by rw [norm_pow, hz.norm'_eq_one hn, one_pow]
  have hp : z ^ (n - k) * z ^ k = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hk, hz.pow_eq_one]
  exact (Complex.inv_eq_conj hnorm).symm.trans (eq_inv_of_mul_eq_one_left hp).symm

private theorem star_cons {A : Type*} [Star A] {n : ℕ} (a : A) (v : Fin n → A) :
    star (Matrix.vecCons a v) = Matrix.vecCons (star a) (star v) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem star_empty {A : Type*} [Star A] :
    star (Matrix.vecEmpty : Fin 0 → A) = Matrix.vecEmpty := Subsingleton.elim _ _

/-- Every entry of the prescribed ordinary table is real. -/
public theorem ordinaryValue_real {z w : ℂ}
    (hz : IsPrimitiveRoot z 5) (hw : IsPrimitiveRoot w 19) (i j : Fin 15) :
    star (ordinaryValue z w i j) = ordinaryValue z w i j := by
  have hz1 : star z = z ^ 4 := by simpa using star_root_pow hz (by decide) (by decide : 1 ≤ 5)
  have hw1 : star w = w ^ 18 := by simpa using star_root_pow hw (by decide) (by decide : 1 ≤ 19)
  have ha : star (z + z ^ 4) = z + z ^ 4 := by
    rw [star_add, hz1, star_root_pow hz (by decide) (by decide : 4 ≤ 5)]
    norm_num; ring
  have hb : star (z ^ 2 + z ^ 3) = z ^ 2 + z ^ 3 := by
    rw [star_add, star_root_pow hz (by decide) (by decide : 2 ≤ 5),
      star_root_pow hz (by decide) (by decide : 3 ≤ 5)]
    norm_num; ring
  have hc : star (w + w ^ 7 + w ^ 8 + w ^ 11 + w ^ 12 + w ^ 18) =
      w + w ^ 7 + w ^ 8 + w ^ 11 + w ^ 12 + w ^ 18 := by
    simp only [star_add, hw1]
    rw [star_root_pow hw (by decide) (by decide : 7 ≤ 19),
      star_root_pow hw (by decide) (by decide : 8 ≤ 19),
      star_root_pow hw (by decide) (by decide : 11 ≤ 19),
      star_root_pow hw (by decide) (by decide : 12 ≤ 19),
      star_root_pow hw (by decide) (by decide : 18 ≤ 19)]
    norm_num; ring
  have hd : star (w ^ 2 + w ^ 3 + w ^ 5 + w ^ 14 + w ^ 16 + w ^ 17) =
      w ^ 2 + w ^ 3 + w ^ 5 + w ^ 14 + w ^ 16 + w ^ 17 := by
    simp only [star_add]
    rw [star_root_pow hw (by decide) (by decide : 2 ≤ 19),
      star_root_pow hw (by decide) (by decide : 3 ≤ 19),
      star_root_pow hw (by decide) (by decide : 5 ≤ 19),
      star_root_pow hw (by decide) (by decide : 14 ≤ 19),
      star_root_pow hw (by decide) (by decide : 16 ≤ 19),
      star_root_pow hw (by decide) (by decide : 17 ≤ 19)]
    norm_num; ring
  have he : star (w ^ 4 + w ^ 6 + w ^ 9 + w ^ 10 + w ^ 13 + w ^ 15) =
      w ^ 4 + w ^ 6 + w ^ 9 + w ^ 10 + w ^ 13 + w ^ 15 := by
    simp only [star_add]
    rw [star_root_pow hw (by decide) (by decide : 4 ≤ 19),
      star_root_pow hw (by decide) (by decide : 6 ≤ 19),
      star_root_pow hw (by decide) (by decide : 9 ≤ 19),
      star_root_pow hw (by decide) (by decide : 10 ≤ 19),
      star_root_pow hw (by decide) (by decide : 13 ≤ 19),
      star_root_pow hw (by decide) (by decide : 15 ≤ 19)]
    norm_num; ring
  have ht : star (ordinaryValue z w) = ordinaryValue z w := by
    simp only [ordinaryValue, star_cons, star_empty, star_one, star_zero, star_ofNat,
      star_mul, star_neg, ha, hb, hc, hd, he, mul_comm]
  exact congrFun (congrFun ht i) j

variable {G : Type*} [Group G] [Finite G]

/-- Realness holds on all actual conjugacy classes, not only on a numerical array. -/
public theorem ordinaryCharacters_real (d : OrdinaryData G) (i : Fin 15) (c : ConjClasses G) :
    star (d.chi i c) = d.chi i c := by
  obtain ⟨j, rfl⟩ := d.classes.surjective c
  rw [d.values]
  exact ordinaryValue_real d.rootFive_primitive d.rootNineteen_primitive i j

/-- The actual eleven-regular columns are exactly those used in tensorCoefficient. -/
public theorem regular_representative_iff (d : OrdinaryData G) (i : Fin 15) :
    ¬ 11 ∣ orderOf (d.representatives i) ↔ i ≠ 9 := by
  rw [d.orders]
  fin_cases i <;> decide

/-- Every element of order eleven belongs to the single specified class. -/
public theorem eleven_class (d : OrdinaryData G) (x : G) (hx : orderOf x = 11) :
    ConjClasses.mk x = d.classes 9 := by
  obtain ⟨i, hi⟩ := d.classes.surjective (ConjClasses.mk x)
  have hc : IsConj (d.representatives i) x :=
    ConjClasses.mk_eq_mk_iff_isConj.mp ((d.classes_eq i).symm.trans hi)
  obtain ⟨a, ha⟩ := isConj_iff.mp hc
  have ho : classOrder i = 11 := by
    rw [← d.orders, ← hx, ← ha]
    exact ((MulAut.conj a).orderOf_eq _).symm
  have he : i = 9 :=
    (show ∀ c : Fin 15, classOrder c = 11 → c = 9 from by decide) i ho
  simpa only [he] using hi.symm

/-- Any two elements of order eleven are conjugate in the source group. -/
public theorem eleven_fusion (d : OrdinaryData G) (x y : G)
    (hx : orderOf x = 11) (hy : orderOf y = 11) : IsConj x y :=
  ConjClasses.mk_eq_mk_iff_isConj.mp ((eleven_class d x hx).trans (eleven_class d y hy).symm)

/-- Fusion of the nonidentity Sylow elements is already realized by its normalizer. -/
public theorem sylow_eleven_normalizer_transitive (d : OrdinaryData G)
    (horder : Nat.card G = 175560) (P : Sylow 11 G) (x y : P)
    (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ n ∈ normalizer (P : Set G), n * (x : G) * n⁻¹ = (y : G) := by
  let : IsCyclic P := sylow_eleven_isCyclic horder P
  have ho (z : P) (hz : z ≠ 1) : orderOf (z : G) = 11 := by
    rw [orderOf_coe z, orderOf_eq_card_of_zpowers_eq_top
      (zpowers_eq_top_of_prime_card (sylow_eleven_card horder P) hz),
      sylow_eleven_card horder P]
  obtain ⟨g, hg⟩ := isConj_iff.mp (eleven_fusion d x y (ho x hx) (ho y hy))
  obtain ⟨n, hn, heq⟩ := P.conj_eq_normalizer_conj_of_mem (x : G) g⁻¹ x.property
    (by simpa only [inv_inv, hg] using y.property)
  refine ⟨n⁻¹, (normalizer (P : Set G)).inv_mem hn, ?_⟩
  simpa only [inv_inv, hg] using heq.symm

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction
