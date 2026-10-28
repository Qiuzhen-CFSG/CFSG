module

public import Theory.AlgebraicGroup.RootSystems.G2ChevalleyBorelWeylExchange

/-!
# Mixed root-word collection for the explicit G2 carrier

This module packages the finite termination argument for arbitrary words in
the twelve displayed root curves.  A same-sign word is first collected into
the six-slot convex product by the explicit positive-Borel collector.  A
nonzero negative factor is then isolated by the singular branch of the
rank-one exchange, while its transported Weyl representative is reduced by
the finite twelve-state Tits table.  The resulting induction has one state
`positive Borel * canonical Weyl word * positive Borel`; the public
finite-Borel exchange closes the state after every factor.  Conjugating the
left Borel by the longest Weyl word and moving the resulting torus factors
then gives the final `negative roots * Weyl * torus * positive roots` form.

All carrier equalities are inherited from the integral G2 representation and
the characteristic-free root-swap, torus, Weyl-lift, finite-normalizer, and
rank-one exchange packages.  The construction uses no root exhaustiveness,
root realization, semisimplicity, center, or general Chevalley presentation
theorem.  The six-slot factors are ordered by the fixed alternating convex
word, so each listed root occurs at most once.
-/

open scoped Matrix
open Theory AlgebraicGroup

namespace Theory.AlgebraicGroup.G2Chevalley

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

public noncomputable def carrierRootFactor (r : Root) (a : k) : CarrierPoint (k := k) :=
  (rootMorphism (k := k) r).onPoints (kPlusPoint a)

public noncomputable def carrierRootWordProduct (word : List (Root × k)) :
    CarrierPoint (k := k) :=
  (word.map fun z => carrierRootFactor z.1 z.2).prod

public def carrierPositiveSlotOrder : List Root :=
  [Root.short, Root.threeShortLong, Root.twoShortLong,
    Root.threeShortTwoLong, Root.shortLong, Root.long]

public def carrierNegativeSlotOrder : List Root :=
  [Root.negShort, Root.negThreeShortLong, Root.negTwoShortLong,
    Root.negThreeShortTwoLong, Root.negShortLong, Root.negLong]

/-- The positive six-slot order contains each displayed root exactly once. -/
public theorem carrierPositiveSlotOrder_nodup : carrierPositiveSlotOrder.Nodup := by
  decide

/-- The negative six-slot order contains each displayed root exactly once. -/
public theorem carrierNegativeSlotOrder_nodup : carrierNegativeSlotOrder.Nodup := by
  decide

/-- The ordered six-slot negative-root product obtained by negating the
positive convex order. -/
public noncomputable def carrierNegativeRootProduct (a : Fin 6 → k) :
    CarrierPoint (k := k) :=
  ([0, 1, 2, 3, 4, 5].map fun i : Fin 6 =>
    carrierRootFactor (k := k) (-positiveConvexRoot i) (a i)).prod

private noncomputable def H (t : Variety.Point (dVariety k 2)) :
    CarrierPoint (k := k) :=
  (splitTorusMorphism (k := k)).onPoints t

private lemma H_mul (t s : Variety.Point (dVariety k 2)) :
    H (k := k) t * H s = H (t * s) := by
  exact ((splitTorusMorphism (k := k)).onPoints.map_mul t s).symm

private lemma H_one : H (k := k) 1 = 1 := by
  exact (splitTorusMorphism (k := k)).onPoints.map_one

private lemma H_inv (t : Variety.Point (dVariety k 2)) :
    (H (k := k) t)⁻¹ = H t⁻¹ := by
  exact ((splitTorusMorphism (k := k)).onPoints.map_inv t).symm

private lemma H_comm (t s : Variety.Point (dVariety k 2)) :
    H (k := k) t * H s = H s * H t := by
  rw [H_mul, H_mul]
  congr 1
  apply (dPointEquiv 2).injective
  funext i
  exact mul_comm _ _

private lemma X_zero (r : Root) : carrierRootFactor (k := k) r 0 = 1 := by
  have hz : kPlusPoint (0 : k) = 1 := by
    apply (additiveGroupPointEquiv k).injective
    rfl
  change (rootMorphism (k := k) r).onPoints (kPlusPoint 0) = 1
  rw [hz]
  exact (rootMorphism (k := k) r).onPoints.map_one

private noncomputable def torusScale (r : Root)
    (t : Variety.Point (dVariety k 2)) : k := by
  letI := (splitTorus (k := k)).carrierAlgebraicGroup
  exact (rootWeight (k := k) r).pointCharacter
    ((splitTorusIso (k := k)).hom.onPoints t)

private lemma X_move_H (r : Root) (a : k)
    (t : Variety.Point (dVariety k 2)) :
    carrierRootFactor (k := k) r a * H t =
      H t * carrierRootFactor r (torusScale r t * a) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  have h := rootMorphism_splitTorus_conjugation (k := k) r a
    ((splitTorusIso (k := k)).hom.onPoints t)
  change ((splitTorus (k := k)).inclusion.onPoints
      ((splitTorusIso (k := k)).hom.onPoints t))⁻¹ * carrierRootFactor r a *
      (splitTorus (k := k)).inclusion.onPoints
        ((splitTorusIso (k := k)).hom.onPoints t) =
    carrierRootFactor r (torusScale r t * a) at h
  have h' : (H (k := k) t)⁻¹ * carrierRootFactor r a * H t =
      carrierRootFactor r (torusScale r t * a) := by
    simpa only [H, splitTorusIso_inclusion_apply] using h
  exact (by
    calc
      carrierRootFactor (k := k) r a * H t =
          H t * ((H t)⁻¹ * carrierRootFactor r a * H t) := by group
      _ = H t * carrierRootFactor r (torusScale r t * a) := by rw [h'])

private lemma torus_mul_positive_root_exists (r : Root) (a : k)
    (hr : r.val < 6) (t : Variety.Point (dVariety k 2)) :
    ∃ u : Variety.Point (dVariety k 2), ∃ c : Fin 6 → k,
      H t * carrierRootFactor r a =
        carrierPositiveBorelFactor u c := by
  obtain ⟨s, c, hc⟩ := carrierRootFactor_positiveBorel_exists (k := k) r a hr
  refine ⟨t * s, c, ?_⟩
  calc
    H t * carrierRootFactor r a =
        H t * carrierPositiveBorelFactor s c := congrArg (H t * ·) hc
    _ = carrierPositiveBorelFactor (t * s) c := by
      change H t * (H s * carrierPositiveRootProduct c) =
        H (t * s) * carrierPositiveRootProduct c
      rw [← mul_assoc, H_mul]

private lemma positive_root_mul_torus_exists (r : Root) (a : k)
    (hr : r.val < 6) (t : Variety.Point (dVariety k 2)) :
    ∃ u : Variety.Point (dVariety k 2), ∃ c : Fin 6 → k,
      carrierRootFactor r a * H t = carrierPositiveBorelFactor u c := by
  rw [X_move_H]
  exact torus_mul_positive_root_exists (k := k) r (torusScale r t * a) hr t

private lemma positive_borel_mul_exists
    (t s : Variety.Point (dVariety k 2)) (a b : Fin 6 → k) :
    ∃ u : Variety.Point (dVariety k 2), ∃ c : Fin 6 → k,
      carrierPositiveBorelFactor t a * carrierPositiveBorelFactor s b =
        carrierPositiveBorelFactor u c :=
  carrierPositiveBorelFactor_mul_exists t s a b

private lemma signedWord_append (u v : List (Fin 2 × Bool)) :
    signedCarrierWord (k := k) (u ++ v) =
      signedCarrierWord u * signedCarrierWord v := by
  induction u with
  | nil => simp [signedCarrierWord]
  | cons z u ih =>
      simp only [List.cons_append, signedCarrierWord]
      rw [ih]
      simp only [mul_assoc]

private lemma signedWord_unsigned (w : List (Fin 2)) :
    signedCarrierWord (k := k) (w.map fun i => (i, false)) =
      carrierWeylWord (k := k) w := by
  induction w with
  | nil => simp [signedCarrierWord, carrierWeylWord]
  | cons i w ih => simp [signedCarrierWord, carrierWeylWord, ih]

private lemma signedWord_reverse_inverse (w : List (Fin 2)) :
    signedCarrierWord (k := k)
        (w.reverse.map fun i => (i, true)) =
      (carrierWeylWord (k := k) w)⁻¹ := by
  induction w with
  | nil => simp [signedCarrierWord, carrierWeylWord]
  | cons i w ih =>
      simp only [List.reverse_cons, List.map_append, List.map_singleton]
      rw [signedWord_append, ih]
      simp [signedCarrierWord, carrierWeylWord, mul_inv_rev,
        carrierWeylRepresentative_inv]

private def rootRepresentativeWord (r : Root) : List (Fin 2 × Bool) :=
  (rootTransportWord r).reverse.map (fun i => (i, true)) ++
    [(rootBaseIndex r, false)] ++
    (rootTransportWord r).map (fun i => (i, false))

private lemma rootRepresentativeWord_eq (r : Root) :
    signedCarrierWord (k := k) (rootRepresentativeWord r) =
      rootWeylRepresentative (k := k) r := by
  unfold rootRepresentativeWord
  rw [signedWord_append, signedWord_append]
  rw [signedWord_reverse_inverse, signedWord_unsigned]
  simp [signedCarrierWord]
  rw [← carrierWeylWordInv_eq_inv]
  rfl

private lemma rootRepresentative_canonical (r : Root) :
    ∃ j : Fin 12, ∃ t : Variety.Point (dVariety k 2),
      rootWeylRepresentative (k := k) r =
        carrierWeylWord (k := k) (canonicalWeylWord j) * H t := by
  obtain ⟨j, t, h⟩ := exists_canonicalWeyl_normalForm (k := k)
    (rootRepresentativeWord r)
  exact ⟨j, t, by rw [← rootRepresentativeWord_eq]; exact h⟩

private lemma positiveRoot_nonzero_borelWeyl (r : Root) (a : k)
    (hr : r.val < 6) :
    ∃ t : Variety.Point (dVariety k 2), ∃ c : Fin 6 → k,
      carrierRootFactor r a = carrierPositiveBorelFactor t c :=
  carrierRootFactor_positiveBorel_exists r a hr

private lemma negativeRoot_borelWeyl (r : Root) (a : k)
    (hr : 6 ≤ r.val) :
    ∃ tLeft : Variety.Point (dVariety k 2), ∃ aLeft : Fin 6 → k,
      ∃ j : Fin 12, ∃ tRight : Variety.Point (dVariety k 2),
        ∃ aRight : Fin 6 → k,
          carrierRootFactor r a =
            carrierPositiveBorelFactor tLeft aLeft *
              carrierWeylWord (k := k) (canonicalWeylWord j) *
                carrierPositiveBorelFactor tRight aRight := by
  by_cases ha : a = 0
  · subst a
    refine ⟨1, fun _ => 0, 0, 1, fun _ => 0, ?_⟩
    rw [X_zero]
    simp [carrierPositiveBorelFactor_one, canonicalWeylWord, carrierWeylWord]
  let b : k := (Units.mk0 a ha)⁻¹
  have hab : a * b = 1 := by simp [b, ha]
  let d : kˣ := Units.mk0 b (right_ne_zero_of_mul_eq_one hab)
  have hsing := carrier_oppositeRootProduct_singular (k := k) r a b hab
  have hpos : (-r).val < 6 := by
    fin_cases r <;> norm_num at hr <;> norm_num
    all_goals change Root.neg _ < 6
    all_goals decide
  obtain ⟨u, cu, hcu⟩ := positive_root_mul_torus_exists (k := k) (-r) (-b)
    hpos (rootCorootTorusPoint (k := k) r d)
  obtain ⟨j, s, hs⟩ := rootRepresentative_canonical (k := k) r
  obtain ⟨v, cv, hcv⟩ := torus_mul_positive_root_exists (k := k) (-r) (-b)
    hpos s
  change carrierRootFactor (-r) (-b) * rootCorootTorusFactor r d =
    carrierPositiveBorelFactor u cu at hcu
  refine ⟨u, cu, j, v, cv, ?_⟩
  have hinv : (carrierRootFactor (k := k) (-r) b)⁻¹ =
      carrierRootFactor (-r) (-b) := by
    change ((rootMorphism (k := k) (-r)).onPoints (kPlusPoint b))⁻¹ = _
    rw [← (rootMorphism (k := k) (-r)).onPoints.map_inv]
    congr 1
  have hsing' : carrierRootFactor (k := k) r a * carrierRootFactor (-r) b =
      carrierRootFactor (-r) (-b) * rootCorootTorusFactor r d *
        rootWeylRepresentative r := by
    simpa [carrierRootFactor, d] using hsing
  have hsolve : carrierRootFactor (k := k) r a =
      carrierRootFactor (-r) (-b) *
        rootCorootTorusFactor r d * rootWeylRepresentative r *
          carrierRootFactor (-r) (-b) := by
    calc
      carrierRootFactor (k := k) r a =
          (carrierRootFactor r a * carrierRootFactor (-r) b) *
            (carrierRootFactor (-r) b)⁻¹ := by group
      _ = (carrierRootFactor (-r) (-b) * rootCorootTorusFactor r d *
          rootWeylRepresentative r) * carrierRootFactor (-r) (-b) := by
            rw [hsing', hinv]
  rw [hsolve, hs]
  calc
    carrierRootFactor (-r) (-b) * rootCorootTorusFactor r d *
          (carrierWeylWord (canonicalWeylWord j) * H s) *
        carrierRootFactor (-r) (-b) =
      (carrierRootFactor (-r) (-b) * rootCorootTorusFactor r d) *
        carrierWeylWord (canonicalWeylWord j) *
          (H s * carrierRootFactor (-r) (-b)) := by group
    _ = carrierPositiveBorelFactor u cu *
        carrierWeylWord (canonicalWeylWord j) *
          carrierPositiveBorelFactor v cv := by rw [hcu, hcv]

private lemma rootFactor_borelWeyl (r : Root) (a : k) :
    ∃ tLeft : Variety.Point (dVariety k 2), ∃ aLeft : Fin 6 → k,
      ∃ j : Fin 12, ∃ tRight : Variety.Point (dVariety k 2),
        ∃ aRight : Fin 6 → k,
          carrierRootFactor r a =
            carrierPositiveBorelFactor tLeft aLeft *
              carrierWeylWord (k := k) (canonicalWeylWord j) *
                carrierPositiveBorelFactor tRight aRight := by
  by_cases h : r.val < 6
  · obtain ⟨t, c, hc⟩ := positiveRoot_nonzero_borelWeyl (k := k) r a h
    refine ⟨t, c, 0, 1, fun _ => 0, ?_⟩
    rw [carrierPositiveBorelFactor_one]
    simpa [canonicalWeylWord, carrierWeylWord] using hc
  · exact negativeRoot_borelWeyl (k := k) r a (Nat.le_of_not_gt h)

/-- Every finite explicit G2 root word has a finite canonical Borel-Weyl form.

The two six-slot factors are in the fixed convex order, and the finite Weyl
state is one of the twelve canonical alternating words. -/
public theorem exists_carrierRootWord_borelWeyl_normalForm
    (word : List (Root × k)) :
    ∃ tLeft : Variety.Point (dVariety k 2), ∃ aLeft : Fin 6 → k,
      ∃ j : Fin 12, ∃ tRight : Variety.Point (dVariety k 2),
        ∃ aRight : Fin 6 → k,
          carrierRootWordProduct word =
            carrierPositiveBorelFactor tLeft aLeft *
              carrierWeylWord (k := k) (canonicalWeylWord j) *
                carrierPositiveBorelFactor tRight aRight := by
  induction word with
  | nil =>
      refine ⟨1, fun _ => 0, 0, 1, fun _ => 0, ?_⟩
      simp [carrierRootWordProduct, carrierPositiveBorelFactor_one,
        canonicalWeylWord, carrierWeylWord]
  | cons z word ih =>
      obtain ⟨t, a, j, s, b, htail⟩ := ih
      obtain ⟨u, c, m, v, d, hz⟩ := rootFactor_borelWeyl (k := k) z.1 z.2
      obtain ⟨q, e, hq⟩ := positive_borel_mul_exists (k := k) v t d a
      obtain ⟨l, f, n, x, g, hmid⟩ :=
        carrierWeyl_positiveBorel_canonical_exchange (k := k) m j q e
      obtain ⟨r, h, hleft⟩ := positive_borel_mul_exists (k := k) u l c f
      obtain ⟨y, p, hright⟩ := positive_borel_mul_exists (k := k) x s g b
      refine ⟨r, h, n, y, p, ?_⟩
      change carrierRootFactor z.1 z.2 * carrierRootWordProduct word = _
      rw [hz, htail]
      calc
        (carrierPositiveBorelFactor u c *
            carrierWeylWord (k := k) (canonicalWeylWord m) *
              carrierPositiveBorelFactor v d) *
            (carrierPositiveBorelFactor t a *
              carrierWeylWord (k := k) (canonicalWeylWord j) *
                carrierPositiveBorelFactor s b) =
          carrierPositiveBorelFactor u c *
            (carrierWeylWord (k := k) (canonicalWeylWord m) *
              (carrierPositiveBorelFactor v d *
                carrierPositiveBorelFactor t a)) *
              carrierWeylWord (k := k) (canonicalWeylWord j) *
                carrierPositiveBorelFactor s b := by group
        _ = carrierPositiveBorelFactor u c *
            (carrierWeylWord (k := k) (canonicalWeylWord m) *
              carrierPositiveBorelFactor q e *
                carrierWeylWord (k := k) (canonicalWeylWord j)) *
              carrierPositiveBorelFactor s b := by
                rw [hq]
                group
        _ = carrierPositiveBorelFactor u c *
            (carrierPositiveBorelFactor l f *
              carrierWeylWord (k := k) (canonicalWeylWord n) *
                carrierPositiveBorelFactor x g) *
              carrierPositiveBorelFactor s b := by rw [hmid]
        _ = (carrierPositiveBorelFactor u c * carrierPositiveBorelFactor l f) *
            carrierWeylWord (k := k) (canonicalWeylWord n) *
              (carrierPositiveBorelFactor x g * carrierPositiveBorelFactor s b) := by
              group
        _ = carrierPositiveBorelFactor r h *
            carrierWeylWord (k := k) (canonicalWeylWord n) *
              carrierPositiveBorelFactor y p := by rw [hleft, hright]

private lemma carrierRootWordProduct_append (u v : List (Root × k)) :
    carrierRootWordProduct (k := k) (u ++ v) =
      carrierRootWordProduct u * carrierRootWordProduct v := by
  simp [carrierRootWordProduct, List.map_append]

private lemma carrierWeylWord_append (u v : List (Fin 2)) :
    carrierWeylWord (k := k) (u ++ v) =
      carrierWeylWord u * carrierWeylWord v := by
  induction u with
  | nil => simp [carrierWeylWord]
  | cons i u ih =>
      simp only [List.cons_append, carrierWeylWord, ih]
      group

private def simpleWeylInverseRootWord (i : Fin 2) : List (Root × k) :=
  [(simpleRoot i, -1), (-simpleRoot i, -1), (simpleRoot i, -1)]

private def carrierWeylInverseRootWord (w : List (Fin 2)) : List (Root × k) :=
  w.reverse.flatMap simpleWeylInverseRootWord

private lemma simpleWeylInverseRootWord_product (i : Fin 2) :
    carrierRootWordProduct (k := k) (simpleWeylInverseRootWord i) =
      carrierWeylRepresentativeInv (k := k) i := by
  simp [carrierRootWordProduct, simpleWeylInverseRootWord, carrierRootFactor,
    carrierWeylRepresentativeInv]
  group

private lemma carrierWeylInverseRootWord_product (w : List (Fin 2)) :
    carrierRootWordProduct (k := k) (carrierWeylInverseRootWord w) =
      (carrierWeylWord (k := k) w)⁻¹ := by
  induction w with
  | nil => simp [carrierWeylInverseRootWord, carrierRootWordProduct,
      carrierWeylWord]
  | cons i w ih =>
      simp only [carrierWeylInverseRootWord, List.reverse_cons,
        List.flatMap_append, List.flatMap_singleton]
      rw [carrierRootWordProduct_append]
      change carrierRootWordProduct (k := k) (carrierWeylInverseRootWord (k := k) w) *
          carrierRootWordProduct (k := k) (simpleWeylInverseRootWord (k := k) i) =
        (carrierWeylWord (k := k) (i :: w))⁻¹
      rw [ih, simpleWeylInverseRootWord_product]
      simp [carrierWeylWord, mul_inv_rev, carrierWeylRepresentative_inv]

private lemma conjugate_list_prod (g : CarrierPoint (k := k))
    (xs : List (CarrierPoint (k := k))) :
    g * xs.prod * g⁻¹ = (xs.map fun x => g * x * g⁻¹).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.prod_cons, List.map_cons]
      rw [← ih]
      group

private lemma longest_conjugate_positiveRootProduct_exists (a : Fin 6 → k) :
    ∃ b : Fin 6 → k,
      carrierWeylWord (k := k) (canonicalWeylWord 11) *
          carrierPositiveRootProduct a *
            (carrierWeylWord (k := k) (canonicalWeylWord 11))⁻¹ =
        carrierNegativeRootProduct b := by
  choose b hb using fun i : Fin 6 =>
    carrierLongestWeyl_root_conjugation_exists (k := k)
      (positiveConvexRoot i) (a i)
  refine ⟨b, ?_⟩
  unfold carrierPositiveRootProduct
  rw [conjugate_list_prod]
  unfold carrierNegativeRootProduct
  simp only [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  exact hb i

private lemma canonicalWeyl_torus_move_right_exists (j : Fin 12)
    (t : Variety.Point (dVariety k 2)) :
    ∃ s : Variety.Point (dVariety k 2),
      H t * carrierWeylWord (k := k) (canonicalWeylWord j) =
        carrierWeylWord (canonicalWeylWord j) * H s := by
  have hex : ∃ s : Variety.Point (dVariety k 2),
      (carrierWeylWord (k := k) (canonicalWeylWord j))⁻¹ * H t *
          carrierWeylWord (canonicalWeylWord j) = H s := by
    refine ⟨(dPointEquiv 2).symm
      (wordTorusParameter (canonicalWeylWord j) (dPointEquiv 2 t)), ?_⟩
    simpa only [H] using canonicalWeyl_torus_conjugation (k := k) j t
  obtain ⟨s, hs⟩ := hex
  refine ⟨s, ?_⟩
  calc
    H t * carrierWeylWord (canonicalWeylWord j) =
        carrierWeylWord (canonicalWeylWord j) *
          ((carrierWeylWord (canonicalWeylWord j))⁻¹ * H t *
            carrierWeylWord (canonicalWeylWord j)) := by group
    _ = carrierWeylWord (canonicalWeylWord j) * H s := by rw [hs]

private lemma canonicalWeyl_torus_conjugation_forward_exists (j : Fin 12)
    (t : Variety.Point (dVariety k 2)) :
    ∃ s : Variety.Point (dVariety k 2),
      carrierWeylWord (k := k) (canonicalWeylWord j) * H t *
          (carrierWeylWord (canonicalWeylWord j))⁻¹ = H s := by
  let inverseWord : List (Fin 2 × Bool) :=
    (canonicalWeylWord j).reverse.map (fun i => (i, true))
  obtain ⟨l, q, hq⟩ := exists_canonicalWeyl_normalForm (k := k) inverseWord
  have hq' : (carrierWeylWord (k := k) (canonicalWeylWord j))⁻¹ =
      carrierWeylWord (canonicalWeylWord l) * H q := by
    simp only [inverseWord] at hq
    rw [signedWord_reverse_inverse] at hq
    exact hq
  have hex : ∃ s : Variety.Point (dVariety k 2),
      (carrierWeylWord (k := k) (canonicalWeylWord l))⁻¹ * H t *
          carrierWeylWord (canonicalWeylWord l) = H s := by
    refine ⟨(dPointEquiv 2).symm
      (wordTorusParameter (canonicalWeylWord l) (dPointEquiv 2 t)), ?_⟩
    simpa only [H] using canonicalWeyl_torus_conjugation (k := k) l t
  obtain ⟨s, hs⟩ := hex
  refine ⟨s, ?_⟩
  calc
    carrierWeylWord (k := k) (canonicalWeylWord j) * H t *
        (carrierWeylWord (canonicalWeylWord j))⁻¹ =
      ((carrierWeylWord (canonicalWeylWord j))⁻¹)⁻¹ * H t *
        (carrierWeylWord (canonicalWeylWord j))⁻¹ := by simp
    _ = (carrierWeylWord (canonicalWeylWord l) * H q)⁻¹ * H t *
        (carrierWeylWord (canonicalWeylWord l) * H q) := by rw [hq']
    _ = (H q)⁻¹ *
        ((carrierWeylWord (canonicalWeylWord l))⁻¹ * H t *
          carrierWeylWord (canonicalWeylWord l)) * H q := by group
    _ = (H q)⁻¹ * H s * H q := by rw [hs]
    _ = H s := by
      rw [H_inv]
      calc
        H q⁻¹ * H s * H q = H q⁻¹ * (H s * H q) := by group
        _ = H q⁻¹ * (H q * H s) := by rw [H_comm]
        _ = H s := by
          rw [← mul_assoc, H_mul]
          simp [H_one]

private lemma longest_conjugate_positiveBorel_exists
    (t : Variety.Point (dVariety k 2)) (a : Fin 6 → k) :
    ∃ s : Variety.Point (dVariety k 2), ∃ b : Fin 6 → k,
      carrierWeylWord (k := k) (canonicalWeylWord 11) *
          carrierPositiveBorelFactor t a *
            (carrierWeylWord (canonicalWeylWord 11))⁻¹ =
        H s * carrierNegativeRootProduct b := by
  obtain ⟨s, hs⟩ := canonicalWeyl_torus_conjugation_forward_exists (k := k) 11 t
  obtain ⟨b, hb⟩ := longest_conjugate_positiveRootProduct_exists (k := k) a
  refine ⟨s, b, ?_⟩
  change carrierWeylWord (canonicalWeylWord 11) *
      (H t * carrierPositiveRootProduct a) *
        (carrierWeylWord (canonicalWeylWord 11))⁻¹ = _
  calc
    _ = (carrierWeylWord (canonicalWeylWord 11) * H t *
          (carrierWeylWord (canonicalWeylWord 11))⁻¹) *
        (carrierWeylWord (canonicalWeylWord 11) * carrierPositiveRootProduct a *
          (carrierWeylWord (canonicalWeylWord 11))⁻¹) := by group
    _ = H s * carrierNegativeRootProduct b := by rw [hs, hb]

private noncomputable def moveNegativeParams
    (t : Variety.Point (dVariety k 2)) (a : Fin 6 → k) : Fin 6 → k :=
  fun i => torusScale (-positiveConvexRoot i) t⁻¹ * a i

private lemma H_move_X (t : Variety.Point (dVariety k 2))
    (r : Root) (a : k) :
    H t * carrierRootFactor (k := k) r a =
      carrierRootFactor r (torusScale r t⁻¹ * a) * H t := by
  have h := X_move_H (k := k) r a t⁻¹
  calc
    H t * carrierRootFactor r a =
        H t * (carrierRootFactor r a * H t⁻¹) * H t := by
          rw [← H_inv]
          group
    _ = H t * (H t⁻¹ * carrierRootFactor r (torusScale r t⁻¹ * a)) * H t := by
          rw [h]
    _ = carrierRootFactor r (torusScale r t⁻¹ * a) * H t := by
          rw [← H_inv]
          group

private noncomputable def moveRootWord
    (t : Variety.Point (dVariety k 2)) (word : List (Root × k)) :
    List (Root × k) :=
  word.map fun z => (z.1, torusScale z.1 t⁻¹ * z.2)

private lemma H_move_rootWord (t : Variety.Point (dVariety k 2))
    (word : List (Root × k)) :
    H t * carrierRootWordProduct (k := k) word =
      carrierRootWordProduct (moveRootWord t word) * H t := by
  induction word with
  | nil => simp [carrierRootWordProduct, moveRootWord]
  | cons z word ih =>
      change H t * (carrierRootFactor z.1 z.2 * carrierRootWordProduct word) =
        carrierRootFactor z.1 (torusScale z.1 t⁻¹ * z.2) *
          carrierRootWordProduct (moveRootWord t word) * H t
      calc
        _ = (H t * carrierRootFactor z.1 z.2) *
            carrierRootWordProduct word := by group
        _ = (carrierRootFactor z.1 (torusScale z.1 t⁻¹ * z.2) * H t) *
            carrierRootWordProduct word := by rw [H_move_X]
        _ = carrierRootFactor z.1 (torusScale z.1 t⁻¹ * z.2) *
            (H t * carrierRootWordProduct word) := by group
        _ = _ := by
          rw [ih]
          group

private lemma H_move_negativeRootProduct
    (t : Variety.Point (dVariety k 2)) (a : Fin 6 → k) :
    H t * carrierNegativeRootProduct (k := k) a =
      carrierNegativeRootProduct (moveNegativeParams t a) * H t := by
  have h := H_move_rootWord (k := k) t
    ([0, 1, 2, 3, 4, 5].map fun i : Fin 6 =>
      (-positiveConvexRoot i, a i))
  simpa [carrierNegativeRootProduct, carrierRootWordProduct, moveRootWord,
    moveNegativeParams, List.map_map, Function.comp_def] using h

private lemma longest_mul_canonical_exists (m : Fin 12) :
    ∃ j : Fin 12, ∃ t : Variety.Point (dVariety k 2),
      carrierWeylWord (k := k) (canonicalWeylWord 11) *
          carrierWeylWord (canonicalWeylWord m) =
        carrierWeylWord (canonicalWeylWord j) * H t := by
  let w := canonicalWeylWord 11 ++ canonicalWeylWord m
  obtain ⟨j, t, ht⟩ := exists_canonicalWeyl_normalForm (k := k)
    (w.map fun i => (i, false))
  refine ⟨j, t, ?_⟩
  rw [signedWord_unsigned] at ht
  rw [carrierWeylWord_append] at ht
  exact ht

/-- Every finite word in the twelve explicit G2 root curves terminates in an
ordered opposite-Borel normal form.  The negative and positive factors use
exactly six fixed slots, the Weyl factor is one of the twelve canonical
words, and the sole torus factor is a point of `dVariety k 2`. -/
public theorem exists_carrierRootWord_mixed_normalForm
    (word : List (Root × k)) :
    ∃ aNegative : Fin 6 → k, ∃ j : Fin 12,
      ∃ t : Variety.Point (dVariety k 2), ∃ aPositive : Fin 6 → k,
        carrierRootWordProduct word =
          carrierNegativeRootProduct aNegative *
            carrierWeylWord (k := k) (canonicalWeylWord j) *
              (splitTorusMorphism (k := k)).onPoints t *
              carrierPositiveRootProduct aPositive := by
  let longest := canonicalWeylWord 11
  let leadWord := carrierWeylInverseRootWord (k := k) longest
  obtain ⟨tLeft, aLeft, m, tRight, aRight, hcollected⟩ :=
    exists_carrierRootWord_borelWeyl_normalForm (k := k) (leadWord ++ word)
  have hprefix : carrierRootWordProduct (k := k) leadWord =
      (carrierWeylWord (k := k) longest)⁻¹ :=
    carrierWeylInverseRootWord_product longest
  have hshift : (carrierWeylWord (k := k) longest)⁻¹ *
      carrierRootWordProduct word =
        carrierPositiveBorelFactor tLeft aLeft *
          carrierWeylWord (canonicalWeylWord m) *
            carrierPositiveBorelFactor tRight aRight := by
    rw [← hprefix, ← carrierRootWordProduct_append]
    exact hcollected
  obtain ⟨sLeft, aNegative, hleft⟩ :=
    longest_conjugate_positiveBorel_exists (k := k) tLeft aLeft
  obtain ⟨j, sWeyl, hweyl⟩ := longest_mul_canonical_exists (k := k) m
  let movedNegative := moveNegativeParams sLeft aNegative
  have hmoveNegative :=
    H_move_negativeRootProduct (k := k) sLeft aNegative
  obtain ⟨sMoved, hmoveWeyl⟩ :=
    canonicalWeyl_torus_move_right_exists (k := k) j sLeft
  have hleft' : carrierWeylWord (k := k) longest *
        (H tLeft * carrierPositiveRootProduct aLeft) *
          (carrierWeylWord longest)⁻¹ =
      H sLeft * carrierNegativeRootProduct aNegative := by
    simpa only [longest, carrierPositiveBorelFactor, H] using hleft
  have hweyl' : carrierWeylWord (k := k) longest *
        carrierWeylWord (canonicalWeylWord m) =
      carrierWeylWord (canonicalWeylWord j) * H sWeyl := by
    simpa only [longest] using hweyl
  refine ⟨movedNegative, j, sMoved * sWeyl * tRight, aRight, ?_⟩
  change carrierRootWordProduct word =
    carrierNegativeRootProduct movedNegative *
      carrierWeylWord (canonicalWeylWord j) *
        H (sMoved * sWeyl * tRight) * carrierPositiveRootProduct aRight
  have hstart : carrierRootWordProduct (k := k) word =
      carrierWeylWord longest *
        (carrierPositiveBorelFactor tLeft aLeft *
          carrierWeylWord (canonicalWeylWord m) *
            carrierPositiveBorelFactor tRight aRight) := by
    rw [← hshift]
    group
  rw [hstart]
  change carrierWeylWord longest *
      ((H tLeft * carrierPositiveRootProduct aLeft) *
        carrierWeylWord (canonicalWeylWord m) *
          (H tRight * carrierPositiveRootProduct aRight)) = _
  calc
    _ = (carrierWeylWord longest * (H tLeft * carrierPositiveRootProduct aLeft) *
          (carrierWeylWord longest)⁻¹) *
        (carrierWeylWord longest * carrierWeylWord (canonicalWeylWord m)) *
          (H tRight * carrierPositiveRootProduct aRight) := by group
    _ = (H sLeft * carrierNegativeRootProduct aNegative) *
        (carrierWeylWord (canonicalWeylWord j) * H sWeyl) *
          (H tRight * carrierPositiveRootProduct aRight) := by rw [hleft', hweyl']
    _ = (carrierNegativeRootProduct movedNegative * H sLeft) *
        (carrierWeylWord (canonicalWeylWord j) * H sWeyl) *
          (H tRight * carrierPositiveRootProduct aRight) := by rw [hmoveNegative]
    _ = carrierNegativeRootProduct movedNegative *
        (H sLeft * carrierWeylWord (canonicalWeylWord j)) *
          (H sWeyl * H tRight) * carrierPositiveRootProduct aRight := by group
    _ = carrierNegativeRootProduct movedNegative *
        (carrierWeylWord (canonicalWeylWord j) * H sMoved) *
          (H sWeyl * H tRight) * carrierPositiveRootProduct aRight := by
            rw [hmoveWeyl]
    _ = carrierNegativeRootProduct movedNegative *
        carrierWeylWord (canonicalWeylWord j) *
          H (sMoved * sWeyl * tRight) * carrierPositiveRootProduct aRight := by
            calc
              _ = carrierNegativeRootProduct movedNegative *
                  carrierWeylWord (canonicalWeylWord j) *
                    ((H sMoved * H sWeyl) * H tRight) *
                      carrierPositiveRootProduct aRight := by group
              _ = carrierNegativeRootProduct movedNegative *
                  carrierWeylWord (canonicalWeylWord j) *
                    (H (sMoved * sWeyl) * H tRight) *
                      carrierPositiveRootProduct aRight := by rw [H_mul]
              _ = _ := by rw [H_mul]

end Theory.AlgebraicGroup.G2Chevalley
