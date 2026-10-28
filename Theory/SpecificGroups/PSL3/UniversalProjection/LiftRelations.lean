module

public import Theory.SpecificGroups.PSL3.UniversalProjection.LiftRelations.Tori

/-!
# Steinberg relations for the degree-three commutator lifts

In a central extension of PSL₃, preimages of one root group commute: one
preimage can be replaced by a commutator whose factors commute with the other
preimage modulo the central kernel. For distinct distant roots, conjugation
by a separating diagonal element and additivity kill their central commutator.
This proves additivity of the published commutator lifts.

For a three-index pair, write B(a,b) for the commutator of root preimages.
Choose a diagonal element scaling the first root by d ≠ 1 and fixing the
second. Since B(v,b) and B(v*b,1) have the same projective image, their
commutators with a lift of this diagonal element agree. Expanding gives
B((d-1)*v,b) = B((d-1)*v*b,1), which proves the exact chain relation.
This retains the original rootLift and works for every central extension,
without finiteness or perfectness of the covering group.

Source: Steinberg, *Lectures on Chevalley Groups*, Sections 6–7,
Theorems 9–10, especially the torus argument in steps (5a) and (8),
`refs/KGroup/GLS3/Chapter2St1.tex`, printed pp.74, 82–84. The field restrictions
are precisely the ordinary degree-three cases in GLS98 6.1.4. Faithfulness
of the elementary presentation remains independent of these lifted relations.
-/

@[expose] public section

open scoped MatrixGroups commutatorElement
open Theory.SpecificGroups.LinearHigher
namespace Matrix.PSL3.UniversalProjection

section General
variable {E B : Type*} [Group E] [Group B]

private theorem commutator_mul_center (z w a b : E)
    (hz : z ∈ Subgroup.center E) (hw : w ∈ Subgroup.center E) :
    ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  have hzC (x : E) : Commute z x := (Subgroup.mem_center_iff.mp hz x).symm
  have hwC (x : E) : Commute w x := (Subgroup.mem_center_iff.mp hw x).symm
  rw [commutatorElement_mul_left_eq_conj_mul, (hzC (w * b)).commutator_eq]
  simp only [mul_one, (hzC ⁅a, w * b⁆).eq, mul_inv_cancel_right]
  rw [commutatorElement_mul_right_eq_mul_conj, (hwC a).symm.commutator_eq]
  simp only [one_mul, (hwC ⁅a, b⁆).eq, mul_inv_cancel_right]

private theorem commutator_eq_of_map_eq (f : E →* B)
    (hc : f.ker ≤ Subgroup.center E) {a b c d : E}
    (hac : f a = f c) (hbd : f b = f d) : ⁅a, b⁆ = ⁅c, d⁆ := by
  have hz : a * c⁻¹ ∈ Subgroup.center E := hc (by simp [MonoidHom.mem_ker, hac])
  have hw : b * d⁻¹ ∈ Subgroup.center E := hc (by simp [MonoidHom.mem_ker, hbd])
  simpa only [inv_mul_cancel_right] using commutator_mul_center (a * c⁻¹) (b * d⁻¹) c d hz hw

private theorem commute_commutator_of_map_commute (f : E →* B)
    (hc : f.ker ≤ Subgroup.center E) {a b c : E}
    (hab : Commute (f a) (f b)) (hac : Commute (f a) (f c)) :
    Commute a ⁅b, c⁆ := by
  have hb : f (a * b * a⁻¹) = f b := by
    rw [map_mul, map_mul, map_inv, hab.eq, mul_inv_cancel_right]
  have hd : f (a * c * a⁻¹) = f c := by
    rw [map_mul, map_mul, map_inv, hac.eq, mul_inv_cancel_right]
  have hh := commutator_eq_of_map_eq f hc hb hd
  rw [← conjugate_commutatorElement] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

end General

variable {F E : Type*} [Field F] [Group E]
variable (f : E →* PSL(3,F)) (hf : Function.Surjective f)
  (hc : f.ker ≤ Subgroup.center E)

include hf hc in
/-- Preimages of any one root group commute, over every field. -/
theorem commute_of_same_root_images (r : Root 3) (a b : F) {x y : E}
    (hx : f x = projectiveRoot r a) (hy : f y = projectiveRoot r b) : Commute x y := by
  apply commutatorElement_eq_one_iff_commute.mp
  rw [commutator_eq_of_map_eq f hc rfl (hy.trans (rootLift_map f hf r b).symm)]
  apply Commute.commutator_eq
  unfold rootLift
  apply commute_commutator_of_map_commute f hc
  · rw [hx, rootPreimage_map]
    exact commutatorElement_eq_one_iff_commute.mp
      (projectiveRoot_relations.distant _ _ _ _ r.property.symm (auxiliary_ne_left r))
  · rw [hx, rootPreimage_map]
    exact commutatorElement_eq_one_iff_commute.mp
      (projectiveRoot_relations.distant _ _ _ _ (auxiliary_ne_right r).symm r.property.symm)

/-- The commutator pairing on two root groups. -/
private noncomputable def rootPair (r s : Root 3) (a b : F) : E :=
  ⁅rootPreimage f hf r a, rootPreimage f hf s b⁆

include hc in
private theorem rootPair_eq (r s : Root 3) (a b : F) {x y : E}
    (hx : f x = projectiveRoot r a) (hy : f y = projectiveRoot s b) :
    rootPair f hf r s a b = ⁅x,y⁆ :=
  commutator_eq_of_map_eq f hc ((rootPreimage_map _ _ _ _).trans hx.symm)
    ((rootPreimage_map _ _ _ _).trans hy.symm)

private theorem rootPair_map (r s : Root 3) (a b : F) :
    f (rootPair f hf r s a b) = ⁅projectiveRoot r a, projectiveRoot s b⁆ := by
  simp only [rootPair, map_commutatorElement, rootPreimage_map]

include hc in
private theorem rootPair_add_left (r s : Root 3) (a b c : F)
    (h : Commute (rootPreimage f hf r a) (rootPair f hf r s b c)) :
    rootPair f hf r s (a+b) c = rootPair f hf r s b c * rootPair f hf r s a c := by
  rw [rootPair_eq f hf hc r s (a+b) c
    (show f (rootPreimage f hf r a * rootPreimage f hf r b) = _ by
      rw [map_mul, rootPreimage_map, rootPreimage_map, projectiveRoot_relations.add])
    (rootPreimage_map f hf s c)]
  rw [commutatorElement_mul_left_eq_conj_mul]
  change rootPreimage f hf r a * rootPair f hf r s b c * (rootPreimage f hf r a)⁻¹ *
    rootPair f hf r s a c = rootPair f hf r s b c * rootPair f hf r s a c
  rw [show rootPreimage f hf r a * rootPair f hf r s b c =
    rootPair f hf r s b c * rootPreimage f hf r a from h.eq, mul_inv_cancel_right]

include hc in
private theorem rootPair_conj (r s : Root 3) (a b d : F) (t : E)
    (hr : ∀ a, f t * projectiveRoot r a * (f t)⁻¹ = projectiveRoot r (d*a))
    (hs : ∀ b, f t * projectiveRoot s b * (f t)⁻¹ = projectiveRoot s b) :
    t * rootPair f hf r s a b * t⁻¹ = rootPair f hf r s (d*a) b := by
  rw [rootPair, conjugate_commutatorElement]
  exact (rootPair_eq f hf hc r s (d*a) b
    (by rw [map_mul, map_mul, map_inv, rootPreimage_map, hr])
    (by rw [map_mul, map_mul, map_inv, rootPreimage_map, hs])).symm

include hc in
private theorem rootPair_center (r s : Root 3) (a b : F)
    (hrs : r.val.2 ≠ s.val.1) (hsr : s.val.2 ≠ r.val.1) :
    rootPair f hf r s a b ∈ Subgroup.center E := by
  apply hc
  rw [MonoidHom.mem_ker, rootPair_map]
  exact projectiveRoot_relations.distant r s a b hrs hsr

include hc in
private theorem rootPair_eq_one_of_torus (r s : Root 3)
    (hrs : r.val.2 ≠ s.val.1) (hsr : s.val.2 ≠ r.val.1)
    (d : F) (hd : d ≠ 1) (t : E)
    (hr : ∀ a, f t * projectiveRoot r a * (f t)⁻¹ = projectiveRoot r (d*a))
    (hs : ∀ b, f t * projectiveRoot s b * (f t)⁻¹ = projectiveRoot s b)
    (a b : F) : rootPair f hf r s a b = 1 := by
  have hinv (v : F) : rootPair f hf r s (d*v) b = rootPair f hf r s v b := by
    rw [← rootPair_conj f hf hc r s v b d t hr hs]
    rw [Subgroup.mem_center_iff.mp (rootPair_center f hf hc r s v b hrs hsr) t,
      mul_inv_cancel_right]
  let v := a / (d-1)
  have hda : d*v = v+a := by
    dsimp [v]
    field_simp [sub_ne_zero.mpr hd]
    ring
  have hc' : Commute (rootPreimage f hf r v) (rootPair f hf r s a b) :=
    Subgroup.mem_center_iff.mp (rootPair_center f hf hc r s a b hrs hsr) _
  have hh := rootPair_add_left f hf hc r s v a b hc'
  rw [← hda, hinv] at hh
  exact mul_right_cancel (hh.symm.trans (one_mul _).symm)

include hf hc in
/-- The separating torus kills the central error between distant roots. -/
theorem commute_of_root_images_of_tori (htori : SeparatingTori F)
    (r s : Root 3) (a b : F) {x y : E}
    (hx : f x = projectiveRoot r a) (hy : f y = projectiveRoot s b)
    (hrs : r.val.2 ≠ s.val.1) (hsr : s.val.2 ≠ r.val.1) : Commute x y := by
  by_cases he : r = s
  · subst s
    exact commute_of_same_root_images f hf hc r a b hx hy
  obtain ⟨d,t,hd,hr,hs⟩ := htori r s he (Or.inl hsr.symm)
  obtain ⟨z,hz⟩ := hf t
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← rootPair_eq f hf hc r s a b hx hy]
  exact rootPair_eq_one_of_torus f hf hc r s hrs hsr d hd z
    (by simpa only [hz] using hr) (by simpa only [hz] using hs) a b

include hc in
/-- Additivity of the commutator lifts follows from distant commutation. -/
theorem rootLift_add_of_tori (htori : SeparatingTori F) (r : Root 3) (a b : F) :
    rootLift f hf r a * rootLift f hf r b = rootLift f hf r (a+b) := by
  let p := root r.val.1 (auxiliary r) (auxiliary_ne_left r).symm
  let q := root (auxiliary r) r.val.2 (auxiliary_ne_right r)
  have hc' : Commute (rootPreimage f hf p a) (rootPair f hf p q b 1) := by
    apply commute_of_root_images_of_tori f hf hc htori p r a b
      (rootPreimage_map f hf p a)
    · exact rootLift_map f hf r b
    · exact auxiliary_ne_left r
    · exact r.property.symm
  have hh := rootPair_add_left f hf hc p q a b 1 hc'
  change rootLift f hf r (a+b) = rootLift f hf r b * rootLift f hf r a at hh
  rw [hh]
  exact (commute_of_same_root_images f hf hc r a b
    (rootLift_map f hf r a) (rootLift_map f hf r b)).eq

private theorem rootLift_eq_pair (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a : F) :
    rootLift f hf (root i k hik) a =
      rootPair f hf (root i j hij) (root j k hjk) a 1 := by
  have hl := auxiliary_ne_left (root i k hik)
  have hr := auxiliary_ne_right (root i k hik)
  change auxiliary (root i k hik) ≠ i at hl
  change auxiliary (root i k hik) ≠ k at hr
  have hj : auxiliary (root i k hik) = j := by omega
  dsimp only [root] at hj
  simp only [rootLift, rootPair, root, hj]

include hc in
private theorem rootPair_chain_balance (htori : SeparatingTori F) (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : F) :
    rootPair f hf (root i j hij) (root j k hjk) a b =
      rootPair f hf (root i j hij) (root j k hjk) (a*b) 1 := by
  let p := root i j hij
  let q := root j k hjk
  let r := root i k hik
  have hpq (a b : F) : f (rootPair f hf p q a b) = projectiveRoot r (a*b) := by
    rw [rootPair_map]
    exact projectiveRoot_relations.chain i j k hij hjk hik a b
  have hadd (a b c : F) : rootPair f hf p q (a+b) c =
      rootPair f hf p q b c * rootPair f hf p q a c := by
    apply rootPair_add_left f hf hc
    exact commute_of_root_images_of_tori f hf hc htori p r a (b*c)
      (rootPreimage_map f hf p a) (hpq b c) hij.symm hik.symm
  have hpne : p ≠ q := fun h => hij (congrArg (fun r : Root 3 => r.val.1) h)
  obtain ⟨d,t,hd,htp,htq⟩ := htori p q hpne (Or.inl hik)
  obtain ⟨z,hz⟩ := hf t
  have hconj (a b : F) : z * rootPair f hf p q a b * z⁻¹ =
      rootPair f hf p q (d*a) b :=
    rootPair_conj f hf hc p q a b d z
      (by simpa only [hz] using htp) (by simpa only [hz] using htq)
  let v := a / (d-1)
  have hda : d*v = v+a := by
    dsimp [v]
    field_simp [sub_ne_zero.mpr hd]
    ring
  have hmap : f (rootPair f hf p q v b) = f (rootPair f hf p q (v*b) 1) := by
    rw [hpq, hpq, mul_one]
  have hh := commutator_eq_of_map_eq f hc (a := z) rfl hmap
  simp only [commutatorElement_def] at hh
  rw [hconj, hconj, hda, show d*(v*b) = v*b+a*b by rw [← mul_assoc, hda, add_mul],
    hadd, hadd, mul_inv_cancel_right, mul_inv_cancel_right] at hh
  exact hh

include hc in
/-- The three-index relation for the specified commutator lifts. -/
theorem rootLift_chain_of_tori (htori : SeparatingTori F) (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : F) :
    ⁅rootLift f hf (root i j hij) a, rootLift f hf (root j k hjk) b⁆ =
      rootLift f hf (root i k hik) (a*b) := by
  rw [← rootPair_eq f hf hc _ _ a b (rootLift_map f hf _ a) (rootLift_map f hf _ b),
    rootLift_eq_pair f hf i j k hij hjk hik]
  exact rootPair_chain_balance f hf hc htori i j k hij hjk hik a b

include hc in
/-- The finite-field calculation reduces to actual separating diagonal elements. -/
theorem rootLift_relations_of_tori (htori : SeparatingTori F) :
    Relations (rootLift f hf) where
  add := rootLift_add_of_tori f hf hc htori
  distant r s a b hrs hsr :=
    (commute_of_root_images_of_tori f hf hc htori r s a b
      (rootLift_map f hf r a) (rootLift_map f hf s b) hrs hsr).commutator_eq
  chain := rootLift_chain_of_tori f hf hc htori

include hc in
/-- All Steinberg relations for the specified lifts in an arbitrary central
extension, at every ordinary degree-three finite-field parameter. -/
theorem rootLift_relations [Finite F] (h2 : Nat.card F ≠ 2) (h4 : Nat.card F ≠ 4) :
    Relations (rootLift f hf) :=
  rootLift_relations_of_tori f hf hc (separatingTori_of_card_ne h2 h4)

/-- The exact finite quasisimple covering input consumed by universality. -/
theorem covering_rootLift_relations [Finite F] (h2 : Nat.card F ≠ 2)
    (h4 : Nat.card F ≠ 4) {M : Type*} [Group M] [Finite M]
    [Theory.GroupTheory.IsQuasisimple M]
    (g : Theory.GroupTheory.Covering M PSL(3,F)) :
    Relations (rootLift g.toMonoidHom g.surjective) :=
  rootLift_relations g.toMonoidHom g.surjective g.ker_le_center h2 h4

include hf hc in
/-- The actual projection square now requires only faithfulness of the
matrix presentation; the lifted relations are discharged here. -/
theorem existsUnique_lift_of_faithful [Finite F]
    (h2 : Nat.card F ≠ 2) (h4 : Nat.card F ≠ 4)
    (hinj : Function.Injective (matrixMap (n := 3) (F := F))) :
    ∃! s : SL(3,F) →* E, f.comp s = projection F :=
  existsUnique_lift_of_faithful_of_relations hinj f hf hc
    (rootLift_relations f hf hc h2 h4)

end Matrix.PSL3.UniversalProjection
