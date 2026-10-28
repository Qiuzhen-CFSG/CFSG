module

public import Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime.LocalSection
public import Theory.SpecificGroups.LinearHigher.TorusAction
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Compatible degree-four root lifts over fields of order greater than three

In any central extension of the literal PSL₄, define a root lift as the
commutator of preimages of two elementary roots through a third coordinate.
Centrality makes the commutator independent of the representatives. A unit
whose square is not one supplies separating tori: put the unit and its inverse
at the two coordinates outside a fixed root. The actual projective torus-word
formula proves that this torus fixes that root and scales each distinct,
nonopposite root nontrivially, including roots with disjoint support.

The resulting commutator pairing is additive and balanced in its coefficients.
Unlike degree three, a root has two possible intermediate coordinates. To
compare them, conjugate both pairings by the torus on the root's endpoints.
Both scale by the same nontrivial square. Their equal projective images and
additivity then force equality in the extension. This proves all three
families of elementary relations for one fixed root family.

The final application uses the positive-subgroup section and transfer in
`LocalSection` to exclude the defining prime from every finite perfect central
kernel. It covers every prime greater than three, including the larger Fermat
primes in Aschbacher–Smith I.1.4(3). Global presentation faithfulness and the
remaining canonical-universal assembly are independent.

Source: Steinberg, *Lectures on Chevalley Groups*, §7, Theorem 10, steps (2)–(8),
`refs/KGroup/GLS3/Chapter2St1.tex`, printed pp.81–84; GLS3 §6.1; and
`refs/quasithin.pdf`, I.1.1 and I.1.4(3), printed pp.407–408. The central
commutator calculations adapt the existing degree-three development in
`PSL3/UniversalProjection/Lifts.lean` and `LiftRelations.lean`.
-/

public section

open scoped MatrixGroups commutatorElement
open Theory.SpecificGroups.LinearHigher Theory.SpecificGroups.LinearHigher.SteinbergWords
namespace Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime.RootLiftsFermat
variable {F : Type*} [Field F]

private def SeparatingTori (F : Type*) [Field F] : Prop :=
  ∀ r s : Root 4, r ≠ s → (r.val.1 ≠ s.val.2 ∨ r.val.2 ≠ s.val.1) →
    ∃ (d : F) (t : PSL(4,F)), d ≠ 1 ∧
      (∀ a, t * projectiveRoot r a * t⁻¹ = projectiveRoot r (d*a)) ∧
      (∀ b, t * projectiveRoot s b * t⁻¹ = projectiveRoot s b)

private theorem exists_unit_sq_ne_one [Finite F] (hF : 3 < Nat.card F) :
    ∃ u : Fˣ, u ^ 2 ≠ 1 := by
  let := Fintype.ofFinite F
  by_contra! h
  have hd := (FiniteField.forall_pow_eq_one_iff F 2).mp h
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
  rw [Nat.card_eq_fintype_card] at hF
  omega

private theorem fourth_coordinate (i j k : Fin 4) : ∃ l, l ≠ i ∧ l ≠ j ∧ l ≠ k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

private theorem torus_conj (i j : Fin 4) (hij : i ≠ j) (u : Fˣ) (r : Root 4) (a : F) :
    torusWord projectiveRoot i j hij u * projectiveRoot r a *
      (torusWord projectiveRoot i j hij u)⁻¹ =
    projectiveRoot r ((rootWeight i j u r : F) * a) :=
  torusWord_conj_generator projectiveRoot_relations (by decide) i j hij u r a

/-- The two coordinates outside `s` give weights `u`, `u⁻¹`, `u²`, or `u⁻²`
on every distinct, nonopposite root. -/
private theorem separatingTori_of_unit (u : Fˣ) (hu : u^2 ≠ 1) : SeparatingTori F := by
  have hu1 : u ≠ 1 := fun h => hu (by simp [h])
  have hui : u⁻¹ ≠ 1 := by simpa using hu1
  have hui2 : u⁻¹^2 ≠ 1 := by
    intro h
    apply hu
    exact inv_eq_one.mp (by simpa only [inv_pow] using h)
  intro r s hrs hnopp
  have hne : r.val.1 ≠ s.val.1 ∨ r.val.2 ≠ s.val.2 := by
    by_contra! h
    exact hrs (Subtype.ext (Prod.ext h.1 h.2))
  have hm : ∃ m : Fin 4, (r.val.1 = m ∨ r.val.2 = m) ∧
      m ≠ s.val.1 ∧ m ≠ s.val.2 := by
    have hrr := r.property
    have hss := s.property
    by_cases h1 : r.val.1 ≠ s.val.1 ∧ r.val.1 ≠ s.val.2
    · exact ⟨r.val.1, Or.inl rfl, h1⟩
    · exact ⟨r.val.2, Or.inr rfl, by omega⟩
  obtain ⟨m,hrm,hms1,hms2⟩ := hm
  obtain ⟨n,hns1,hns2,hnm⟩ := fourth_coordinate s.val.1 s.val.2 m
  let t : PSL(4,F) := torusWord projectiveRoot m n hnm.symm u
  refine ⟨(rootWeight m n u r : F), t, ?_, ?_, ?_⟩
  · intro h
    have hw : rootWeight m n u r = 1 := Units.ext h
    rcases hrm with hr1 | hr2
    · have hr2 : r.val.2 ≠ m := by rw [← hr1]; exact r.property.symm
      by_cases hrn : r.val.2 = n
      · apply hu
        simpa [rootWeight, torusWeight, hr1, hr2, hrn, hnm, div_eq_mul_inv, ← pow_two] using hw
      · apply hu1
        simpa [rootWeight, torusWeight, hr1, hr2, hrn] using hw
    · have hr1 : r.val.1 ≠ m := by rw [← hr2]; exact r.property
      by_cases hrn : r.val.1 = n
      · apply hui2
        simpa [rootWeight, torusWeight, hr1, hr2, hrn, hnm, div_eq_mul_inv, ← pow_two] using hw
      · apply hui
        simpa [rootWeight, torusWeight, hr1, hr2, hrn] using hw
  · intro a
    exact torus_conj m n hnm.symm u r a
  · intro b
    rw [torus_conj]
    simp [rootWeight, torusWeight, hms1.symm, hms2.symm, hns1.symm, hns2.symm]

variable {E : Type*} [Group E]

/-- The third coordinate outside a degree-four root. -/
private noncomputable def auxiliary (r : Root 4) : Fin 4 :=
  Classical.choose (Fin.exists_ne_and_ne_of_two_lt r.val.1 r.val.2 (by decide : 2 < 4))

private theorem auxiliary_ne_left (r : Root 4) : auxiliary r ≠ r.val.1 :=
  (Classical.choose_spec
    (Fin.exists_ne_and_ne_of_two_lt r.val.1 r.val.2 (by decide : 2 < 4))).1

private theorem auxiliary_ne_right (r : Root 4) : auxiliary r ≠ r.val.2 :=
  (Classical.choose_spec
    (Fin.exists_ne_and_ne_of_two_lt r.val.1 r.val.2 (by decide : 2 < 4))).2

private noncomputable def rootPreimage (f : E →* PSL(4, F)) (hf : Function.Surjective f)
    (r : Root 4) (a : F) : E := Classical.choose (hf (projectiveRoot r a))

@[simp] private theorem rootPreimage_map (f : E →* PSL(4, F)) (hf : Function.Surjective f)
    (r : Root 4) (a : F) : f (rootPreimage f hf r a) = projectiveRoot r a :=
  Classical.choose_spec (hf _)

/-- Lift a root by a commutator through a fixed auxiliary coordinate. -/
noncomputable def rootLift (f : E →* PSL(4, F)) (hf : Function.Surjective f)
    (r : Root 4) (a : F) : E :=
  ⁅rootPreimage f hf (root r.val.1 (auxiliary r) (auxiliary_ne_left r).symm) a,
    rootPreimage f hf (root (auxiliary r) r.val.2 (auxiliary_ne_right r)) 1⁆

@[simp] theorem rootLift_map (f : E →* PSL(4, F)) (hf : Function.Surjective f)
    (r : Root 4) (a : F) : f (rootLift f hf r a) = projectiveRoot r a := by
  rcases r with ⟨⟨i, j⟩, hij⟩
  rw [rootLift, map_commutatorElement, rootPreimage_map, rootPreimage_map]
  change _ = projectiveRoot (root i j hij) a
  simpa only [mul_one] using projectiveRoot_relations.chain i (auxiliary ⟨(i, j), hij⟩) j
    (auxiliary_ne_left ⟨(i, j), hij⟩).symm (auxiliary_ne_right ⟨(i, j), hij⟩) hij a (1 : F)

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

variable (f : E →* PSL(4,F)) (hf : Function.Surjective f)
  (hc : f.ker ≤ Subgroup.center E)

include hf hc in
/-- Preimages of any one root group commute, over every field. -/
private theorem commute_of_same_root_images (r : Root 4) (a b : F) {x y : E}
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
private noncomputable def rootPair (r s : Root 4) (a b : F) : E :=
  ⁅rootPreimage f hf r a, rootPreimage f hf s b⁆

include hc in
private theorem rootPair_eq (r s : Root 4) (a b : F) {x y : E}
    (hx : f x = projectiveRoot r a) (hy : f y = projectiveRoot s b) :
    rootPair f hf r s a b = ⁅x,y⁆ :=
  commutator_eq_of_map_eq f hc ((rootPreimage_map _ _ _ _).trans hx.symm)
    ((rootPreimage_map _ _ _ _).trans hy.symm)

private theorem rootPair_map (r s : Root 4) (a b : F) :
    f (rootPair f hf r s a b) = ⁅projectiveRoot r a, projectiveRoot s b⁆ := by
  simp only [rootPair, map_commutatorElement, rootPreimage_map]

include hc in
private theorem rootPair_add_left (r s : Root 4) (a b c : F)
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
private theorem rootPair_conj (r s : Root 4) (a b d : F) (t : E)
    (hr : ∀ a, f t * projectiveRoot r a * (f t)⁻¹ = projectiveRoot r (d*a))
    (hs : ∀ b, f t * projectiveRoot s b * (f t)⁻¹ = projectiveRoot s b) :
    t * rootPair f hf r s a b * t⁻¹ = rootPair f hf r s (d*a) b := by
  rw [rootPair, conjugate_commutatorElement]
  exact (rootPair_eq f hf hc r s (d*a) b
    (by rw [map_mul, map_mul, map_inv, rootPreimage_map, hr])
    (by rw [map_mul, map_mul, map_inv, rootPreimage_map, hs])).symm

include hc in
private theorem rootPair_center (r s : Root 4) (a b : F)
    (hrs : r.val.2 ≠ s.val.1) (hsr : s.val.2 ≠ r.val.1) :
    rootPair f hf r s a b ∈ Subgroup.center E := by
  apply hc
  rw [MonoidHom.mem_ker, rootPair_map]
  exact projectiveRoot_relations.distant r s a b hrs hsr

include hc in
private theorem rootPair_eq_one_of_torus (r s : Root 4)
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
private theorem commute_of_root_images_of_tori (htori : SeparatingTori F)
    (r s : Root 4) (a b : F) {x y : E}
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
private theorem rootLift_add_of_tori (htori : SeparatingTori F) (r : Root 4) (a b : F) :
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

include hc in
private theorem rootPair_chain_balance (htori : SeparatingTori F) (i j k : Fin 4)
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
  have hpne : p ≠ q := fun h => hij (congrArg (fun r : Root 4 => r.val.1) h)
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
private theorem rootPair_conj_both (r s : Root 4) (a b d e : F) (t : E)
    (hr : ∀ a, f t * projectiveRoot r a * (f t)⁻¹ = projectiveRoot r (d*a))
    (hs : ∀ b, f t * projectiveRoot s b * (f t)⁻¹ = projectiveRoot s (e*b)) :
    t * rootPair f hf r s a b * t⁻¹ = rootPair f hf r s (d*a) (e*b) := by
  rw [rootPair, conjugate_commutatorElement]
  exact (rootPair_eq f hf hc r s (d*a) (e*b)
    (by rw [map_mul, map_mul, map_inv, rootPreimage_map, hr])
    (by rw [map_mul, map_mul, map_inv, rootPreimage_map, hs])).symm

private theorem rootWeight_chain (m n : Fin 4) (u : Fˣ) (i j k : Fin 4)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    rootWeight m n u (root i j hij) * rootWeight m n u (root j k hjk) =
      rootWeight m n u (root i k hik) :=
  div_mul_div_cancel _ _ _

include hc in
private theorem rootPair_chain_conj (htori : SeparatingTori F)
    (i j k : Fin 4) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (m n : Fin 4) (hmn : m ≠ n) (u : Fˣ) (z : E)
    (hz : f z = torusWord projectiveRoot m n hmn u) (a : F) :
    z * rootPair f hf (root i j hij) (root j k hjk) a 1 * z⁻¹ =
      rootPair f hf (root i j hij) (root j k hjk)
        ((rootWeight m n u (root i k hik) : F)*a) 1 := by
  rw [rootPair_conj_both f hf hc _ _ a 1
    (rootWeight m n u (root i j hij) : F) (rootWeight m n u (root j k hjk) : F) z
    (by intro a; rw [hz]; exact torus_conj m n hmn u _ a)
    (by intro b; rw [hz]; exact torus_conj m n hmn u _ b),
    rootPair_chain_balance f hf hc htori i j k hij hjk hik]
  congr 1
  rw [mul_one, mul_right_comm, ← Units.val_mul,
    rootWeight_chain m n u i j k hij hjk hik]

include hc in
private theorem equal_of_same_map_of_scaling (A B : F → E) (d : F) (hd : d ≠ 1)
    (z : E) (hmap : ∀ a, f (A a) = f (B a))
    (hA : ∀ a b, A (a+b) = A b * A a)
    (hB : ∀ a b, B (a+b) = B b * B a)
    (hconjA : ∀ a, z * A a * z⁻¹ = A (d*a))
    (hconjB : ∀ a, z * B a * z⁻¹ = B (d*a)) (a : F) : A a = B a := by
  let v := a / (d-1)
  have hda : d*v = v+a := by
    dsimp [v]
    field_simp [sub_ne_zero.mpr hd]
    ring
  have hh := commutator_eq_of_map_eq f hc (a := z) rfl (hmap v)
  simp only [commutatorElement_def] at hh
  rw [hconjA, hconjB, hda, hA, hB, mul_inv_cancel_right,
    mul_inv_cancel_right] at hh
  exact hh

include hc in
/-- The endpoint torus compares the two possible intermediate coordinates.
Its common nontrivial square weight removes the possible central discrepancy. -/
private theorem rootLift_eq_pair (htori : SeparatingTori F)
    (u : Fˣ) (hu : u^2 ≠ 1) (i j k : Fin 4)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a : F) :
    rootLift f hf (root i k hik) a =
      rootPair f hf (root i j hij) (root j k hjk) a 1 := by
  let l := auxiliary (root i k hik)
  have hil : i ≠ l := (auxiliary_ne_left (root i k hik)).symm
  have hlk : l ≠ k := auxiliary_ne_right (root i k hik)
  change rootPair f hf (root i l hil) (root l k hlk) a 1 = _
  obtain ⟨z,hz⟩ := hf (torusWord projectiveRoot i k hik u)
  have hd : (u : F)^2 ≠ 1 := fun h => hu (Units.ext h)
  have hadd (j : Fin 4) (hij : i ≠ j) (hjk : j ≠ k) (a b : F) :
      rootPair f hf (root i j hij) (root j k hjk) (a+b) 1 =
        rootPair f hf (root i j hij) (root j k hjk) b 1 *
        rootPair f hf (root i j hij) (root j k hjk) a 1 := by
    apply rootPair_add_left f hf hc
    apply commute_of_root_images_of_tori f hf hc htori (root i j hij)
      (root i k hik) a (b*1) (rootPreimage_map _ _ _ _)
    · rw [rootPair_map]
      exact projectiveRoot_relations.chain i j k hij hjk hik b 1
    · exact hij.symm
    · exact hik.symm
  have hconj (j : Fin 4) (hij : i ≠ j) (hjk : j ≠ k) (a : F) :
      z * rootPair f hf (root i j hij) (root j k hjk) a 1 * z⁻¹ =
        rootPair f hf (root i j hij) (root j k hjk) ((u : F)^2*a) 1 := by
    simpa [rootWeight, torusWeight, root, hik, hik.symm, div_eq_mul_inv,
      ← pow_two] using
      rootPair_chain_conj f hf hc htori i j k hij hjk hik i k hik u z hz a
  apply equal_of_same_map_of_scaling f hc _ _ ((u : F)^2) hd z
    (fun a => ?_) (hadd l hil hlk) (hadd j hij hjk) (hconj l hil hlk) (hconj j hij hjk) a
  rw [rootPair_map, rootPair_map,
    projectiveRoot_relations.chain i l k hil hlk hik,
    projectiveRoot_relations.chain i j k hij hjk hik]

include hc in
/-- The three-index relation is independent of the intermediate coordinate. -/
private theorem rootLift_chain_of_unit (u : Fˣ) (hu : u^2 ≠ 1) (i j k : Fin 4)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : F) :
    ⁅rootLift f hf (root i j hij) a, rootLift f hf (root j k hjk) b⁆ =
      rootLift f hf (root i k hik) (a*b) := by
  let htori := separatingTori_of_unit u hu
  rw [← rootPair_eq f hf hc _ _ a b (rootLift_map f hf _ a) (rootLift_map f hf _ b),
    rootLift_eq_pair f hf hc htori u hu i j k hij hjk hik]
  exact rootPair_chain_balance f hf hc htori i j k hij hjk hik a b

include hc in
/-- All elementary relations in an arbitrary central extension of PSL₄. -/
theorem rootLift_relations_of_unit (u : Fˣ) (hu : u^2 ≠ 1) :
    Relations (rootLift f hf) where
  add := rootLift_add_of_tori f hf hc (separatingTori_of_unit u hu)
  distant r s a b hrs hsr :=
    (commute_of_root_images_of_tori f hf hc (separatingTori_of_unit u hu) r s a b
      (rootLift_map f hf r a) (rootLift_map f hf s b) hrs hsr).commutator_eq
  chain := rootLift_chain_of_unit f hf hc u hu

include hc in
/-- The finite-field restriction supplies the required nontrivial square. -/
theorem rootLift_relations [Finite F] (hF : 3 < Nat.card F) :
    Relations (rootLift f hf) := by
  obtain ⟨u,hu⟩ := exists_unit_sq_ne_one hF
  exact rootLift_relations_of_unit f hf hc u hu

end Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime.RootLiftsFermat

namespace Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime

universe u
variable {F : Type u} [Field F] [Finite F] {p : ℕ}

/-- The required prime-kernel root lifts, for every field order greater
than three. In fact the construction works for every central extension. -/
theorem primeKernelRootLifts_of_three_lt (hF : Nat.card F = p) (hp3 : 3 < p) :
    PrimeKernelRootLifts F p := by
  intro E _ _ c _
  refine ⟨RootLiftsFermat.rootLift c.toMonoidHom c.surjective, ?_,
    RootLiftsFermat.rootLift_map c.toMonoidHom c.surjective⟩
  exact RootLiftsFermat.rootLift_relations c.toMonoidHom c.surjective c.ker_le_center
    (by simpa only [hF] using hp3)

/-- The defining-prime exclusion needed for the PSL₄ case of I.1.4(3), with
the stronger parameter range of all primes greater than three. -/
theorem not_dvd_kernel_of_three_lt (hp : p.Prime) (hF : Nat.card F = p)
    (hp3 : 3 < p) {E : Type u} [Group E] [Finite E]
    (c : PerfectCentralCovering.Cover E PSL(4,F)) :
    ¬ p ∣ Nat.card c.toMonoidHom.ker :=
  not_dvd_kernel_of_primeKernelRootLifts hp hF
    (primeKernelRootLifts_of_three_lt hF hp3) c

end Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime
