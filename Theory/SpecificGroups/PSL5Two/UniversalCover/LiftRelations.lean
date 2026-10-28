module

public import Theory.SpecificGroups.PSL5Two.UniversalCover.Lifts

/-!
# Steinberg relations for the binary degree-five commutator lifts

In a central extension of the actual matrix group PSL₅(2), arbitrary preimages
of distant roots commute. To prove this exact equality, choose a fifth index
outside the two roots: one root becomes a commutator whose two factors commute
with the other root modulo the central kernel. Central errors disappear from
that commutator.

The Hall–Witt identity on four distinct indices then makes the length-two
commutator independent of its intermediate index. This identifies the published
`rootLift` with the commutator through any third index and proves the chain
relation. The square relation follows by expanding the commutator of a central
square. Neither perfectness of the extension nor faithfulness of the Steinberg
presentation is needed.

The final theorem supplies these relations for the literal `universalProjection`.
Together with the separately proved presentation faithfulness, this is the input
to the universal-cover assembly for the PSL₅(2) case of Aschbacher–Smith I.1.3,
printed p.407, citing GLS98 §6.1 (especially 6.1.1–6.1.4).
-/

@[expose] public section

open scoped commutatorElement
namespace Theory.SpecificGroups.PSL5Two.UniversalCover

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
    (hker : f.ker ≤ Subgroup.center E) {a b c d : E}
    (hac : f a = f c) (hbd : f b = f d) : ⁅a, b⁆ = ⁅c, d⁆ := by
  have hz : a * c⁻¹ ∈ Subgroup.center E := hker (by simp [MonoidHom.mem_ker, hac])
  have hw : b * d⁻¹ ∈ Subgroup.center E := hker (by simp [MonoidHom.mem_ker, hbd])
  simpa only [inv_mul_cancel_right] using commutator_mul_center (a * c⁻¹) (b * d⁻¹) c d hz hw

private theorem commute_commutator_of_map_commute (f : E →* B)
    (hker : f.ker ≤ Subgroup.center E) {a b c : E}
    (hab : Commute (f a) (f b)) (hac : Commute (f a) (f c)) :
    Commute a ⁅b, c⁆ := by
  have hb : f (a * b * a⁻¹) = f b := by rw [map_mul, map_mul, map_inv, hab.eq, mul_inv_cancel_right]
  have hc : f (a * c * a⁻¹) = f c := by rw [map_mul, map_mul, map_inv, hac.eq, mul_inv_cancel_right]
  have hh := commutator_eq_of_map_eq f hker hb hc
  rw [← conjugate_commutatorElement] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh : a * ⁅b, c⁆ = ⁅b, c⁆ * a)

private theorem commutator_assoc_of_commute {a b c : E}
    (hac : Commute a c) (hde : Commute ⁅a, b⁆ ⁅b, c⁆)
    (het : Commute ⁅b, c⁆ ⁅⁅a, b⁆, c⁆) : ⁅⁅a, b⁆, c⁆ = ⁅a, ⁅b, c⁆⁆ := by
  have h := commutatorElement_commutatorElement_conj_mul a b c
  have hca : c * a * c⁻¹ = a := by rw [hac.symm.eq, mul_inv_cancel_right]
  have hbc : b * c * b⁻¹ = ⁅b, c⁆ * c := by simp [commutatorElement_def]
  rw [hac.symm.commutator_eq, commutatorElement_one_left, mul_one, hca, hbc,
    commutatorElement_mul_right_eq_mul_conj, hde.commutator_eq, one_mul,
    het.eq, mul_inv_cancel_right] at h
  exact (eq_inv_of_mul_eq_one_left h).trans (commutatorElement_inv _ _)
end General

private theorem exists_spare (i j k l : Fin 5) :
    ∃ m : Fin 5, m ≠ i ∧ m ≠ j ∧ m ≠ k ∧ m ≠ l := by
  have hc : ({i, j, k, l} : Finset (Fin 5)).card < (Finset.univ : Finset (Fin 5)).card := by
    exact lt_of_le_of_lt Finset.card_le_four (by decide)
  obtain ⟨m, _, hm'⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  exact ⟨m, by simpa using hm'⟩

variable {E : Type*} [Group E]

/-- Distant elementary matrices have commuting preimages in every central
extension. The spare fifth index removes the possible central commutator. -/
theorem commute_of_root_images (f : E →* G) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) (r s : Root) {x y : E}
    (hx : f x = projectiveRoot r) (hy : f y = projectiveRoot s)
    (hrs : r.val.2 ≠ s.val.1) (hsr : s.val.2 ≠ r.val.1) : Commute x y := by
  obtain ⟨m, hmi, hmj, hmk, hml⟩ := exists_spare r.val.1 r.val.2 s.val.1 s.val.2
  let a := rootPreimage f hf (root r.val.1 m hmi.symm)
  let b := rootPreimage f hf (root m r.val.2 hmj)
  have hab : f ⁅a, b⁆ = projectiveRoot r := by
    rw [map_commutatorElement, rootPreimage_map, rootPreimage_map]
    exact projectiveRoot_relations.chain _ _ _ _ _ r.property
  have hya : Commute (f y) (f a) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [hy, rootPreimage_map]
    exact projectiveRoot_relations.distant _ _ hsr hmk
  have hyb : Commute (f y) (f b) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [hy, rootPreimage_map]
    exact projectiveRoot_relations.distant _ _ hml.symm hrs
  apply commutatorElement_eq_one_iff_commute.mp
  rw [commutator_eq_of_map_eq f hker (hx.trans hab.symm) rfl]
  exact (commute_commutator_of_map_commute f hker hya hyb).symm.commutator_eq

private theorem root_commutator_map (f : E →* G) {i j k : Fin 5}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) {a b : E}
    (ha : f a = projectiveRoot (root i j hij))
    (hb : f b = projectiveRoot (root j k hjk)) :
    f ⁅a, b⁆ = projectiveRoot (root i k hik) := by
  rw [map_commutatorElement, ha, hb]
  exact projectiveRoot_relations.chain i j k hij hjk hik

/-- The two length-two paths between fixed endpoints yield the same commutator. -/
theorem rootPreimage_commutator_independent (f : E →* G) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) (i j k l : Fin 5)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hil : i ≠ l) (hlk : l ≠ k) :
    ⁅rootPreimage f hf (root i j hij), rootPreimage f hf (root j k hjk)⁆ =
      ⁅rootPreimage f hf (root i l hil), rootPreimage f hf (root l k hlk)⁆ := by
  by_cases hjl : j = l
  · subst l
    rfl
  let a := rootPreimage f hf (root i j hij)
  let b := rootPreimage f hf (root j l hjl)
  let c := rootPreimage f hf (root l k hlk)
  have ha : f a = projectiveRoot (root i j hij) := rootPreimage_map _ _ _
  have hb : f b = projectiveRoot (root j l hjl) := rootPreimage_map _ _ _
  have hc : f c = projectiveRoot (root l k hlk) := rootPreimage_map _ _ _
  have hd := root_commutator_map f hij hjl hil ha hb
  have he := root_commutator_map f hjl hlk hjk hb hc
  have ht := root_commutator_map f hil hlk hik hd hc
  have hac : Commute a c := commute_of_root_images f hf hker _ _ ha hc hjl hik.symm
  have hde : Commute ⁅a, b⁆ ⁅b, c⁆ :=
    commute_of_root_images f hf hker _ _ hd he (Ne.symm hjl) hik.symm
  have het : Commute ⁅b, c⁆ ⁅⁅a, b⁆, c⁆ :=
    commute_of_root_images f hf hker _ _ he ht hik.symm hjk.symm
  calc
    _ = ⁅a, ⁅b, c⁆⁆ := commutator_eq_of_map_eq f hker rfl
      ((rootPreimage_map f hf _).trans he.symm)
    _ = ⁅⁅a, b⁆, c⁆ := (commutator_assoc_of_commute hac hde het).symm
    _ = _ := commutator_eq_of_map_eq f hker
      (hd.trans (rootPreimage_map f hf _).symm) rfl

/-- The published lift can be computed through any third index, using any
preimages of the two roots. -/
theorem rootLift_eq_commutator (f : E →* G) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) (i j k : Fin 5)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) {a b : E}
    (ha : f a = projectiveRoot (root i j hij))
    (hb : f b = projectiveRoot (root j k hjk)) :
    rootLift f hf (root i k hik) = ⁅a, b⁆ := by
  rw [rootLift]
  exact (rootPreimage_commutator_independent f hf hker i _ k j
    (auxiliary_ne_left (root i k hik)).symm (auxiliary_ne_right (root i k hik)) hik hij hjk).trans
      (commutator_eq_of_map_eq f hker ((rootPreimage_map _ _ _).trans ha.symm)
        ((rootPreimage_map _ _ _).trans hb.symm))

/-- The commutator lift of each binary root is an involution or the identity. -/
theorem rootLift_square (f : E →* G) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) (r : Root) : rootLift f hf r ^ 2 = 1 := by
  let a := rootPreimage f hf (root r.val.1 (auxiliary r) (auxiliary_ne_left r).symm)
  let b := rootPreimage f hf (root (auxiliary r) r.val.2 (auxiliary_ne_right r))
  have hca : Commute (rootLift f hf r) a :=
    commute_of_root_images f hf hker _ _ (rootLift_map _ _ _) (rootPreimage_map _ _ _)
      r.property.symm (auxiliary_ne_left r)
  have ha2 : a ^ 2 ∈ Subgroup.center E := hker (by
    rw [MonoidHom.mem_ker, map_pow, rootPreimage_map]
    exact projectiveRoot_relations.square _)
  have ha2b : Commute (a ^ 2) b := (Subgroup.mem_center_iff.mp ha2 b).symm
  have h := ha2b.commutator_eq
  rw [pow_two, commutatorElement_mul_left_eq_conj_mul] at h
  change a * rootLift f hf r * a⁻¹ * rootLift f hf r = 1 at h
  rw [hca.symm.eq, mul_inv_cancel_right, ← pow_two] at h
  exact h

/-- All three Steinberg relations hold for the published commutator lifts. -/
theorem rootLift_relations (f : E →* G) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) : Relations (rootLift f hf) where
  square := rootLift_square f hf hker
  distant r s hrs hsr :=
    (commute_of_root_images f hf hker r s (rootLift_map _ _ _) (rootLift_map _ _ _)
      hrs hsr).commutator_eq
  chain i j k hij hjk hik :=
    (rootLift_eq_commutator f hf hker i j k hij hjk hik
      (rootLift_map _ _ _) (rootLift_map _ _ _)).symm

local instance : Group.IsPerfect G := Atlas.psl_perfect 5 (by decide)

/-- The literal universal projection has the lifted Steinberg relations. -/
theorem universalProjection_rootLift_relations :
    Relations (rootLift (PerfectCentralCovering.universalProjection G)
      (PerfectCentralCovering.universalProjection_surjective G)) :=
  rootLift_relations _ _ (PerfectCentralCovering.universalProjection_ker_le_center G)

end Theory.SpecificGroups.PSL5Two.UniversalCover
