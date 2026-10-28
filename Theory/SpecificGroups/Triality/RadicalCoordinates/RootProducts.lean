module

public import Theory.SpecificGroups.Triality.PositiveRootCoordinates
public import Theory.SpecificGroups.Triality.ParabolicLocalDefinitions

/-!
# Positive root products for the two triality radicals

The roots outside the chosen Levi subsystem have nine or eleven coordinates
in the ordered positive D4 normal form. The actual Geck exchange identities
and filtered collection prove that their products form the subgroup generated
by those root curves, with unique supported coordinates. In particular these
subgroups are two-groups in characteristic two.

Root commutators place every such curve in the existing parabolic normal-closure
candidate `splitRadical`. The reverse inclusion reduces to relative parabolic
normality of the root product; that normalization is not assumed as a theorem.
The support test is checked against the actual simple-root coefficients.

Source: GLS3 Definition 2.6.4 and §§2.4, 2.6
(`refs/KGroup/GLS3/chapter2.tex`); Aschbacher–Smith F.1.11–12
(`refs/quasithin.pdf`, printed pp.262–264).
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.PositiveCoordinates
namespace Triality.Standard.RadicalCoordinates
open Parabolics

/-- Positive roots outside the selected Levi subsystem. -/
def rootSupport : Node → Fin 12 → Prop
  | .arms, i => 3 ≤ i.val
  | .central, i => i ≠ 3

instance (a : Node) : DecidablePred (rootSupport a) := by
  cases a <;> unfold rootSupport <;> infer_instance

/-- Coordinates of a product of positive roots outside the Levi subsystem. -/
abbrev SupportedCoordinates (P : Parameters) (a : Node) :=
  {v : Coordinates P // ∀ i, ¬ rootSupport a i → v i = 0}

/-- The positive-root subgroup before identification with the parabolic normal closure. -/
def rootSubgroup (P : Parameters) (a : Node) : Subgroup (SplitGroup P) :=
  Subgroup.closure {g | ∃ i, rootSupport a i ∧ ∃ t, g = curve P i t}

theorem rootSupport_simple (a : Node) (i : Fin 4) :
    rootSupport a (simplePosition i) ↔ i ∉ a.support := by
  cases a <;> fin_cases i <;> simp [rootSupport, simplePosition, Node.support]

@[simp] theorem rootSupport_diagram (a : Node) (i : Fin 12) :
    rootSupport a (diagram i) ↔ rootSupport a i := by
  cases a <;> fin_cases i <;> decide

private theorem rootSupport_of_height (a : Node) {i : Fin 12}
    (h : 1 < collectionHeight i) : rootSupport a i := by
  cases a <;> fin_cases i <;> simp_all [collectionHeight, rootSupport]

/-- Any positive root sum is outside both rank-one Levi subsystems. -/
theorem rootSupport_of_sum (a : Node) {i j k : Fin 12}
    (h : (typeDRootPairing 2).root (rootIndex k) =
      (typeDRootPairing 2).root (rootIndex i) +
        (typeDRootPairing 2).root (rootIndex j)) : rootSupport a k := by
  apply rootSupport_of_height
  have := collectionHeight_add h
  have := collectionHeight_pos i
  have := collectionHeight_pos j
  omega

theorem curve_mem_rootSubgroup (P : Parameters) (a : Node) (i : Fin 12)
    (hi : rootSupport a i) (t : ExtensionField P) : curve P i t ∈ rootSubgroup P a :=
  Subgroup.subset_closure ⟨i, hi, t, rfl⟩

theorem rootSubgroup_le_positiveSubgroup (P : Parameters) (hp : P.prime = 2) (a : Node) :
    rootSubgroup P a ≤ positiveSubgroup P := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i, _, t, rfl⟩
  exact curve_mem_positiveSubgroup_of_sumExchange _ (sumExchange_binary n hn) i t

theorem orderedProduct_mem_rootSubgroup (P : Parameters) (a : Node)
    (v : SupportedCoordinates P a) : orderedProduct P v.val ∈ rootSubgroup P a := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  by_cases hi : rootSupport a i
  · exact curve_mem_rootSubgroup P a i hi _
  · rw [v.property i hi, curve_zero]
    exact Subgroup.one_mem _

private theorem product_filter (P : Parameters) (a : Node) (v : Coordinates P)
    (l : List (Fin 12)) :
    ((l.filter (rootSupport a)).map fun i => curve P i (v i)).prod =
      (l.map fun i => curve P i (if rootSupport a i then v i else 0)).prod := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases hi : rootSupport a i <;> simp [hi, ih]

open FilteredCollection in
private theorem collect_supported (P : Parameters) (hp : P.prime = 2) (a : Node)
    (word : List (Fin 12 × ExtensionField P))
    (hw : ∀ z ∈ word, rootSupport a z.1) :
    ∃ v : SupportedCoordinates P a, wordProduct (curve P) word = orderedProduct P v.val := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  let P := binaryParameters n hn
  let order := (List.finRange 12).filter (rootSupport a)
  have hm (i : Fin 12) : i ∈ order ↔ rootSupport a i := by simp [order]
  have hs : ∀ (i j : Fin 12) (s t : ExtensionField P),
      i ∈ order → j ∈ order → i ≠ j →
      ∃ correction : List (Fin 12 × ExtensionField P),
        (∀ z ∈ correction, z.1 ∈ order ∧
          max (collectionHeight i) (collectionHeight j) < collectionHeight z.1) ∧
        curve P i s * curve P j t =
          curve P j t * curve P i s * wordProduct (curve P) correction := by
    intro i j s t _ _ hij
    by_cases h : ∃ k : Fin 12, (typeDRootPairing 2).root (rootIndex k) =
        (typeDRootPairing 2).root (rootIndex i) + (typeDRootPairing 2).root (rootIndex j)
    · obtain ⟨k, hk⟩ := h
      refine ⟨[(k, s * t)], ?_, ?_⟩
      · intro z hz
        have hz' : z = (k, s * t) := by simpa using hz
        subst z
        exact ⟨(hm k).mpr (rootSupport_of_sum a hk), collectionHeight_sum_gt hk⟩
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one] using sumExchange_binary n hn i j k hk s t
    · refine ⟨[], by simp, ?_⟩
      simpa only [wordProduct, List.map_nil, List.prod_nil, mul_one] using
        (nonsumCommute_binary n hn i j hij h s t).eq
  obtain ⟨v, hv⟩ := filteredCollection_exists_params collectionHeight (curve P)
    order ((List.nodup_finRange 12).filter _) 6
    (fun i _ => collectionHeight_lt_six i)
    (fun i s t => (curve_add P i s t).symm) hs word
    (fun z hz => (hm z.1).mpr (hw z hz))
  refine ⟨⟨fun i => if rootSupport a i then v i else 0, ?_⟩, ?_⟩
  · intro i hi
    simp [hi]
  · exact hv.trans (by simpa only [orderedProduct, List.ofFn_eq_map] using
      (product_filter P a v (List.finRange 12)))

open FilteredCollection in
private theorem exists_supported_word (P : Parameters) (a : Node) {g : SplitGroup P}
    (hg : g ∈ rootSubgroup P a) :
    ∃ word : List (Fin 12 × ExtensionField P),
      (∀ z ∈ word, rootSupport a z.1) ∧ wordProduct (curve P) word = g := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, hi, t, rfl⟩ := hg
    exact ⟨[(i, t)], by simpa, by simp [wordProduct]⟩
  | one => exact ⟨[], by simp, by simp [wordProduct]⟩
  | mul g h _ _ hg hh =>
    obtain ⟨v, hv, rfl⟩ := hg
    obtain ⟨w, hw, rfl⟩ := hh
    exact ⟨v ++ w, by simpa only [List.mem_append, or_imp, forall_and] using ⟨hv, hw⟩,
      by simp [wordProduct]⟩
  | inv g _ hg =>
    obtain ⟨word, hw, rfl⟩ := hg
    refine ⟨(word.map fun z => (z.1, -z.2)).reverse, ?_, ?_⟩
    · intro z hz
      obtain ⟨w, hw', rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hz)
      exact hw w hw'
    · simp only [wordProduct, List.map_reverse, List.map_map, List.prod_inv_reverse]
      apply congrArg List.prod
      apply congrArg List.reverse
      apply List.map_congr_left
      intro z _
      exact (curve_inv P z.1 z.2).symm

/-- The positive-root subgroup has precisely the supported ordered products. -/
theorem mem_rootSubgroup_iff (P : Parameters) (hp : P.prime = 2) (a : Node)
    (g : SplitGroup P) :
    g ∈ rootSubgroup P a ↔ ∃ v : SupportedCoordinates P a, orderedProduct P v.val = g := by
  constructor
  · intro hg
    obtain ⟨word, hw, rfl⟩ := exists_supported_word P a hg
    obtain ⟨v, hv⟩ := collect_supported P hp a word hw
    exact ⟨v, hv.symm⟩
  · rintro ⟨v, rfl⟩
    exact orderedProduct_mem_rootSubgroup P a v

/-- Faithful ordered root coordinates for the subgroup defined by the source root set. -/
def rootEquiv (P : Parameters) (hp : P.prime = 2) (a : Node) :
    SupportedCoordinates P a ≃ rootSubgroup P a :=
  Equiv.ofBijective
    (fun v => ⟨orderedProduct P v.val, orderedProduct_mem_rootSubgroup P a v⟩)
    ⟨by
      intro v w h
      apply Subtype.ext
      obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
      exact orderedProduct_injective_binary n hn (congrArg Subtype.val h), by
      intro g
      obtain ⟨v, hv⟩ := (mem_rootSubgroup_iff P hp a g.val).mp g.property
      exact ⟨v, Subtype.ext hv⟩⟩

@[simp] theorem rootEquiv_val (P : Parameters) (hp : P.prime = 2) (a : Node)
    (v : SupportedCoordinates P a) : (rootEquiv P hp a v).val = orderedProduct P v.val := rfl


/-- The support condition in GLS3 2.6.4, expressed in the actual simple-root basis. -/
theorem rootSupport_iff_outside_coefficient (a : Node) (i : Fin 12) :
    rootSupport a i ↔ ∃ j : Fin 4, j ∉ a.support ∧ coefficients i j ≠ 0 := by
  cases a <;> fin_cases i <;>
    simp [rootSupport, coefficients, Node.support, Fin.exists_fin_succ]


theorem isPGroup_rootSubgroup (P : Parameters) (hp : P.prime = 2) (a : Node) :
    IsPGroup 2 (rootSubgroup P a) := by
  have hpos : IsPGroup 2 (positiveSubgroup P) := by
    obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
    exact isPGroup_positiveSubgroup_binary n hn
  exact hpos.to_le (rootSubgroup_le_positiveSubgroup P hp a)


/-- The root product lies in the original parabolic normal-closure candidate.
The reverse inclusion needs stability under the negative Levi roots and torus. -/
theorem rootSubgroup_le_splitRadical (P : Parameters) (hp : P.prime = 2) (a : Node) :
    rootSubgroup P a ≤ splitRadical P a := by
  have hsum : SumExchange P := by
    obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
    exact sumExchange_binary n hn
  have hpos (i : Fin 12) (t : ExtensionField P) : curve P i t ∈ splitParabolic P a :=
    (show positiveSubgroup P ≤ splitParabolic P a from le_sup_left.trans le_sup_left)
      (curve_mem_positiveSubgroup_of_sumExchange P hsum i t)
  have hconj := (Subgroup.normal_subgroupOf_iff (splitRadical_le_splitParabolic P a)).mp
    (splitRadical_normal P a)
  have hadd (j : Fin 8) (s : ExtensionField P)
      (hm : curve P (leftParent j) s ∈ splitRadical P a ∨
        curve P (rightParent j) 1 ∈ splitRadical P a) :
      curve P ⟨j + 4, by omega⟩ s ∈ splitRadical P a := by
    have he := hsum (leftParent j) (rightParent j) ⟨j + 4, by omega⟩ (root_add j) s 1
    simp only [mul_one] at he
    have heq : curve P ⟨j + 4, by omega⟩ s =
        (curve P (leftParent j) s)⁻¹ * (curve P (rightParent j) 1)⁻¹ *
          curve P (leftParent j) s * curve P (rightParent j) 1 := by
      calc
        _ = (curve P (rightParent j) 1 * curve P (leftParent j) s)⁻¹ *
              (curve P (leftParent j) s * curve P (rightParent j) 1) := by
                rw [he, inv_mul_cancel_left]
        _ = _ := by simp only [mul_inv_rev, mul_assoc]
    rw [heq]
    rcases hm with hl | hr
    · have hc := hconj _ (curve P (rightParent j) 1)⁻¹ hl
        ((splitParabolic P a).inv_mem (hpos _ _))
      simpa only [inv_inv, mul_assoc] using
        (splitRadical P a).mul_mem ((splitRadical P a).inv_mem hl) hc
    · have hc := hconj _ (curve P (leftParent j) s)⁻¹
        ((splitRadical P a).inv_mem hr) ((splitParabolic P a).inv_mem (hpos _ _))
      simpa only [inv_inv] using (splitRadical P a).mul_mem hc hr
  have hs (i : Fin 4) (hi : i ∉ a.support) (s : ExtensionField P) :
      curve P (simplePosition i) s ∈ splitRadical P a := by
    rw [curve_simple]
    exact positiveRoot_mem_splitRadical P a i hi s
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i, hi, s, rfl⟩
  cases a
  · have h3 := hs 1 (by simp [Node.support])
    have h4 (t) := hadd 0 t (Or.inr (h3 1))
    have h5 (t) := hadd 1 t (Or.inr (h3 1))
    have h6 (t) := hadd 2 t (Or.inr (h3 1))
    have h7 (t) := hadd 3 t (Or.inl (h4 t))
    have h8 (t) := hadd 4 t (Or.inl (h5 t))
    have h9 (t) := hadd 5 t (Or.inl (h6 t))
    have h10 (t) := hadd 6 t (Or.inl (h7 t))
    have h11 (t) := hadd 7 t (Or.inl (h10 t))
    fin_cases i
    · simp [rootSupport] at hi
    · simp [rootSupport] at hi
    · simp [rootSupport] at hi
    · exact h3 s
    · exact h4 s
    · exact h5 s
    · exact h6 s
    · exact h7 s
    · exact h8 s
    · exact h9 s
    · exact h10 s
    · exact h11 s
  · have h0 := hs 0 (by simp [Node.support])
    have h1 := hs 2 (by simp [Node.support])
    have h2 := hs 3 (by simp [Node.support])
    have h4 (t) := hadd 0 t (Or.inl (h0 t))
    have h5 (t) := hadd 1 t (Or.inl (h1 t))
    have h6 (t) := hadd 2 t (Or.inl (h2 t))
    have h7 (t) := hadd 3 t (Or.inl (h4 t))
    have h8 (t) := hadd 4 t (Or.inl (h5 t))
    have h9 (t) := hadd 5 t (Or.inl (h6 t))
    have h10 (t) := hadd 6 t (Or.inl (h7 t))
    have h11 (t) := hadd 7 t (Or.inl (h10 t))
    fin_cases i
    · exact h0 s
    · exact h1 s
    · exact h2 s
    · simp [rootSupport] at hi
    · exact h4 s
    · exact h5 s
    · exact h6 s
    · exact h7 s
    · exact h8 s
    · exact h9 s
    · exact h10 s
    · exact h11 s


/-- Relative parabolic normality is the missing reverse inclusion in the root
identification. The forward inclusion was proved by root commutators. -/
theorem splitRadical_eq_rootSubgroup_of_normal (P : Parameters) (hp : P.prime = 2) (a : Node)
    (hN : ((rootSubgroup P a).subgroupOf (splitParabolic P a)).Normal) :
    splitRadical P a = rootSubgroup P a := by
  apply le_antisymm _ (rootSubgroup_le_splitRadical P hp a)
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨x, hx, i, hi, t, rfl⟩
  have hle : rootSubgroup P a ≤ splitParabolic P a :=
    (rootSubgroup_le_splitRadical P hp a).trans (splitRadical_le_splitParabolic P a)
  apply (Subgroup.normal_subgroupOf_iff hle).mp hN _ _ _ hx
  rw [← curve_simple]
  exact curve_mem_rootSubgroup P a (simplePosition i) ((rootSupport_simple a i).mpr hi) t


end Triality.Standard.RadicalCoordinates
