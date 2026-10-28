module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm.CellCollection.PositiveCollection
public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm.CellCollection.RootSigns
public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm.Basic

/-!
# Collection and simple-reflection exchange for concrete split D4 cells

Every matrix in the Borel double coset of a root Weyl element has the published
four-factor coordinates: positive, torus, Weyl representative, and a positive
ordered product supported precisely where that Weyl element sends roots negative.
Collection in a partitioned root order absorbs the complementary factors into
the left Borel; the right factor retains the existing twelve-root order.

For simple-reflection exchange, collect the marked simple curve last. Conjugation
sends the other positive factors back into the positive subgroup. The sign of the
inverse Weyl image of the simple root then selects either direct absorption into
the right Borel or the checked rank-one negative-root factorization. This proves
exchange using only the published Weyl/torus inputs and concrete matrix relations.

These are conditional helpers for the split Bruhat assembly. They do not assert
global coverage, separation, or discharge the Weyl/torus inputs.

Source: GLS3 2.3.5, 2.3.7–8 and §2.4
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.Standard.ConcreteBruhat.SplitNormalForm
open PositiveCoordinates Parabolics CellCollection
noncomputable section

private theorem collect_identity {G : Type*} [Group G] (b n t f r : G) :
    (b * (n * t * n⁻¹) * (n * f * n⁻¹)) * n * r = b * n * (t * (f * r)) := by
  simp [mul_assoc]

private theorem conjugate_prefix {G : Type*} [Group G] (n t v x w : G) :
    ((n * t * n⁻¹) * (n * v * n⁻¹)) * (n * x * w) = n * (t * (v * x)) * w := by
  simp [mul_assoc]

private theorem borel_torus_positive {P : Parameters} (D : Inputs P)
    {b : SplitGroup P} (hb : b ∈ splitBorel P) :
    ∃ t : splitTorus P, ∃ u : positiveSubgroup P, b = t.val * u.val := by
  obtain ⟨a, ha, _⟩ := D.existsUnique_borel_factors ⟨b⁻¹, (splitBorel P).inv_mem hb⟩
  refine ⟨a.2⁻¹, a.1⁻¹, ?_⟩
  have h := congrArg (fun x : SplitGroup P => x⁻¹) ha
  simpa only [Subgroup.coe_inv, mul_inv_rev, inv_inv] using h.symm

private theorem lift_conjugate_torus {P : Parameters} (D : Inputs P)
    (w : rootWeylGroup) (t : splitTorus P) :
    D.lift w * t.val * (D.lift w)⁻¹ ∈ splitTorus P := by
  have hn : D.lift w ∈ Subgroup.normalizer (splitTorus P) :=
    D.weyl_normalizes_torus (D.weylEquiv.symm w).property
  exact (Subgroup.mem_normalizer_iff.mp hn t.val).mp t.property

/-- Every element of a split D4 cell has the published ordered inversion coordinates. -/
theorem exists_coordinates_of_mem_cell (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (w : rootWeylGroup)
    {g : SplitGroup (binaryParameters n hn)} (hg : g ∈ cell D w) :
    ∃ a : Coordinates (binaryParameters n hn), a.weyl = w ∧ evaluate D a = g := by
  classical
  let P := binaryParameters n hn
  obtain ⟨b₁, hb₁, b₂, hb₂, hg⟩ := hg
  obtain ⟨t, u, hb₂'⟩ := borel_torus_positive D hb₂
  obtain ⟨f, r, hf, hr, hu⟩ := positive_partition n hn
    (fun i => (typeDRootPairing_base 2).IsPos (w.val (rootIndex i))) u.property
  have hf' : D.lift w * orderedProduct P f * (D.lift w)⁻¹ ∈ positiveSubgroup P := by
    apply conjugate_orderedProduct_mem_positive n hn D w f
    intro i hi
    by_contra h
    exact hi (hf i h)
  let c := b₁ * (D.lift w * t.val * (D.lift w)⁻¹) *
    (D.lift w * orderedProduct P f * (D.lift w)⁻¹)
  have hc : c ∈ splitBorel P :=
    (splitBorel P).mul_mem ((splitBorel P).mul_mem hb₁
      (splitTorus_le_splitBorel P (lift_conjugate_torus D w t)))
      (Subgroup.mem_sup_left hf')
  obtain ⟨a, ha, _⟩ := D.existsUnique_borel_factors ⟨c, hc⟩
  refine ⟨⟨a.1, a.2, w, r, hr⟩, rfl, ?_⟩
  change a.1.val * a.2.val * D.lift w * orderedProduct P r = g
  exact (congrArg (fun x => x * D.lift w * orderedProduct P r) ha).trans
    ((collect_identity b₁ (D.lift w) t.val (orderedProduct P f) (orderedProduct P r)).trans
      ((congrArg (fun x => b₁ * D.lift w * x)
        ((congrArg (fun x => t.val * x) hu).symm.trans hb₂'.symm)).trans hg.symm))

/-- Left multiplication by a Borel element preserves the cell. -/
theorem borel_mul_mem_cell {P : Parameters} (D : Inputs P) (w : rootWeylGroup)
    {b g : SplitGroup P} (hb : b ∈ splitBorel P) (hg : g ∈ cell D w) :
    b * g ∈ cell D w := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hg
  exact ⟨b * b₁, (splitBorel P).mul_mem hb hb₁, b₂, hb₂, by simp only [mul_assoc]⟩

/-- Right multiplication by a Borel element preserves the cell. -/
theorem mul_borel_mem_cell {P : Parameters} (D : Inputs P) (w : rootWeylGroup)
    {b g : SplitGroup P} (hb : b ∈ splitBorel P) (hg : g ∈ cell D w) :
    g * b ∈ cell D w := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hg
  exact ⟨b₁, hb₁, b₂ * b, (splitBorel P).mul_mem hb₂ hb, by simp only [mul_assoc]⟩

private theorem borel_mul_mem_cell_union {P : Parameters} (D : Inputs P)
    (v w : rootWeylGroup) {b g : SplitGroup P} (hb : b ∈ splitBorel P)
    (hg : g ∈ cell D v ∪ cell D w) : b * g ∈ cell D v ∪ cell D w := by
  rcases hg with h | h
  · exact Or.inl (borel_mul_mem_cell D v hb h)
  · exact Or.inr (borel_mul_mem_cell D w hb h)

private theorem rootCurve_simple_eq (P : Parameters) (i : Fin 4) (t : ExtensionField P) :
    rootCurve P (typeDSimpleRootIndex 2 i) t = positiveRoot P i t := by
  rw [← rootIndex_simple, rootCurve_positive, curve_simple]

private theorem rootCurve_mem_positive (n : ℕ) (hn : 0 < n)
    (r : TypeDRootIndex 4) (hr : (typeDRootPairing_base 2).IsPos r)
    (t : ExtensionField (binaryParameters n hn)) :
    rootCurve (binaryParameters n hn) r t ∈ positiveSubgroup _ := by
  have h : r ∈ Set.range rootIndex := by rw [range_rootIndex]; exact hr
  obtain ⟨j, rfl⟩ := h
  exact curve_mem_positiveSubgroup_of_sumExchange _ (sumExchange_binary n hn) j t

private theorem rootCurve_mul_lift {P : Parameters} (D : Inputs P)
    (w : rootWeylGroup) (r : TypeDRootIndex 4) (t : ExtensionField P) :
    rootCurve P r t * D.lift w = D.lift w * rootCurve P ((w⁻¹).val r) t := by
  have h := lift_conjugate_root D w ((w⁻¹).val r) t
  have h' : D.lift w * rootCurve P ((w⁻¹).val r) t * (D.lift w)⁻¹ =
      rootCurve P r t := by
    simpa only [Subgroup.coe_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h
  simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using
    (congrArg (fun x => x * D.lift w) h').symm

private theorem lift_simple_inv {P : Parameters} (D : Inputs P) (i : Fin 4) :
    (D.lift (rootWeylGenerator i))⁻¹ = D.lift (rootWeylGenerator i) := by
  rw [← map_inv, simple_inv]

private theorem rootCurve_negative_simple (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (i : Fin 4)
    (t : ExtensionField (binaryParameters n hn)) :
    rootCurve _ (negativeIndex (typeDSimpleRootIndex 2 i)) t = negativeRoot _ i t := by
  let P := binaryParameters n hn
  let s := D.lift (rootWeylGenerator i)
  calc
    rootCurve P (negativeIndex (typeDSimpleRootIndex 2 i)) t =
        s * rootCurve P (typeDSimpleRootIndex 2 i) t * s⁻¹ :=
      (lift_conjugate_root D (rootWeylGenerator i) (typeDSimpleRootIndex 2 i) t).symm
    _ = s * positiveRoot P i t * s :=
      congrArg₂ (fun x y => s * x * y) (rootCurve_simple_eq P i t) (lift_simple_inv D i)
    _ = weylWord P i 1 * positiveRoot P i t * weylWord P i 1 :=
      congrArg (fun x => x * positiveRoot P i t * x) (D.lift_simple i)
    _ = negativeRoot P i t := weylWord_positive P rfl i t

private theorem orderedProduct_single_support (P : Parameters)
    (a : PositiveCoordinates.Coordinates P) (j : Fin 12)
    (ha : ∀ i, i ≠ j → a i = 0) : orderedProduct P a = curve P j (a j) := by
  classical
  have h := List.prod_map_eq_pow_single (l := List.finRange 12) j
    (fun i => curve P i (a i)) (fun i hi _ => by rw [ha i hi, curve_zero])
  simpa only [orderedProduct, List.ofFn_eq_map, List.count_finRange, pow_one] using h

private theorem positive_simple_last (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (i : Fin 4)
    {u : SplitGroup (binaryParameters n hn)} (hu : u ∈ positiveSubgroup _) :
    ∃ v : positiveSubgroup (binaryParameters n hn), ∃ t : ExtensionField (binaryParameters n hn),
      u = v.val * positiveRoot _ i t ∧
      D.lift (rootWeylGenerator i) * v.val * (D.lift (rootWeylGenerator i))⁻¹ ∈
        positiveSubgroup _ := by
  classical
  obtain ⟨a, b, ha, hb, hu⟩ := positive_partition n hn (fun j => j ≠ simplePosition i) hu
  have hva : orderedProduct (binaryParameters n hn) a ∈ positiveSubgroup _ :=
    orderedProduct_mem_positiveSubgroup_of_sumExchange _ (sumExchange_binary n hn) a
  refine ⟨⟨orderedProduct _ a, hva⟩, b (simplePosition i), ?_, ?_⟩
  · simpa only [orderedProduct_single_support _ b _ hb, curve_simple] using hu
  · apply conjugate_orderedProduct_mem_positive n hn D (rootWeylGenerator i) a
    intro j hj
    apply simple_preserves_other_positive
    intro heq
    exact hj (ha j (not_not_intro heq))

private theorem simple_positive_simple (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (i : Fin 4)
    (t : ExtensionField (binaryParameters n hn)) :
    D.lift (rootWeylGenerator i) * positiveRoot _ i t * D.lift (rootWeylGenerator i) =
      negativeRoot _ i t := by
  rw [D.lift_simple, weylWord_positive _ rfl]

private theorem simple_mul_positive (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (i : Fin 4)
    (t : ExtensionField (binaryParameters n hn)) :
    D.lift (rootWeylGenerator i) * positiveRoot _ i t =
      negativeRoot _ i t * D.lift (rootWeylGenerator i) := by
  have h : D.lift (rootWeylGenerator i) * positiveRoot _ i t *
      (D.lift (rootWeylGenerator i))⁻¹ = negativeRoot _ i t := by
    rw [lift_simple_inv]
    exact simple_positive_simple n hn D i t
  simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using
    congrArg (fun x => x * D.lift (rootWeylGenerator i)) h

private theorem simple_root_exchange (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (i : Fin 4) (w : rootWeylGroup)
    (t : ExtensionField (binaryParameters n hn)) :
    D.lift (rootWeylGenerator i) * positiveRoot _ i t * D.lift w ∈
      cell D (rootWeylGenerator i * w) ∪ cell D w := by
  classical
  let P := binaryParameters n hn
  let α := typeDSimpleRootIndex 2 i
  by_cases ht : t = 0
  · subst t
    exact Or.inl ⟨1, (splitBorel P).one_mem, 1, (splitBorel P).one_mem,
      by simp only [positiveRoot_zero, mul_one, one_mul, map_mul]⟩
  by_cases hp : (typeDRootPairing_base 2).IsPos ((w⁻¹).val α)
  · have hm := rootCurve_mul_lift D w α t
    rw [rootCurve_simple_eq] at hm
    refine Or.inl ⟨1, (splitBorel P).one_mem, rootCurve P ((w⁻¹).val α) t,
      Subgroup.mem_sup_left (rootCurve_mem_positive n hn _ hp t), ?_⟩
    simpa only [one_mul, map_mul, mul_assoc] using
      congrArg (fun x => D.lift (rootWeylGenerator i) * x) hm
  · have hneg := inverse_negative_simple_positive w i hp
    let c := positiveRoot P i t⁻¹ * torusWord P i (Units.mk0 t⁻¹ (inv_ne_zero ht))
    have hc : c ∈ splitBorel P :=
      (splitBorel P).mul_mem
        (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨i, t⁻¹, rfl⟩))
        (splitTorus_le_splitBorel P (Subgroup.subset_closure ⟨i, _, rfl⟩))
    refine Or.inr ⟨c, hc, rootCurve P ((w⁻¹).val (negativeIndex α)) t⁻¹,
      Subgroup.mem_sup_left (rootCurve_mem_positive n hn _ hneg t⁻¹), ?_⟩
    calc
      D.lift (rootWeylGenerator i) * positiveRoot P i t * D.lift w =
          negativeRoot P i t * D.lift (rootWeylGenerator i) * D.lift w := by
        exact congrArg (fun x => x * D.lift w) (simple_mul_positive n hn D i t)
      _ = c * (D.lift (rootWeylGenerator i) * positiveRoot P i t⁻¹ *
            D.lift (rootWeylGenerator i)) * D.lift w := by
        have hf : negativeRoot P i t = positiveRoot P i t⁻¹ *
            torusWord P i (Units.mk0 t⁻¹ (inv_ne_zero ht)) *
              D.lift (rootWeylGenerator i) * positiveRoot P i t⁻¹ :=
          (negativeRoot_factorization P rfl i t ht).trans
            (congrArg (fun x => positiveRoot P i t⁻¹ *
              torusWord P i (Units.mk0 t⁻¹ (inv_ne_zero ht)) * x * positiveRoot P i t⁻¹)
              (D.lift_simple i).symm)
        simpa only [c, mul_assoc] using
          congrArg (fun x => x * D.lift (rootWeylGenerator i) * D.lift w) hf
      _ = c * negativeRoot P i t⁻¹ * D.lift w := by
        exact congrArg (fun x => c * x * D.lift w) (simple_positive_simple n hn D i t⁻¹)
      _ = c * D.lift w * rootCurve P ((w⁻¹).val (negativeIndex α)) t⁻¹ := by
        have hm : negativeRoot P i t⁻¹ * D.lift w =
            D.lift w * rootCurve P ((w⁻¹).val (negativeIndex α)) t⁻¹ :=
          (congrArg (fun x => x * D.lift w) (rootCurve_negative_simple n hn D i t⁻¹).symm).trans
            (rootCurve_mul_lift D w (negativeIndex α) t⁻¹)
        simpa only [mul_assoc] using congrArg (fun x => c * x) hm

/-- Simple-reflection exchange for the literal split D4 double cosets. -/
theorem simple_reflection_exchange (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (i : Fin 4) (w : rootWeylGroup)
    {b : SplitGroup (binaryParameters n hn)} (hb : b ∈ splitBorel _) :
    D.lift (rootWeylGenerator i) * b * D.lift w ∈
      cell D (rootWeylGenerator i * w) ∪ cell D w := by
  let P := binaryParameters n hn
  let s := D.lift (rootWeylGenerator i)
  obtain ⟨h, u, hb'⟩ := borel_torus_positive D hb
  obtain ⟨v, t, hu, hv⟩ := positive_simple_last n hn D i u.property
  let c := (s * h.val * s⁻¹) * (s * v.val * s⁻¹)
  have hc : c ∈ splitBorel P :=
    (splitBorel P).mul_mem
      (splitTorus_le_splitBorel P (lift_conjugate_torus D (rootWeylGenerator i) h))
      (Subgroup.mem_sup_left hv)
  have heq : s * b * D.lift w = c * (s * positiveRoot P i t * D.lift w) := by
    exact (congrArg (fun x => s * x * D.lift w)
      (hb'.trans (congrArg (fun x => h.val * x) hu))).trans
      (conjugate_prefix s h.val v.val (positiveRoot P i t) (D.lift w)).symm
  have hmem : c * (s * positiveRoot P i t * D.lift w) ∈
      cell D (rootWeylGenerator i * w) ∪ cell D w :=
    borel_mul_mem_cell_union D (rootWeylGenerator i * w) w hc
      (simple_root_exchange n hn D i w t)
  exact heq.symm ▸ hmem

end
end Triality.Standard.ConcreteBruhat.SplitNormalForm
