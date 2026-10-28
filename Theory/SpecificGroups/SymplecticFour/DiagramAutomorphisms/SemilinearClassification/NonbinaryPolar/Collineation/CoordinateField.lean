module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.NonbinaryPolar.Collineation.Frame

/-!
# Coordinate-line arithmetic for a normalized collineation

This module reconstructs the field map carried by a projective collineation
which fixes the standard projective frame.  The proof uses only the induced
order isomorphism on submodules and explicit coordinate calculations: coordinate
planes first recover the parameter maps, three-coordinate spans give their
multiplication and addition laws, and normalization identifies all ordered
coordinate pairs with one field automorphism.  This is the coordinate-line
ingredient of Aschbacher--Smith F.1.12, printed pp.263--264 of
`refs/quasithin.pdf`.
-/

public noncomputable section
open Projectivization Module
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.Collineation
variable {F : Type*} [Field F]

private theorem pairPoint_ne_axis_right (i j : Index) (hij : i ≠ j) (t : F) :
    pairPoint i j hij t ≠ axis j := by
  intro h
  obtain ⟨c, hc⟩ := (mk_eq_mk_iff' F _ _ _ _).mp h
  have hi := congrFun hc i
  simp [hij] at hi

private theorem pairPoint_eq_of_mem_axes (i j : Index) (hij : i ≠ j)
    (p : ProjectivePoint F)
    (hp : p.submodule ≤ (axis (F := F) i).submodule ⊔ (axis (F := F) j).submodule)
    (hjp : p ≠ axis j) : ∃ t : F, p = pairPoint i j hij t := by
  induction p using Projectivization.ind with
  | h v hv =>
    have hmem : v ∈ (axis (F := F) i).submodule ⊔ (axis (F := F) j).submodule := by
      simpa only [submodule_mk, Submodule.span_singleton_le_iff_mem] using hp
    obtain ⟨u, hu, w, hw, huv⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hw
    -- The `i` coordinate of the representative is nonzero, since otherwise
    -- the projective point would be the right hand axis.
    have hi : a ≠ 0 := by
      intro ha
      apply hjp
      apply (mk_eq_mk_iff' F _ _ _ _).mpr
      refine ⟨b, ?_⟩
      simpa [ha] using huv
    refine ⟨b / a, ?_⟩
    apply (mk_eq_mk_iff' F _ _ _ _).mpr
    refine ⟨a, ?_⟩
    rw [← huv]
    ext k
    by_cases hki : k = i
    · subst k
      simp [hij]
    by_cases hkj : k = j
    · subst k
      simp [div_eq_mul_inv]
      field_simp [hi]
    · simp [hki, hkj]

theorem exists_pairPoint_coordinate (ψ : Equiv.Perm (ProjectivePoint F))
    (hψ : PreservesLines ψ) (haxes : ∀ i : Index, ψ (axis i) = axis i)
    (i j : Index) (hij : i ≠ j) (t : F) :
    ∃ s : F, ψ (pairPoint i j hij t) = pairPoint i j hij s := by
  have hplane : (ψ (pairPoint i j hij t)).submodule ≤
      (axis i).submodule ⊔ (axis j).submodule := by
    simpa only [haxes] using
      (hψ (axis i) (axis j) (pairPoint i j hij t)).mpr
        (pairPoint_le_axes i j hij t)
  obtain ⟨s, hs⟩ := pairPoint_eq_of_mem_axes i j hij (ψ (pairPoint i j hij t)) hplane
    (by intro h; exact pairPoint_ne_axis_right i j hij t (ψ.injective (by simpa [haxes j] using h)))
  exact ⟨s, hs⟩

noncomputable def coordinateParameter (ψ : Equiv.Perm (ProjectivePoint F))
    (hψ : PreservesLines ψ) (haxes : ∀ i : Index, ψ (axis i) = axis i)
    (i j : Index) (hij : i ≠ j) (t : F) : F :=
  (exists_pairPoint_coordinate ψ hψ haxes i j hij t).choose

theorem coordinateParameter_spec (ψ : Equiv.Perm (ProjectivePoint F))
    (hψ : PreservesLines ψ) (haxes : ∀ i : Index, ψ (axis i) = axis i)
    (i j : Index) (hij : i ≠ j) (t : F) :
    ψ (pairPoint i j hij t) = pairPoint i j hij (coordinateParameter ψ hψ haxes i j hij t) :=
  (exists_pairPoint_coordinate ψ hψ haxes i j hij t).choose_spec

theorem coordinateParameter_zero (ψ : Equiv.Perm (ProjectivePoint F))
    (hψ : PreservesLines ψ) (haxes : ∀ i : Index, ψ (axis i) = axis i)
    (i j : Index) (hij : i ≠ j) :
    coordinateParameter ψ hψ haxes i j hij 0 = 0 := by
  apply pairPoint_injective i j hij
  have h := coordinateParameter_spec ψ hψ haxes i j hij 0
  rw [pairPoint_zero, haxes i] at h
  simpa only [pairPoint_zero] using h.symm

theorem coordinateParameter_injective (ψ : Equiv.Perm (ProjectivePoint F))
    (hψ : PreservesLines ψ) (haxes : ∀ i : Index, ψ (axis i) = axis i)
    (i j : Index) (hij : i ≠ j) :
    Function.Injective (coordinateParameter ψ hψ haxes i j hij) := by
  intro s t hst
  apply pairPoint_injective i j hij
  apply ψ.injective
  have hs := coordinateParameter_spec ψ hψ haxes i j hij s
  have ht := coordinateParameter_spec ψ hψ haxes i j hij t
  rw [hs, ht, hst]

theorem coordinateParameter_surjective (ψ : Equiv.Perm (ProjectivePoint F))
    (hψ : PreservesLines ψ) (haxes : ∀ i : Index, ψ (axis i) = axis i)
    (i j : Index) (hij : i ≠ j) :
    Function.Surjective (coordinateParameter ψ hψ haxes i j hij) := by
  intro y
  let q := ψ.symm (pairPoint i j hij y)
  have haxes_symm (k : Index) : ψ.symm (axis k) = axis k := by
    calc
      ψ.symm (axis k) = ψ.symm (ψ (axis k)) := congrArg ψ.symm (haxes k).symm
      _ = axis k := ψ.symm_apply_apply _
  have hplane : q.submodule ≤ (axis i).submodule ⊔ (axis j).submodule := by
    simpa only [q, haxes_symm] using
      (hψ.symm (axis i) (axis j) (pairPoint i j hij y)).mpr
        (pairPoint_le_axes i j hij y)
  have hqj : q ≠ axis j := by
    intro h
    have h' : pairPoint i j hij y = axis j := by
      calc
        pairPoint i j hij y = ψ q := (ψ.apply_symm_apply _).symm
        _ = ψ (axis j) := congrArg ψ h
        _ = axis j := haxes j
    exact pairPoint_ne_axis_right i j hij y h'
  obtain ⟨t, ht⟩ := pairPoint_eq_of_mem_axes i j hij q hplane hqj
  refine ⟨t, ?_⟩
  apply pairPoint_injective i j hij
  have hqt : ψ (pairPoint i j hij t) = pairPoint i j hij y := by
    rw [← ht, ψ.apply_symm_apply]
  rw [coordinateParameter_spec] at hqt
  exact hqt


private def coordinateHyperplane (i j : Index) (t : F) : Submodule F (Vector F) where
  carrier := {v | v j = t * v i}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change v j + w j = t * (v i + w i)
    rw [hv, hw, mul_add]
  smul_mem' := by
    intro c v hv
    change c * v j = t * (c * v i)
    rw [hv]
    ring

private theorem mem_remaining_axes (i j : Index) (v : Vector F)
    (hi : v i = 0) (hj : v j = 0) :
    v ∈ ⨆ (k : Index) (_ : k ≠ i) (_ : k ≠ j), (axis (F := F) k).submodule := by
  rw [pi_eq_sum_univ' v]
  apply Submodule.sum_mem
  intro k _
  by_cases hki : k = i
  · subst k
    simp [hi]
  by_cases hkj : k = j
  · subst k
    simp [hj]
  apply Submodule.smul_mem
  have hle : (axis (F := F) k).submodule ≤
      ⨆ (l : Index) (_ : l ≠ i) (_ : l ≠ j), (axis (F := F) l).submodule :=
    le_iSup_of_le k (le_iSup_of_le hki (le_iSup_of_le hkj le_rfl))
  exact hle (Submodule.mem_span_singleton_self _)

private theorem coordinateHyperplane_eq_span (i j : Index) (hij : i ≠ j) (t : F) :
    coordinateHyperplane i j t = (pairPoint i j hij t).submodule ⊔
      ⨆ (k : Index) (_ : k ≠ i) (_ : k ≠ j), (axis (F := F) k).submodule := by
  apply le_antisymm
  · intro v hv
    let u : Vector F := Pi.single i 1 + t • Pi.single j 1
    have hui : u i = 1 := by simp [u, hij]
    have huj : u j = t := by simp [u, hij.symm]
    have hi : (v - v i • u) i = 0 := by simp [hui]
    have hj : (v - v i • u) j = 0 := by
      change v j - v i * u j = 0
      change v j = t * v i at hv
      rw [huj, hv, mul_comm t, sub_self]
    have hrem := mem_remaining_axes i j (v - v i • u) hi hj
    have hu : u ∈ (pairPoint i j hij t).submodule :=
      Submodule.mem_span_singleton_self _
    have hadd := Submodule.add_mem
      ((pairPoint i j hij t).submodule ⊔
        ⨆ (k : Index) (_ : k ≠ i) (_ : k ≠ j), (axis (F := F) k).submodule)
      (Submodule.mem_sup_left (Submodule.smul_mem _ (v i) hu))
      (Submodule.mem_sup_right hrem)
    simpa only [add_sub_cancel] using hadd
  · refine sup_le ?_ (iSup_le fun k => iSup_le fun hki => iSup_le fun hkj => ?_)
    · rw [pairPoint, submodule_mk, Submodule.span_singleton_le_iff_mem]
      change (Pi.single i 1 + t • Pi.single j 1 : Vector F) j =
        t * (Pi.single i 1 + t • Pi.single j 1 : Vector F) i
      simp [hij, hij.symm]
    · rw [axis_submodule, Submodule.span_singleton_le_iff_mem]
      change (Pi.single k 1 : Vector F) j = t * (Pi.single k 1 : Vector F) i
      simp [hki.symm, hkj.symm]

private theorem map_coordinateHyperplane (ψ : Equiv.Perm (ProjectivePoint F))
    (hψ : PreservesLines ψ) (haxes : ∀ i : Index, ψ (axis i) = axis i)
    (i j : Index) (hij : i ≠ j) (t : F) :
    submoduleOrderIso ψ hψ (coordinateHyperplane i j t) =
      coordinateHyperplane i j (coordinateParameter ψ hψ haxes i j hij t) := by
  rw [coordinateHyperplane_eq_span i j hij t,
    coordinateHyperplane_eq_span i j hij (coordinateParameter ψ hψ haxes i j hij t)]
  simp only [OrderIso.map_sup, OrderIso.map_iSup, submoduleOrderIso_point,
    coordinateParameter_spec ψ hψ haxes, haxes]

private theorem image_coordinate_relation (ψ : Equiv.Perm (ProjectivePoint F))
    (hψ : PreservesLines ψ) (haxes : ∀ i : Index, ψ (axis i) = axis i)
    (v : Vector F) (hv : v ≠ 0) (i j : Index) (hij : i ≠ j) (t : F)
    (ht : v j = t * v i) :
    (ψ (mk F v hv)).rep j =
      coordinateParameter ψ hψ haxes i j hij t * (ψ (mk F v hv)).rep i := by
  have hle : (mk F v hv).submodule ≤ coordinateHyperplane i j t := by
    rw [submodule_mk, Submodule.span_singleton_le_iff_mem]
    exact ht
  have hm := (submoduleOrderIso ψ hψ).monotone hle
  rw [submoduleOrderIso_point, map_coordinateHyperplane ψ hψ haxes i j hij] at hm
  exact hm (by rw [submodule_eq]; exact Submodule.mem_span_singleton_self _)

private theorem image_pivot_ne_zero (ψ : Equiv.Perm (ProjectivePoint F))
    (hψ : PreservesLines ψ) (haxes : ∀ i : Index, ψ (axis i) = axis i)
    (v : Vector F) (hv : v ≠ 0) (i : Index) (hi : v i = 1) :
    (ψ (mk F v hv)).rep i ≠ 0 := by
  intro hz
  apply (ψ (mk F v hv)).rep_nonzero
  ext j
  by_cases hij : i = j
  · subst j
    exact hz
  · simpa only [hz, mul_zero, Pi.zero_apply] using
      image_coordinate_relation ψ hψ haxes v hv i j hij (v j) (by simp only [hi, mul_one])

private theorem coordinateParameter_one (ψ : Equiv.Perm (ProjectivePoint F))
    (hψ : PreservesLines ψ) (haxes : ∀ i : Index, ψ (axis i) = axis i)
    (hdiag : ψ diagonalPoint = diagonalPoint) (i j : Index) (hij : i ≠ j) :
    coordinateParameter ψ hψ haxes i j hij 1 = 1 := by
  have hle : (diagonalPoint (F := F)).submodule ≤ coordinateHyperplane i j 1 := by
    rw [diagonalPoint, submodule_mk, Submodule.span_singleton_le_iff_mem]
    exact (one_mul _).symm
  have hm := (submoduleOrderIso ψ hψ).monotone hle
  rw [submoduleOrderIso_point, hdiag, map_coordinateHyperplane ψ hψ haxes i j hij,
    diagonalPoint, submodule_mk, Submodule.span_singleton_le_iff_mem] at hm
  change (1 : F) = coordinateParameter ψ hψ haxes i j hij 1 * 1 at hm
  exact (hm.trans (mul_one _)).symm

private def tripleVector (i j k : Index) (x y : F) : Vector F :=
  Pi.single i 1 + x • Pi.single j 1 + y • Pi.single k 1

private theorem tripleVector_i (i j k : Index) (hij : i ≠ j) (hik : i ≠ k) (x y : F) :
    tripleVector i j k x y i = 1 := by simp [tripleVector, hij, hik]

private theorem tripleVector_j (i j k : Index) (hij : i ≠ j) (hjk : j ≠ k) (x y : F) :
    tripleVector i j k x y j = x := by simp [tripleVector, hij.symm, hjk]

private theorem tripleVector_k (i j k : Index) (hik : i ≠ k) (hjk : j ≠ k) (x y : F) :
    tripleVector i j k x y k = y := by simp [tripleVector, hik.symm, hjk.symm]

private theorem coordinateParameter_comp (ψ : Equiv.Perm (ProjectivePoint F))
    (hψ : PreservesLines ψ) (haxes : ∀ i : Index, ψ (axis i) = axis i)
    (i j k : Index) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x y : F) :
    coordinateParameter ψ hψ haxes i k hik (x * y) =
      coordinateParameter ψ hψ haxes i j hij x * coordinateParameter ψ hψ haxes j k hjk y := by
  let v := tripleVector i j k x (x * y)
  have hi : v i = 1 := tripleVector_i i j k hij hik x (x * y)
  have hj : v j = x := tripleVector_j i j k hij hjk x (x * y)
  have hk : v k = x * y := tripleVector_k i j k hik hjk x (x * y)
  have hv : v ≠ 0 := by intro h; have := congrFun h i; simp only [hi, Pi.zero_apply] at this; exact one_ne_zero this
  let q := ψ (mk F v hv)
  have hqi : q.rep i ≠ 0 := image_pivot_ne_zero ψ hψ haxes v hv i hi
  have hqj := image_coordinate_relation ψ hψ haxes v hv i j hij x (by rw [hi, hj, mul_one])
  have hqk := image_coordinate_relation ψ hψ haxes v hv i k hik (x * y) (by rw [hi, hk, mul_one])
  have hqjk := image_coordinate_relation ψ hψ haxes v hv j k hjk y (by rw [hj, hk, mul_comm])
  apply mul_right_cancel₀ hqi
  rw [← hqk, hqjk, hqj]
  ring

private theorem coordinateParameter_same_left (ψ : Equiv.Perm (ProjectivePoint F))
    (hψ : PreservesLines ψ) (haxes : ∀ i : Index, ψ (axis i) = axis i)
    (hdiag : ψ diagonalPoint = diagonalPoint)
    (i j k : Index) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x : F) :
    coordinateParameter ψ hψ haxes i k hik x =
      coordinateParameter ψ hψ haxes i j hij x := by
  have h := coordinateParameter_comp ψ hψ haxes i j k hij hik hjk x 1
  simpa only [mul_one, coordinateParameter_one ψ hψ haxes hdiag j k hjk,
    mul_one] using h

private theorem coordinateParameter_same_right (ψ : Equiv.Perm (ProjectivePoint F))
    (hψ : PreservesLines ψ) (haxes : ∀ i : Index, ψ (axis i) = axis i)
    (hdiag : ψ diagonalPoint = diagonalPoint)
    (i j k : Index) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x : F) :
    coordinateParameter ψ hψ haxes i k hik x =
      coordinateParameter ψ hψ haxes j k hjk x := by
  have h := coordinateParameter_comp ψ hψ haxes i j k hij hik hjk 1 x
  simpa only [one_mul, coordinateParameter_one ψ hψ haxes hdiag i j hij,
    one_mul] using h

private theorem coordinateParameter_eq_base (ψ : Equiv.Perm (ProjectivePoint F))
    (hψ : PreservesLines ψ) (haxes : ∀ i : Index, ψ (axis i) = axis i)
    (hdiag : ψ diagonalPoint = diagonalPoint)
    (i j : Index) (hij : i ≠ j) (x : F) :
    coordinateParameter ψ hψ haxes i j hij x =
      coordinateParameter ψ hψ haxes (.inl 0) (.inl 1) (by decide) x := by
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals try exact (hij rfl).elim
  · simpa using (coordinateParameter_same_left ψ hψ haxes hdiag (Sum.inl 0) (Sum.inl 1) (Sum.inr 0) (by decide) (by decide) (by decide) x)
  · simpa using (coordinateParameter_same_left ψ hψ haxes hdiag (Sum.inl 0) (Sum.inl 1) (Sum.inr 1) (by decide) (by decide) (by decide) x)
  · simpa using ((coordinateParameter_same_left ψ hψ haxes hdiag (Sum.inl 1) (Sum.inr 0) (Sum.inl 0) (by decide) (by decide) (by decide) x).trans
      ((coordinateParameter_same_right ψ hψ haxes hdiag (Sum.inl 1) (Sum.inl 0) (Sum.inr 0) (by decide) (by decide) (by decide) x).trans
        (coordinateParameter_same_left ψ hψ haxes hdiag (Sum.inl 0) (Sum.inl 1) (Sum.inr 0) (by decide) (by decide) (by decide) x)))
  · simpa using ((coordinateParameter_same_right ψ hψ haxes hdiag (Sum.inl 0) (Sum.inl 1) (Sum.inr 0) (by decide) (by decide) (by decide) x).symm.trans
      (coordinateParameter_same_left ψ hψ haxes hdiag (Sum.inl 0) (Sum.inl 1) (Sum.inr 0) (by decide) (by decide) (by decide) x))
  · simpa using ((coordinateParameter_same_right ψ hψ haxes hdiag (Sum.inl 0) (Sum.inl 1) (Sum.inr 1) (by decide) (by decide) (by decide) x).symm.trans
      (coordinateParameter_same_left ψ hψ haxes hdiag (Sum.inl 0) (Sum.inl 1) (Sum.inr 1) (by decide) (by decide) (by decide) x))
  · simpa using ((coordinateParameter_same_left ψ hψ haxes hdiag (Sum.inr 0) (Sum.inl 1) (Sum.inl 0) (by decide) (by decide) (by decide) x).trans
      (coordinateParameter_same_right ψ hψ haxes hdiag (Sum.inr 0) (Sum.inl 0) (Sum.inl 1) (by decide) (by decide) (by decide) x))
  · simpa using (coordinateParameter_same_right ψ hψ haxes hdiag (Sum.inr 0) (Sum.inl 0) (Sum.inl 1) (by decide) (by decide) (by decide) x)
  · simpa using ((coordinateParameter_same_right ψ hψ haxes hdiag (Sum.inr 0) (Sum.inl 0) (Sum.inr 1) (by decide) (by decide) (by decide) x).trans
      (coordinateParameter_same_left ψ hψ haxes hdiag (Sum.inl 0) (Sum.inl 1) (Sum.inr 1) (by decide) (by decide) (by decide) x))
  · simpa using ((coordinateParameter_same_left ψ hψ haxes hdiag (Sum.inr 1) (Sum.inl 1) (Sum.inl 0) (by decide) (by decide) (by decide) x).trans
      (coordinateParameter_same_right ψ hψ haxes hdiag (Sum.inr 1) (Sum.inl 0) (Sum.inl 1) (by decide) (by decide) (by decide) x))
  · simpa using (coordinateParameter_same_right ψ hψ haxes hdiag (Sum.inr 1) (Sum.inl 0) (Sum.inl 1) (by decide) (by decide) (by decide) x)
  · simpa using ((coordinateParameter_same_right ψ hψ haxes hdiag (Sum.inr 1) (Sum.inl 0) (Sum.inr 0) (by decide) (by decide) (by decide) x).trans
      (coordinateParameter_same_left ψ hψ haxes hdiag (Sum.inl 0) (Sum.inl 1) (Sum.inr 0) (by decide) (by decide) (by decide) x))

private theorem coordinateParameter_add (ψ : Equiv.Perm (ProjectivePoint F))
    (hψ : PreservesLines ψ) (haxes : ∀ i : Index, ψ (axis i) = axis i)
    (hdiag : ψ diagonalPoint = diagonalPoint)
    (i j k : Index) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x y : F) :
    coordinateParameter ψ hψ haxes i j hij (x + y) =
      coordinateParameter ψ hψ haxes i j hij x +
        coordinateParameter ψ hψ haxes i j hij y := by
  let v := tripleVector i j k (x + y) 1
  have hi : v i = 1 := tripleVector_i i j k hij hik (x + y) 1
  have hj : v j = x + y := tripleVector_j i j k hij hjk (x + y) 1
  have hk : v k = 1 := tripleVector_k i j k hik hjk (x + y) 1
  have hv : v ≠ 0 := by
    intro h
    have h := congrFun h i
    simp only [hi, Pi.zero_apply] at h
    exact one_ne_zero h
  let p := pairPoint i j hij x
  let q := pairPoint k j hjk.symm y
  have hpq : (mk F v hv).submodule ≤ p.submodule ⊔ q.submodule := by
    rw [submodule_mk, Submodule.span_singleton_le_iff_mem]
    apply Submodule.mem_sup.mpr
    refine ⟨Pi.single i 1 + x • Pi.single j 1, ?_,
      Pi.single k 1 + y • Pi.single j 1, ?_, ?_⟩
    · exact Submodule.mem_span_singleton_self _
    · exact Submodule.mem_span_singleton_self _
    · ext r
      by_cases hri : r = i
      · subst r; simp [v, tripleVector, hij, hik]
      by_cases hrj : r = j
      · subst r; simp [v, tripleVector, hij.symm, hjk]
      by_cases hrk : r = k
      · subst r; simp [v, tripleVector, hik, hjk.symm]
      · simp [v, tripleVector, hri, hrj, hrk]
  have himage := (hψ p q (mk F v hv)).mpr hpq
  have hp' : ψ p = pairPoint i j hij
      (coordinateParameter ψ hψ haxes i j hij x) := coordinateParameter_spec ψ hψ haxes i j hij x
  have hq' : ψ q = pairPoint k j hjk.symm
      (coordinateParameter ψ hψ haxes k j hjk.symm y) := coordinateParameter_spec ψ hψ haxes k j hjk.symm y
  have hrep : (ψ (mk F v hv)).rep ∈ (ψ (mk F v hv)).submodule := by
    rw [submodule_eq]
    exact Submodule.mem_span_singleton_self _
  have hmem := himage hrep
  rw [hp', hq'] at hmem
  simp only [pairPoint, submodule_mk] at hmem
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hu
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hw
  rw [← ha, ← hb] at huw
  have hi' := congrFun huw i
  have hj' := congrFun huw j
  have hk' := congrFun huw k
  have hzi : (ψ (mk F v hv)).rep i ≠ 0 := image_pivot_ne_zero ψ hψ haxes v hv i hi
  have hratioik := image_coordinate_relation ψ hψ haxes v hv i k hik 1 (by rw [hi, hk, mul_one])
  have hratioij := image_coordinate_relation ψ hψ haxes v hv i j hij (x + y) (by rw [hi, hj, mul_one])
  have heqik := coordinateParameter_eq_base ψ hψ haxes hdiag i k hik 1
  have heqij := coordinateParameter_eq_base ψ hψ haxes hdiag i j hij (x + y)
  have heqijx := coordinateParameter_eq_base ψ hψ haxes hdiag i j hij x
  have heqijy := coordinateParameter_eq_base ψ hψ haxes hdiag i j hij y
  have heqkjy := coordinateParameter_eq_base ψ hψ haxes hdiag k j hjk.symm y
  rw [heqik, coordinateParameter_one ψ hψ haxes hdiag _ _ (by decide)] at hratioik
  rw [heqij] at hratioij
  rw [heqijx, heqkjy] at hj'
  simp [smul_eq_mul, hij, hij.symm, hik, hik.symm, hjk, hjk.symm]
    at hi' hj' hk' hratioik hratioij
  rw [hi', hk', hratioik] at hj'
  apply mul_right_cancel₀ hzi
  rw [heqij, heqijx, heqijy]
  rw [← hratioij]
  rw [← hj']
  ring

theorem normalized_coordinate_field [Finite F] [CharP F 2]
    (_hF : Nat.card F ≠ 2) (ψ : Equiv.Perm (ProjectivePoint F))
    (hψ : PreservesLines ψ) (haxes : ∀ i : Index, ψ (axis i) = axis i)
    (hdiag : ψ diagonalPoint = diagonalPoint) :
    ∃ σ : F ≃+* F, ∀ (i j : Index) (hij : i ≠ j) (t : F),
      ψ (pairPoint i j hij t) = pairPoint i j hij (σ t) := by
  let i₀ : Index := .inl 0
  let j₀ : Index := .inl 1
  let k₀ : Index := .inr 0
  have hij₀ : i₀ ≠ j₀ := by decide
  have hik₀ : i₀ ≠ k₀ := by decide
  have hjk₀ : j₀ ≠ k₀ := by decide
  let f : F → F := coordinateParameter ψ hψ haxes i₀ j₀ hij₀
  have hf_zero : f 0 = 0 := by
    exact coordinateParameter_zero ψ hψ haxes i₀ j₀ hij₀
  have hf_one : f 1 = 1 := by
    exact coordinateParameter_one ψ hψ haxes hdiag i₀ j₀ hij₀
  have hf_inj : Function.Injective f := by
    exact coordinateParameter_injective ψ hψ haxes i₀ j₀ hij₀
  have hf_surj : Function.Surjective f := by
    exact coordinateParameter_surjective ψ hψ haxes i₀ j₀ hij₀
  have hf_mul (x y : F) : f (x * y) = f x * f y := by
    have h := coordinateParameter_comp ψ hψ haxes i₀ j₀ k₀
      hij₀ hik₀ hjk₀ x y
    have hr := coordinateParameter_same_right ψ hψ haxes hdiag i₀ j₀ k₀
      hij₀ hik₀ hjk₀ y
    have hl := coordinateParameter_same_left ψ hψ haxes hdiag i₀ j₀ k₀
      hij₀ hik₀ hjk₀ y
    have hlxy := coordinateParameter_same_left ψ hψ haxes hdiag i₀ j₀ k₀
      hij₀ hik₀ hjk₀ (x * y)
    dsimp [f] at h ⊢
    rw [← hr, hlxy, hl] at h
    exact h
  have hf_add (x y : F) : f (x + y) = f x + f y := by
    exact coordinateParameter_add ψ hψ haxes hdiag i₀ j₀ k₀
      hij₀ hik₀ hjk₀ x y
  let σhom : F →+* F :=
    { toFun := f
      map_one' := hf_one
      map_mul' := hf_mul
      map_zero' := hf_zero
      map_add' := hf_add }
  let σ : F ≃+* F := RingEquiv.ofBijective σhom ⟨hf_inj, hf_surj⟩
  refine ⟨σ, ?_⟩
  intro i j hij t
  have hs := coordinateParameter_spec ψ hψ haxes i j hij t
  have heq := coordinateParameter_eq_base ψ hψ haxes hdiag i j hij t
  change ψ (pairPoint i j hij t) = pairPoint i j hij (f t)
  rw [hs, heq]

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.Collineation
