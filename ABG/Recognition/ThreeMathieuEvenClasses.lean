module
public import ABG.Recognition.ThreeMathieuCharacterData
public import Theory.GroupTheory.InvolutionRoots

/-!
# The five even-order conjugacy classes in Wong's characteristic-three case

Fuse the unique involution of each even cyclic subgroup to the distinguished
involution, and then use the actual GL₂(3) representatives in its centralizer.
Uniqueness of an involution in a cyclic group prevents further fusion between
these root classes. Their centralizers remain inside the involution centralizer,
so the local cardinalities are also the ambient cardinalities. This gives the
five class orders 2,4,6,8,8, centralizer orders 48,8,6,8,8, and first-character
values 2,2,-1,0,0 without assuming a global character table.

Source: Wong (1964), Theorem 6(a), p.107,
DOI 10.1017/S1446788700022771. The even-class calculation also applies to the
other global degree alternative.
-/
open BenderGlauberman Matrix.GeneralLinearGroup
open scoped BigOperators
namespace ABG
noncomputable section
variable {G : Type*} [Group G] [Finite G] (c : ThreeGlobalDegreeData G)

private def centralizerEquiv {H : Type*} [Group H] (e : G ≃* H) (a : G) :
    Subgroup.centralizer ({a} : Set G) ≃ Subgroup.centralizer ({e a} : Set H) where
  toFun x := ⟨e x.val, Subgroup.mem_centralizer_singleton_iff.mpr (by
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp x.property])⟩
  invFun x := ⟨e.symm x.val, Subgroup.mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simp only [map_mul, e.apply_symm_apply]
    exact Subgroup.mem_centralizer_singleton_iff.mp x.property)⟩
  left_inv _ := Subtype.ext (e.symm_apply_apply _)
  right_inv _ := Subtype.ext (e.apply_symm_apply _)

private def rootCentralizerEquiv {t : G} (a : Subgroup.centralizer ({t} : Set G))
    (ha : t ∈ Subgroup.zpowers (a : G)) :
    Subgroup.centralizer ({(a : G)} : Set G) ≃
      Subgroup.centralizer ({a} : Set (Subgroup.centralizer ({t} : Set G))) := by
  have hc {g : G} (hg : g ∈ Subgroup.centralizer ({(a : G)} : Set G)) :
      g ∈ Subgroup.centralizer ({t} : Set G) := by
    obtain ⟨n, hn⟩ := ha
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change (a : G) ^ n = t at hn
    rw [← hn]
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hg) n).eq
  exact
    { toFun := fun g => ⟨⟨g.val, hc g.property⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.property))⟩
      invFun := fun g => ⟨g.val.val,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp g.property))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private def rootIndex : Fin 5 → Fin 8 := ![1,2,4,6,7]
private theorem rootIndex_mem (i : Fin 5) :
    rootIndex i = 1 ∨ rootIndex i = 2 ∨ rootIndex i = 4 ∨ rootIndex i = 6 ∨ rootIndex i = 7 := by
  fin_cases i <;> simp [rootIndex]
private theorem rootIndex_inj : Function.Injective rootIndex := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [rootIndex]

/-- Representatives of the five root classes, viewed in the actual centralizer. -/
public def ThreeGlobalDegreeData.evenRepresentative (i : Fin 5) :
    Subgroup.centralizer ({c.involution} : Set G) :=
  (threeCentralizerEquiv c.involution c.centralizerEquiv).symm (threeClassRepr (rootIndex i))

/-- Each representative has the distinguished involution in its cyclic subgroup. -/
public theorem ThreeGlobalDegreeData.evenRepresentative_root (i : Fin 5) :
    c.involution ∈ Subgroup.zpowers (c.evenRepresentative i : G) := by
  apply (threeCentralizerEquiv_root_iff c.involution c.order_involution c.centralizerEquiv _).mp
  simpa only [ThreeGlobalDegreeData.evenRepresentative, MulEquiv.apply_symm_apply] using
    (glTwoThreeRootSupport_class (rootIndex i)).mpr (rootIndex_mem i)

/-- The five ambient element orders. -/
public theorem ThreeGlobalDegreeData.evenRepresentative_order (i : Fin 5) :
    orderOf (c.evenRepresentative i : G) = ![2,4,6,8,8] i := by
  rw [Subgroup.orderOf_coe, ThreeGlobalDegreeData.evenRepresentative,
    MulEquiv.orderOf_eq, three_conjugacy_data.2.1]
  fin_cases i <;> rfl

/-- The five local root classes remain distinct in the ambient group. -/
public theorem ThreeGlobalDegreeData.evenRepresentative_not_fused (i j : Fin 5)
    (h : IsConj (c.evenRepresentative i : G) (c.evenRepresentative j : G)) : i = j := by
  have h' := (isConj_involution_roots_iff c.involution c.order_involution _ _
    (c.evenRepresentative_root i) (c.evenRepresentative_root j)).mp h
  have h'' := (threeCentralizerEquiv c.involution c.centralizerEquiv).toMonoidHom.map_isConj h'
  change IsConj
    ((threeCentralizerEquiv c.involution c.centralizerEquiv)
      ((threeCentralizerEquiv c.involution c.centralizerEquiv).symm (threeClassRepr (rootIndex i))))
    ((threeCentralizerEquiv c.involution c.centralizerEquiv)
      ((threeCentralizerEquiv c.involution c.centralizerEquiv).symm (threeClassRepr (rootIndex j)))) at h''
  simp only [MulEquiv.apply_symm_apply] at h''
  obtain ⟨k, hk, hu⟩ := three_conjugacy_data.1 (threeClassRepr (rootIndex i))
  exact rootIndex_inj ((hu _ (IsConj.refl _)).trans (hu _ h'').symm)

/-- Values of the first character on the five representatives. -/
public theorem ThreeGlobalDegreeData.first_evenRepresentative_value (i : Fin 5) :
    c.decomposition.χ 0 (c.evenRepresentative i) = (![2,2,-1,0,0] i : ℂ) := by
  have h := c.first_root_class_values (rootIndex i) (rootIndex_mem i)
  change c.decomposition.χ 0 (c.evenRepresentative i) = _ at h
  rw [h]
  fin_cases i <;> rfl

/-- The ambient centralizer orders of the five representatives. -/
public theorem ThreeGlobalDegreeData.evenRepresentative_centralizer_card (i : Fin 5) :
    Nat.card (Subgroup.centralizer ({(c.evenRepresentative i : G)} : Set G)) =
      ![48,8,6,8,8] i := by
  calc
    _ = Nat.card (Subgroup.centralizer ({c.evenRepresentative i} :
        Set (Subgroup.centralizer ({c.involution} : Set G)))) :=
      Nat.card_congr (rootCentralizerEquiv _ (c.evenRepresentative_root i))
    _ = Nat.card (Subgroup.centralizer
        ({threeCentralizerEquiv c.involution c.centralizerEquiv (c.evenRepresentative i)} :
          Set (GL (Fin 2) (ZMod 3)))) :=
      Nat.card_congr (centralizerEquiv (threeCentralizerEquiv c.involution c.centralizerEquiv)
        (c.evenRepresentative i))
    _ = _ := by
      simp only [ThreeGlobalDegreeData.evenRepresentative, MulEquiv.apply_symm_apply,
        three_conjugacy_data.2.2.1]
      fin_cases i <;> rfl

/-- Every even-order element belongs to precisely one of the five classes. -/
public theorem ThreeGlobalDegreeData.even_conjugacy_coverage
    [IsSimpleGroup G] (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (x : G) (hx : 2 ∣ orderOf x) :
    ∃! i : Fin 5, IsConj x (c.evenRepresentative i : G) := by
  have hQD := isQDGroup_of_simple ⟨S, hS⟩
  have hclass : HasElementConjugacyClassCount G 2 1 := by
    rcases hQD with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.2.1
  have hfuse (u : G) (hu : orderOf u = 2) : IsConj u c.involution := by
    obtain ⟨r, _, _, hcov⟩ := hclass
    obtain ⟨i, hi⟩ := hcov u hu
    obtain ⟨j, hj⟩ := hcov c.involution c.order_involution
    exact hi.trans ((Subsingleton.elim i j) ▸ hj.symm)
  obtain ⟨a, ha, hxa⟩ := exists_isConj_involution_root c.involution hfuse x hx
  let e := threeCentralizerEquiv c.involution c.centralizerEquiv
  obtain ⟨j, hj, _⟩ := three_conjugacy_data.1 (e a)
  have hroot : threeClassRepr j ∈ glTwoThreeRootSupport := by
    exact (threeCentral_mem_zpowers_isConj hj).mp
      ((threeCentralizerEquiv_root_iff c.involution c.order_involution c.centralizerEquiv a).mpr ha)
  have hji : ∃ i : Fin 5, rootIndex i = j := by
    rcases (glTwoThreeRootSupport_class j).mp hroot with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
  obtain ⟨i, rfl⟩ := hji
  have hlocal : IsConj a (c.evenRepresentative i) := by
    have h := e.symm.toMonoidHom.map_isConj hj
    change IsConj (e.symm (e a)) (e.symm (threeClassRepr (rootIndex i))) at h
    simpa only [MulEquiv.symm_apply_apply, e, ThreeGlobalDegreeData.evenRepresentative] using h
  have hi := hxa.trans ((Subgroup.centralizer ({c.involution} : Set G)).subtype.map_isConj hlocal)
  exact ⟨i, hi, fun j hj => c.evenRepresentative_not_fused j i (hj.symm.trans hi)⟩

include c in
/-- Ambient centralizer orders depend only on the even element order. -/
public theorem ThreeGlobalDegreeData.even_centralizer_card
    [IsSimpleGroup G] (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (x : G) (hx : 2 ∣ orderOf x) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) =
      if orderOf x = 2 then 48 else if orderOf x = 6 then 6 else 8 := by
  obtain ⟨i, hi, _⟩ := c.even_conjugacy_coverage S hS x hx
  obtain ⟨g, hg⟩ := isConj_iff.mp hi
  have horder : orderOf x = ![2,4,6,8,8] i := by
    rw [← c.evenRepresentative_order i, ← hg]
    exact (MulAut.conj g).orderOf_eq x |>.symm
  have hcard : Nat.card (Subgroup.centralizer ({x} : Set G)) = ![48,8,6,8,8] i := by
    calc
      _ = Nat.card (Subgroup.centralizer ({MulAut.conj g x} : Set G)) :=
        Nat.card_congr (centralizerEquiv (MulAut.conj g) x)
      _ = _ := by
        change Nat.card (Subgroup.centralizer ({g * x * g⁻¹} : Set G)) = _
        rw [hg, c.evenRepresentative_centralizer_card]
  rw [hcard, horder]
  fin_cases i <;> norm_num

include c in
/-- There are no even element orders other than 2,4,6,8. -/
public theorem ThreeGlobalDegreeData.even_order_exhaustion
    [IsSimpleGroup G] (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (x : G) (hx : 2 ∣ orderOf x) :
    orderOf x = 2 ∨ orderOf x = 4 ∨ orderOf x = 6 ∨ orderOf x = 8 := by
  obtain ⟨i, hi, _⟩ := c.even_conjugacy_coverage S hS x hx
  obtain ⟨g, hg⟩ := isConj_iff.mp hi
  have horder : orderOf x = ![2,4,6,8,8] i := by
    rw [← c.evenRepresentative_order i, ← hg]
    exact (MulAut.conj g).orderOf_eq x |>.symm
  fin_cases i <;> simp_all

/-- The first character on arbitrary even-order elements. -/
public theorem ThreeGlobalDegreeData.first_character_even_values
    [IsSimpleGroup G] (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (x : G) (hx : 2 ∣ orderOf x) :
    c.decomposition.χ 0 x = if orderOf x = 6 then -1 else if orderOf x = 8 then 0 else 2 := by
  obtain ⟨i, hi, _⟩ := c.even_conjugacy_coverage S hS x hx
  obtain ⟨g, hg⟩ := isConj_iff.mp hi
  have horder : orderOf x = ![2,4,6,8,8] i := by
    rw [← c.evenRepresentative_order i, ← hg]
    exact (MulAut.conj g).orderOf_eq x |>.symm
  have hval : c.decomposition.χ 0 x = (![2,2,-1,0,0] i : ℂ) := by
    rw [← c.first_evenRepresentative_value i, ← hg]
    exact (irreducibleCharacter_isClassFunction (c.decomposition.irreducible 0) x g).symm
  rw [hval, horder]
  fin_cases i <;> norm_num
end
end ABG
