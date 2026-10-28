module

public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortFamilies.Basic

/-!
# The pure-four short extraspecial family

The actual source words `r_u(xy)` and `r_v(xy)` reduce to the two vectors
`4(e_x + e_y)` and `4(e_x - e_y)`. Their norm is four in the Leech
normalization. Recovering the two nonzero coordinates from the ATLAS
pure-four shell proves exhaustion, including both central signs.

The group elements depend on the unordered coordinate pair. Swapping the
coordinates negates the chosen representative for `r_v` but fixes its group
element; the rank-one tensor and vector correction therefore stay well defined.
Equality of minimal lattice classes determines the unordered support pair,
and separates the `u` and `v` families. Their signed vectors are orthonormal.
The vectors `wPlus = v + u` and `wMinus = v - u` are orthogonal families
of squared norm two, with the source recovery identities for `u` and `v`.

This proves the pure-four branch of 27.8(4) and its vector relations in
27.8(5). The whole-space splitting also requires the octad and odd branches.
Source: Michael Aschbacher, *Sporadic Groups*, Lemma 27.8, printed p. 150
(PDF page 81, left page). The shell classifications are the existing
attributed ATLAS ports.
-/

@[expose] public section
noncomputable section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
open scoped BigOperators
namespace Sporadic.Monster.Construction.LocalC.ShortFamilies
open TrialitySpin
attribute [local instance] Classical.propDecidable

theorem ruElement_class (x y : Omega) :
    latticeClass sourceLatticeComparison (ruElement x y) = leechReduction (uRepresentative x y) := by
  rw [ruElement, latticeClass_mul, loopImage_class, cocodeImage_class, sourceWordClass_pair]
  change leechReduction (sourceCodeVector golayOne) + _ = _
  simp only [uRepresentative, map_add]
  abel

theorem rvElement_class (x y : Omega) :
    latticeClass sourceLatticeComparison (rvElement x y) = leechReduction (vRepresentative x y) := by
  rw [rvElement, cocodeImage_class, sourceWordClass_pair]
  simp [vRepresentative, sub_eq_add_neg, leechReduction_neg]

theorem uRepresentative_apply (x y i : Omega) :
    (uRepresentative x y).val i = (if i = x then 4 else 0) + (if i = y then 4 else 0) := by
  change (sourcePointVector x).val i + (sourcePointVector y).val i +
    (sourceCodeVector golayOne).val i = _
  rw [sourcePointVector_apply, sourcePointVector_apply, sourceCodeVector_one_apply]
  ring

theorem vRepresentative_apply (x y i : Omega) :
    (vRepresentative x y).val i = (if i = x then 4 else 0) - (if i = y then 4 else 0) := by
  change (sourcePointVector x).val i - (sourcePointVector y).val i = _
  rw [sourcePointVector_apply, sourcePointVector_apply]
  ring

theorem uRepresentative_norm (x y : Omega) (hxy : x ≠ y) :
    integerDot (uRepresentative x y).val (uRepresentative x y).val = 32 := by
  have h (i : Omega) : (uRepresentative x y).val i * (uRepresentative x y).val i =
      (if i = x then 16 else 0) + (if i = y then 16 else 0) := by
    rw [uRepresentative_apply]
    by_cases hx : i = x <;> by_cases hy : i = y <;> simp_all
  simp [integerDot, h, Finset.sum_add_distrib]

theorem vRepresentative_norm (x y : Omega) (hxy : x ≠ y) :
    integerDot (vRepresentative x y).val (vRepresentative x y).val = 32 := by
  have h (i : Omega) : (vRepresentative x y).val i * (vRepresentative x y).val i =
      (if i = x then 16 else 0) + (if i = y then 16 else 0) := by
    rw [vRepresentative_apply]
    by_cases hx : i = x <;> by_cases hy : i = y <;> simp_all
  simp [integerDot, h, Finset.sum_add_distrib]

def uShell (x y : Omega) (hxy : x ≠ y) : LeechShell 4 :=
  ⟨uRepresentative x y, uRepresentative_norm x y hxy⟩

def vShell (x y : Omega) (hxy : x ≠ y) : LeechShell 4 :=
  ⟨vRepresentative x y, vRepresentative_norm x y hxy⟩

def ru (x y : Omega) (hxy : x ≠ y) : Lift :=
  ofRepresentative (ruElement x y) (uShell x y hxy) (ruElement_class x y)

def rv (x y : Omega) (hxy : x ≠ y) : Lift :=
  ofRepresentative (rvElement x y) (vShell x y hxy) (rvElement_class x y)

theorem ru_class (x y : Omega) (hxy : x ≠ y) :
    shortLiftClass sourceLatticeComparison (ru x y hxy) = shortReduction (uShell x y hxy) :=
  ofRepresentative_class _ _ _

theorem rv_class (x y : Omega) (hxy : x ≠ y) :
    shortLiftClass sourceLatticeComparison (rv x y hxy) = shortReduction (vShell x y hxy) :=
  ofRepresentative_class _ _ _

theorem ru_tensor (x y : Omega) (hxy : x ≠ y) :
    shortLiftTensor sourceLatticeComparison (ru x y hxy) = rankOne (leechVector (uRepresentative x y)) :=
  ofRepresentative_tensor _ _ _

theorem rv_tensor (x y : Omega) (hxy : x ≠ y) :
    shortLiftTensor sourceLatticeComparison (rv x y hxy) = rankOne (leechVector (vRepresentative x y)) :=
  ofRepresentative_tensor _ _ _

theorem ru_correction (x y : Omega) (hxy : x ≠ y) (a : NaturalSpace) :
    shortLiftCorrection sourceLatticeComparison (ru x y hxy) a =
      vectorCorrection (leechVector (uRepresentative x y)) a :=
  ofRepresentative_correction _ _ _ _

theorem rv_correction (x y : Omega) (hxy : x ≠ y) (a : NaturalSpace) :
    shortLiftCorrection sourceLatticeComparison (rv x y hxy) a =
      vectorCorrection (leechVector (vRepresentative x y)) a :=
  ofRepresentative_correction _ _ _ _

theorem pureFour_representatives (v : LeechShell 4) (hv : v.val.val ∈ twoFourFamily 0 2) :
    ∃ x y : Omega, x ≠ y ∧
      (v.val = uRepresentative x y ∨ v.val = -uRepresentative x y ∨
        v.val = vRepresentative x y ∨ v.val = -vRepresentative x y) := by
  obtain ⟨hb, htwo, hfour⟩ := twoFourFamily_shape 0 2 _ hv
  obtain ⟨x,y,hxy,hs⟩ := Finset.card_eq_two.mp hfour
  have htwo' : evenMagnitudeSupport v.val.val 2 = ∅ := Finset.card_eq_zero.mp htwo
  have small (i : Omega) : v.val.val i = -4 ∨ v.val.val i = 0 ∨ v.val.val i = 4 := by
    have hn : v.val.val i * v.val.val i ≠ 4 := by
      intro hh
      have hm : i ∈ evenMagnitudeSupport v.val.val 2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩
      rw [htwo'] at hm
      exact Finset.notMem_empty _ hm
    rcases hb i with h | h | h | h | h <;> simp_all
  have at_pair (i : Omega) (hi : i = x ∨ i = y) :
      v.val.val i = -4 ∨ v.val.val i = 4 := by
    have hm : i ∈ evenMagnitudeSupport v.val.val 4 := by simp [hs, hi]
    have hm := (Finset.mem_filter.mp hm).2
    rcases small i with h | h | h <;> simp_all
  have outside (i : Omega) (hx : i ≠ x) (hy : i ≠ y) : v.val.val i = 0 := by
    have hn : i ∉ evenMagnitudeSupport v.val.val 4 := by simp [hs,hx,hy]
    have hn : v.val.val i * v.val.val i ≠ 16 := by
      intro hh
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
    rcases small i with h | h | h <;> simp_all
  refine ⟨x,y,hxy,?_⟩
  rcases at_pair x (Or.inl rfl) with hx | hx <;>
    rcases at_pair y (Or.inr rfl) with hy | hy
  · apply Or.inr ∘ Or.inl
    apply Subtype.ext
    funext i
    change v.val.val i = -(uRepresentative x y).val i
    rw [uRepresentative_apply]
    by_cases hi : i = x
    · simp [hi,hx,hxy]
    · by_cases hj : i = y
      · simp [hj,hy,hxy.symm]
      · simp [hi,hj,outside i hi hj]
  · apply Or.inr ∘ Or.inr ∘ Or.inr
    apply Subtype.ext
    funext i
    change v.val.val i = -(vRepresentative x y).val i
    rw [vRepresentative_apply]
    by_cases hi : i = x
    · simp [hi,hx,hxy]
    · by_cases hj : i = y
      · simp [hj,hy,hxy.symm]
      · simp [hi,hj,outside i hi hj]
  · apply Or.inr ∘ Or.inr ∘ Or.inl
    apply Subtype.ext
    funext i
    rw [vRepresentative_apply]
    by_cases hi : i = x
    · simp [hi,hx,hxy]
    · by_cases hj : i = y
      · simp [hj,hy,hxy.symm]
      · simp [hi,hj,outside i hi hj]
  · apply Or.inl
    apply Subtype.ext
    funext i
    rw [uRepresentative_apply]
    by_cases hi : i = x
    · simp [hi,hx,hxy]
    · by_cases hj : i = y
      · simp [hj,hy,hxy.symm]
      · simp [hi,hj,outside i hi hj]

theorem pureFour_exhaustion (q : Lift) (hq : HasShape (twoFourFamily 0 2) q) :
    ∃ x y : Omega, ∃ hxy : x ≠ y,
      q = ru x y hxy ∨ q = (shortLiftSigns sourceLatticeComparison).flip (ru x y hxy) ∨
        q = rv x y hxy ∨ q = (shortLiftSigns sourceLatticeComparison).flip (rv x y hxy) := by
  obtain ⟨v,hv,hs⟩ := hq
  obtain ⟨x,y,hxy,he⟩ := pureFour_representatives v hs
  refine ⟨x,y,hxy,?_⟩
  have hu (he : v.val = uRepresentative x y ∨ v.val = -uRepresentative x y) :
      q = ru x y hxy ∨ q = (shortLiftSigns sourceLatticeComparison).flip (ru x y hxy) := by
    apply (shortLiftClass_eq_iff sourceLatticeComparison _ _).mp
    rw [ru_class, ← hv]
    exact (shortReduction_eq_iff _ _).mpr he
  have hw (he : v.val = vRepresentative x y ∨ v.val = -vRepresentative x y) :
      q = rv x y hxy ∨ q = (shortLiftSigns sourceLatticeComparison).flip (rv x y hxy) := by
    apply (shortLiftClass_eq_iff sourceLatticeComparison _ _).mp
    rw [rv_class, ← hv]
    exact (shortReduction_eq_iff _ _).mpr he
  rcases he with h | h | h | h
  · exact (hu (Or.inl h)).imp_right Or.inl
  · exact (hu (Or.inr h)).imp_right Or.inl
  · exact Or.inr (Or.inr (hw (Or.inl h)))
  · exact Or.inr (Or.inr (hw (Or.inr h)))

theorem ru_swap (x y : Omega) (hxy : x ≠ y) : ru x y hxy = ru y x hxy.symm := by
  apply Subtype.ext
  change ruElement x y = ruElement y x
  simp only [ruElement, pairWord, add_comm]

theorem rv_swap (x y : Omega) (hxy : x ≠ y) : rv x y hxy = rv y x hxy.symm := by
  apply Subtype.ext
  change rvElement x y = rvElement y x
  simp only [rvElement, pairWord, add_comm]

theorem uRepresentative_swap (x y : Omega) : uRepresentative x y = uRepresentative y x := by
  simp only [uRepresentative, add_comm]

theorem vRepresentative_swap (x y : Omega) : vRepresentative x y = -vRepresentative y x := by
  simp [vRepresentative]

theorem ru_rv_classes_ne (x y : Omega) (hxy : x ≠ y) :
    shortLiftClass sourceLatticeComparison (ru x y hxy) ≠
      shortLiftClass sourceLatticeComparison (rv x y hxy) := by
  rw [ru_class,rv_class]
  intro h
  rcases (shortReduction_eq_iff _ _).mp h with h | h
  · have hy := congrArg (fun v : leech => v.val y) h
    simp [uShell,vShell,uRepresentative_apply,vRepresentative_apply,hxy.symm] at hy
  · have hx := congrArg (fun v : leech => v.val x) h
    change (uRepresentative x y).val x = -(vRepresentative x y).val x at hx
    simp [uRepresentative_apply,vRepresentative_apply,hxy] at hx

/-- The source signed vector `u_xy = y(r_u(xy))`. -/
def u (x y : Omega) (hxy : x ≠ y) : Space := shortVector sourceLatticeComparison (ru x y hxy)

/-- The source signed vector `v_xy = y(r_v(xy))`. -/
def v (x y : Omega) (hxy : x ≠ y) : Space := shortVector sourceLatticeComparison (rv x y hxy)

/-- The source vector `w_xy^2`. -/
def wPlus (x y : Omega) (hxy : x ≠ y) : Space := v x y hxy + u x y hxy

/-- The source vector `w_xy^3`. -/
def wMinus (x y : Omega) (hxy : x ≠ y) : Space := v x y hxy - u x y hxy

theorem form_u_v (x y : Omega) (hxy : x ≠ y) :
    shortForm sourceLatticeComparison (u x y hxy) (v x y hxy) = 0 :=
  form_vector_eq_zero _ _ (ru_rv_classes_ne x y hxy)

theorem form_u_u (x y : Omega) (hxy : x ≠ y) :
    shortForm sourceLatticeComparison (u x y hxy) (u x y hxy) = 1 :=
  shortForm_vector_self _ _

theorem form_v_v (x y : Omega) (hxy : x ≠ y) :
    shortForm sourceLatticeComparison (v x y hxy) (v x y hxy) = 1 :=
  shortForm_vector_self _ _

theorem form_wPlus_wMinus (x y : Omega) (hxy : x ≠ y) :
    shortForm sourceLatticeComparison (wPlus x y hxy) (wMinus x y hxy) = 0 := by
  have hvu := (shortForm_symmetric sourceLatticeComparison (v x y hxy) (u x y hxy)).trans
    (form_u_v x y hxy)
  simp [wPlus,wMinus,map_add,map_sub,form_u_u,form_v_v,form_u_v,hvu]

theorem form_wPlus_self (x y : Omega) (hxy : x ≠ y) :
    shortForm sourceLatticeComparison (wPlus x y hxy) (wPlus x y hxy) = 2 := by
  have hvu := (shortForm_symmetric sourceLatticeComparison (v x y hxy) (u x y hxy)).trans
    (form_u_v x y hxy)
  norm_num [wPlus,map_add,form_u_u,form_v_v,form_u_v,hvu]

theorem form_wMinus_self (x y : Omega) (hxy : x ≠ y) :
    shortForm sourceLatticeComparison (wMinus x y hxy) (wMinus x y hxy) = 2 := by
  have hvu := (shortForm_symmetric sourceLatticeComparison (v x y hxy) (u x y hxy)).trans
    (form_u_v x y hxy)
  norm_num [wMinus,map_sub,form_u_u,form_v_v,form_u_v,hvu]

theorem wPlus_add_wMinus (x y : Omega) (hxy : x ≠ y) :
    wPlus x y hxy + wMinus x y hxy = (2 : ℝ) • v x y hxy := by
  simp only [wPlus,wMinus,two_smul]
  abel

theorem wPlus_sub_wMinus (x y : Omega) (hxy : x ≠ y) :
    wPlus x y hxy - wMinus x y hxy = (2 : ℝ) • u x y hxy := by
  simp only [wPlus,wMinus,two_smul]
  abel

theorem u_four_support (x y : Omega) (hxy : x ≠ y) :
    evenMagnitudeSupport (uRepresentative x y).val 4 = {x,y} := by
  ext i
  simp only [evenMagnitudeSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    uRepresentative_apply, Finset.mem_insert, Finset.mem_singleton]
  by_cases hi : i = x <;> by_cases hj : i = y <;> simp_all

theorem v_four_support (x y : Omega) (hxy : x ≠ y) :
    evenMagnitudeSupport (vRepresentative x y).val 4 = {x,y} := by
  ext i
  simp only [evenMagnitudeSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    vRepresentative_apply, Finset.mem_insert, Finset.mem_singleton]
  by_cases hi : i = x <;> by_cases hj : i = y <;> simp_all

theorem uRepresentative_mem (x y : Omega) (hxy : x ≠ y) :
    (uRepresentative x y).val ∈ twoFourFamily 0 2 := by
  apply (twoFourFamily_iff _ _ _).mpr
  refine ⟨(uRepresentative x y).prop, ?_, ?_, ?_⟩
  · intro i
    rw [uRepresentative_apply]
    by_cases hi : i = x <;> by_cases hj : i = y <;> simp_all
  · have h : evenMagnitudeSupport (uRepresentative x y).val 2 = ∅ := by
      ext i
      simp only [evenMagnitudeSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        uRepresentative_apply, Finset.notMem_empty, iff_false]
      by_cases hi : i = x <;> by_cases hj : i = y <;> simp_all
    rw [h, Finset.card_empty]
  · rw [u_four_support x y hxy, Finset.card_pair hxy]

theorem vRepresentative_mem (x y : Omega) (hxy : x ≠ y) :
    (vRepresentative x y).val ∈ twoFourFamily 0 2 := by
  apply (twoFourFamily_iff _ _ _).mpr
  refine ⟨(vRepresentative x y).prop, ?_, ?_, ?_⟩
  · intro i
    rw [vRepresentative_apply]
    by_cases hi : i = x <;> by_cases hj : i = y <;> simp_all
  · have h : evenMagnitudeSupport (vRepresentative x y).val 2 = ∅ := by
      ext i
      simp only [evenMagnitudeSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        vRepresentative_apply, Finset.notMem_empty, iff_false]
      by_cases hi : i = x <;> by_cases hj : i = y <;> simp_all
    rw [h, Finset.card_empty]
  · rw [v_four_support x y hxy, Finset.card_pair hxy]

theorem ru_hasShape (x y : Omega) (hxy : x ≠ y) :
    HasShape (twoFourFamily 0 2) (ru x y hxy) :=
  ⟨uShell x y hxy, (ru_class x y hxy).symm, uRepresentative_mem x y hxy⟩

theorem rv_hasShape (x y : Omega) (hxy : x ≠ y) :
    HasShape (twoFourFamily 0 2) (rv x y hxy) :=
  ⟨vShell x y hxy, (rv_class x y hxy).symm, vRepresentative_mem x y hxy⟩

/-- Lemma 27.8(4): exactly the two pair words and their central sign partners. -/
theorem pureFour_iff (q : Lift) : HasShape (twoFourFamily 0 2) q ↔
    ∃ x y : Omega, ∃ hxy : x ≠ y,
      q = ru x y hxy ∨ q = (shortLiftSigns sourceLatticeComparison).flip (ru x y hxy) ∨
        q = rv x y hxy ∨ q = (shortLiftSigns sourceLatticeComparison).flip (rv x y hxy) := by
  constructor
  · exact pureFour_exhaustion q
  · rintro ⟨x,y,hxy,h | h | h | h⟩ <;> subst q
    · exact ru_hasShape x y hxy
    · exact (hasShape_flip _ _).mpr (ru_hasShape x y hxy)
    · exact rv_hasShape x y hxy
    · exact (hasShape_flip _ _).mpr (rv_hasShape x y hxy)

theorem pairWord_support (x y : Omega) (hxy : x ≠ y) :
    pairWord x y = supportWord {x,y} := by
  ext i
  by_cases hi : i = x <;> by_cases hj : i = y <;>
    simp_all [pairWord,pointWord,supportWord]

theorem ru_eq_of_pair_eq (x y z t : Omega) (hxy : x ≠ y) (hzt : z ≠ t)
    (h : ({x,y} : Finset Omega) = {z,t}) : ru x y hxy = ru z t hzt := by
  apply Subtype.ext
  change ruElement x y = ruElement z t
  rw [ruElement,ruElement,pairWord_support x y hxy,pairWord_support z t hzt,h]

theorem rv_eq_of_pair_eq (x y z t : Omega) (hxy : x ≠ y) (hzt : z ≠ t)
    (h : ({x,y} : Finset Omega) = {z,t}) : rv x y hxy = rv z t hzt := by
  apply Subtype.ext
  change rvElement x y = rvElement z t
  rw [rvElement,rvElement,pairWord_support x y hxy,pairWord_support z t hzt,h]

theorem ru_class_eq_iff (x y z t : Omega) (hxy : x ≠ y) (hzt : z ≠ t) :
    shortLiftClass sourceLatticeComparison (ru x y hxy) =
      shortLiftClass sourceLatticeComparison (ru z t hzt) ↔ ({x,y} : Finset Omega) = {z,t} := by
  constructor
  · rw [ru_class,ru_class]
    intro h
    simpa only [uShell,u_four_support x y hxy,u_four_support z t hzt] using
      support_eq_of_reduction_eq _ _ h 4
  · intro h
    rw [ru_eq_of_pair_eq x y z t hxy hzt h]

theorem rv_class_eq_iff (x y z t : Omega) (hxy : x ≠ y) (hzt : z ≠ t) :
    shortLiftClass sourceLatticeComparison (rv x y hxy) =
      shortLiftClass sourceLatticeComparison (rv z t hzt) ↔ ({x,y} : Finset Omega) = {z,t} := by
  constructor
  · rw [rv_class,rv_class]
    intro h
    simpa only [vShell,v_four_support x y hxy,v_four_support z t hzt] using
      support_eq_of_reduction_eq _ _ h 4
  · intro h
    rw [rv_eq_of_pair_eq x y z t hxy hzt h]

theorem ru_rv_classes_ne_all (x y z t : Omega) (hxy : x ≠ y) (hzt : z ≠ t) :
    shortLiftClass sourceLatticeComparison (ru x y hxy) ≠
      shortLiftClass sourceLatticeComparison (rv z t hzt) := by
  intro h
  have hp : ({x,y} : Finset Omega) = {z,t} := by
    rw [ru_class,rv_class] at h
    simpa only [uShell,vShell,u_four_support x y hxy,v_four_support z t hzt] using
      support_eq_of_reduction_eq _ _ h 4
  rw [← rv_eq_of_pair_eq x y z t hxy hzt hp] at h
  exact ru_rv_classes_ne x y hxy h

theorem form_u_v_all (x y z t : Omega) (hxy : x ≠ y) (hzt : z ≠ t) :
    shortForm sourceLatticeComparison (u x y hxy) (v z t hzt) = 0 :=
  form_vector_eq_zero _ _ (ru_rv_classes_ne_all x y z t hxy hzt)

theorem form_u_u_all (x y z t : Omega) (hxy : x ≠ y) (hzt : z ≠ t) :
    shortForm sourceLatticeComparison (u x y hxy) (u z t hzt) =
      if ({x,y} : Finset Omega) = {z,t} then 1 else 0 := by
  split_ifs with h
  · have he := ru_eq_of_pair_eq x y z t hxy hzt h
    simpa only [u, he] using shortForm_vector_self sourceLatticeComparison (ru z t hzt)
  · exact form_vector_eq_zero _ _ (mt (ru_class_eq_iff x y z t hxy hzt).mp h)

theorem form_v_v_all (x y z t : Omega) (hxy : x ≠ y) (hzt : z ≠ t) :
    shortForm sourceLatticeComparison (v x y hxy) (v z t hzt) =
      if ({x,y} : Finset Omega) = {z,t} then 1 else 0 := by
  split_ifs with h
  · have he := rv_eq_of_pair_eq x y z t hxy hzt h
    simpa only [v, he] using shortForm_vector_self sourceLatticeComparison (rv z t hzt)
  · exact form_vector_eq_zero _ _ (mt (rv_class_eq_iff x y z t hxy hzt).mp h)

theorem form_wPlus_wMinus_all (x y z t : Omega) (hxy : x ≠ y) (hzt : z ≠ t) :
    shortForm sourceLatticeComparison (wPlus x y hxy) (wMinus z t hzt) = 0 := by
  have h := (shortForm_symmetric sourceLatticeComparison (v x y hxy) (u z t hzt)).trans
    (form_u_v_all z t x y hzt hxy)
  simp [wPlus,wMinus,map_add,map_sub,form_u_v_all,h,form_u_u_all,form_v_v_all]

theorem form_wPlus_all (x y z t : Omega) (hxy : x ≠ y) (hzt : z ≠ t) :
    shortForm sourceLatticeComparison (wPlus x y hxy) (wPlus z t hzt) =
      if ({x,y} : Finset Omega) = {z,t} then 2 else 0 := by
  have h := (shortForm_symmetric sourceLatticeComparison (v x y hxy) (u z t hzt)).trans
    (form_u_v_all z t x y hzt hxy)
  simp only [wPlus,map_add,LinearMap.add_apply,form_u_v_all,h,form_u_u_all,form_v_v_all]
  split_ifs <;> norm_num

theorem form_wMinus_all (x y z t : Omega) (hxy : x ≠ y) (hzt : z ≠ t) :
    shortForm sourceLatticeComparison (wMinus x y hxy) (wMinus z t hzt) =
      if ({x,y} : Finset Omega) = {z,t} then 2 else 0 := by
  have h := (shortForm_symmetric sourceLatticeComparison (v x y hxy) (u z t hzt)).trans
    (form_u_v_all z t x y hzt hxy)
  simp only [wMinus,map_sub,LinearMap.sub_apply,form_u_v_all,h,form_u_u_all,form_v_v_all]
  split_ifs <;> norm_num

end Sporadic.Monster.Construction.LocalC.ShortFamilies
