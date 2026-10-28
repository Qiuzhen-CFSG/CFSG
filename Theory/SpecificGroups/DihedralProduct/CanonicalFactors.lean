module
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Data.Finset.NoncommProd

/-!
# Canonical central enlargements of dihedral direct factors

In a finite direct power of the dihedral group of order eight, every
automorphism permutes the products of one coordinate factor with the full
center. The proof uses only the eight-element factor: the centralizer of a
noncommuting pair is its center. A nontrivial coordinate of each factor's
central involution selects a distinct output coordinate; finiteness makes
these selections a permutation.

Source application: Aschbacher--Smith, quasithin 10.2.1, printed p.743,
where A.1.15 is applied to the four central enlargements.
-/

public noncomputable section
open Subgroup
namespace DihedralProductCanonical

abbrev D := DihedralGroup 4

/-- One coordinate dihedral group enlarged by the center of the whole power. -/
@[expose] def gamma {ι : Type*} (i : ι) : Subgroup (ι → D) where
  carrier := {x | ∀ j, j ≠ i → x j ∈ center D}
  one_mem' := by
    change ∀ j, j ≠ i → (1 : D) ∈ center D
    intro j hj
    exact (center D).one_mem
  mul_mem' := by intro x y hx hy j hji; exact (center D).mul_mem (hx j hji) (hy j hji)
  inv_mem' := by intro x hx j hji; exact (center D).inv_mem (hx j hji)

@[simp] theorem mem_gamma {ι : Type*} {i : ι} {x : ι → D} :
    x ∈ gamma i ↔ ∀ j, j ≠ i → x j ∈ center D := Iff.rfl

private theorem halfturn_ne_one : (DihedralGroup.r 2 : D) ≠ 1 := by decide +kernel

private theorem generator_commutator :
    (DihedralGroup.r 1 : D) * DihedralGroup.sr 0 *
      (DihedralGroup.r 1)⁻¹ * (DihedralGroup.sr 0)⁻¹ = DihedralGroup.r 2 := by
  decide +kernel

private theorem centralizer_noncommuting : ∀ a b c : D,
    a * b * a⁻¹ * b⁻¹ ≠ 1 → c * a = a * c → c * b = b * c →
      c ∈ center D := by decide +kernel

private theorem commutator_cases : ∀ a b : D,
    a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = DihedralGroup.r 2 := by
  decide +kernel

private theorem center_cases : ∀ a : D, a ∈ center D → a = 1 ∨ a = DihedralGroup.r 2 := by
  decide +kernel

private theorem halfturn_mem_center : (DihedralGroup.r 2 : D) ∈ center D := by
  decide +kernel

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- The full center lies in every central enlargement. -/
theorem center_le_gamma (i : ι) : center (ι → D) ≤ gamma i := by
  intro x hx j hj
  rw [Subgroup.center_pi] at hx
  exact hx j (Set.mem_univ j)

/-- The marked coordinate factor lies in its central enlargement. -/
theorem single_mem_gamma (i : ι) (a : D) :
    (Pi.mulSingle i a : ι → D) ∈ gamma i := by
  intro j hji
  simp [hji]

/-- Every element of an enlargement is a marked factor element times a
central element. -/
theorem exists_single_mul_center (i : ι) {x : ι → D} (hx : x ∈ gamma i) :
    ∃ z ∈ center (ι → D), x = Pi.mulSingle i (x i) * z := by
  let z : ι → D := (Pi.mulSingle i (x i))⁻¹ * x
  refine ⟨z, ?_, by simp [z]⟩
  rw [Subgroup.center_pi]
  change ∀ j ∈ Set.univ, z j ∈ center D
  intro j hj
  by_cases hji : j = i
  · subst j; simp [z]
  · simpa [z, Pi.mulSingle_apply, hji, Ne.symm hji] using hx j hji

/-- The coordinate description agrees with the literal factor-center join. -/
theorem gamma_eq_range_sup_center (i : ι) :
    gamma i = (MonoidHom.mulSingle (fun _ : ι => D) i).range ⊔ center (ι → D) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨z, hz, hdecomp⟩ := exists_single_mul_center i hx
    rw [hdecomp]
    exact mul_mem_sup ⟨x i, rfl⟩ hz
  · apply sup_le
    · rintro x ⟨a, rfl⟩
      exact single_mem_gamma i a
    · exact center_le_gamma i

/-- The homomorphism from a specified input factor to a specified output factor. -/
def coordinateHom (f : MulAut (ι → D)) (i j : ι) : D →* D where
  toFun a := f (Pi.mulSingle i a) j
  map_one' := by simp
  map_mul' a b := by simp [Pi.mulSingle_mul]

private theorem coordinate_halfturn (f : MulAut (ι → D)) (i j : ι) :
    coordinateHom f i j (DihedralGroup.r 2) =
      coordinateHom f i j (DihedralGroup.r 1) *
        coordinateHom f i j (DihedralGroup.sr 0) *
        (coordinateHom f i j (DihedralGroup.r 1))⁻¹ *
        (coordinateHom f i j (DihedralGroup.sr 0))⁻¹ := by
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, generator_commutator]

private theorem single_commute {i k : ι} (hik : i ≠ k) (a b : D) :
    Commute (Pi.mulSingle i a : ι → D) (Pi.mulSingle k b) := by
  change (Pi.mulSingle i a : ι → D) * Pi.mulSingle k b =
    Pi.mulSingle k b * Pi.mulSingle i a
  ext j
  by_cases hji : j = i
  · subst j; simp [hik]
  · by_cases hjk : j = k
    · subst j; simp [Ne.symm hik]
    · simp [hji, hjk]

/-- A noncentral output from one factor forces every other factor's output
at that coordinate to be central. -/
theorem other_coordinate_central (f : MulAut (ι → D)) {i j k : ι}
    (hi : coordinateHom f i j (DihedralGroup.r 2) ≠ 1) (hki : k ≠ i) (a : D) :
    coordinateHom f k j a ∈ center D := by
  apply centralizer_noncommuting
    (coordinateHom f i j (DihedralGroup.r 1))
    (coordinateHom f i j (DihedralGroup.sr 0))
  · rwa [← coordinate_halfturn]
  · exact congrFun ((single_commute hki a (DihedralGroup.r 1)).map f).eq j
  · exact congrFun ((single_commute hki a (DihedralGroup.sr 0)).map f).eq j

private theorem exists_nontrivial_coordinate (f : MulAut (ι → D)) (i : ι) :
    ∃ j, coordinateHom f i j (DihedralGroup.r 2) ≠ 1 := by
  by_contra! h
  have he : f (Pi.mulSingle i (DihedralGroup.r 2)) = 1 := funext h
  have hs : Pi.mulSingle i (DihedralGroup.r 2 : D) = 1 :=
    f.injective (he.trans (map_one f).symm)
  have hh := congrFun hs i
  exact halfturn_ne_one (by simpa using hh)

private theorem distinct_nontrivial_coordinates (f : MulAut (ι → D))
    {i k j : ι} (hi : coordinateHom f i j (DihedralGroup.r 2) ≠ 1)
    (hk : coordinateHom f k j (DihedralGroup.r 2) ≠ 1) : i = k := by
  by_contra hik
  have hc := other_coordinate_central f hi (Ne.symm hik) (DihedralGroup.r 1)
  have hcomm := mem_center_iff.mp hc (coordinateHom f k j (DihedralGroup.sr 0))
  apply hk
  rw [coordinate_halfturn, ← hcomm]
  simp [mul_assoc]

/-- The central enlargements are pairwise incomparable. -/
theorem gamma_le_iff {i j : ι} : gamma i ≤ gamma j ↔ i = j := by
  constructor
  · intro h
    by_contra hij
    have hx : (Pi.mulSingle i (DihedralGroup.r 1 : D) : ι → D) ∈ gamma i := by
      intro k hki
      simp [hki]
    have hc := (h hx) i hij
    have hn : (DihedralGroup.r 1 : D) ∉ center D := by decide +kernel
    exact hn (by simpa using hc)
  · rintro rfl; exact le_rfl

theorem gamma_injective : Function.Injective (gamma (ι := ι)) := by
  intro i j h
  exact gamma_le_iff.mp h.le

private def selectedCoordinate (f : MulAut (ι → D)) (i : ι) : ι :=
  Classical.choose (exists_nontrivial_coordinate f i)

private theorem selectedCoordinate_nontrivial (f : MulAut (ι → D)) (i : ι) :
    coordinateHom f i (selectedCoordinate f i) (DihedralGroup.r 2) ≠ 1 :=
  Classical.choose_spec (exists_nontrivial_coordinate f i)

private theorem selectedCoordinate_injective (f : MulAut (ι → D)) :
    Function.Injective (selectedCoordinate f) := by
  intro i k hik
  exact distinct_nontrivial_coordinates f
    (selectedCoordinate_nontrivial f i)
    (hik.symm ▸ selectedCoordinate_nontrivial f k)

variable [Finite ι]

/-- The permutation of central enlargements selected by an automorphism. -/
def factorPermutation (f : MulAut (ι → D)) : Equiv.Perm ι :=
  Equiv.ofBijective (selectedCoordinate f)
    ⟨selectedCoordinate_injective f,
      Finite.surjective_of_injective (selectedCoordinate_injective f)⟩

private theorem permutation_nontrivial (f : MulAut (ι → D)) (i : ι) :
    coordinateHom f i (factorPermutation f i) (DihedralGroup.r 2) ≠ 1 :=
  selectedCoordinate_nontrivial f i

private theorem off_permutation_central (f : MulAut (ι → D)) (i j : ι)
    (hji : j ≠ factorPermutation f i) (a : D) :
    coordinateHom f i j a ∈ center D := by
  obtain ⟨k, rfl⟩ := (factorPermutation f).surjective j
  exact other_coordinate_central f (permutation_nontrivial f k)
    (fun h => hji (congrArg (factorPermutation f) h.symm)) a

/-- Automorphisms map every central enlargement into its selected enlargement. -/
theorem apply_mem_gamma (f : MulAut (ι → D)) (i : ι) {x : ι → D}
    (hx : x ∈ gamma i) : f x ∈ gamma (factorPermutation f i) := by
  obtain ⟨z, hz, hdecomp⟩ := exists_single_mul_center i hx
  have hfz : f z ∈ center (ι → D) := ((centerCongr f) ⟨z, hz⟩).property
  intro j hji
  rw [hdecomp, map_mul]
  apply (center D).mul_mem (off_permutation_central f i j hji (x i))
  rw [Subgroup.center_pi] at hfz
  exact hfz j (Set.mem_univ j)

private theorem inverse_permutation_apply (f : MulAut (ι → D)) (i : ι) :
    factorPermutation f.symm (factorPermutation f i) = i := by
  symm
  apply gamma_le_iff.mp
  intro x hx
  simpa using apply_mem_gamma f.symm (factorPermutation f i) (apply_mem_gamma f i hx)

/-- The literal subgroup map under an automorphism is the selected enlargement. -/
theorem map_gamma (f : MulAut (ι → D)) (i : ι) :
    (gamma i).map f.toMonoidHom = gamma (factorPermutation f i) := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact apply_mem_gamma f i hx
  · intro y hy
    refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
    have hh := apply_mem_gamma f.symm (factorPermutation f i) hy
    rwa [inverse_permutation_apply] at hh

/-- Every automorphism acts by permutation on the canonical central enlargements. -/
def factorAction : MulAut (ι → D) →* Equiv.Perm ι where
  toFun := factorPermutation
  map_one' := by
    ext i
    apply gamma_injective
    rw [← map_gamma]
    exact map_id _
  map_mul' f g := by
    ext i
    apply gamma_injective
    change gamma (factorPermutation (f * g) i) =
      gamma (factorPermutation f (factorPermutation g i))
    rw [← map_gamma, ← map_gamma, ← map_gamma, map_map]
    rfl

/-- Literal subgroup transport for the homomorphism to the symmetric group. -/
theorem map_gamma_factorAction (f : MulAut (ι → D)) (i : ι) :
    (gamma i).map f.toMonoidHom = gamma (factorAction f i) := map_gamma f i

/-- The same permutation acts literally on the coordinate central involutions. -/
theorem apply_single_halfturn (f : MulAut (ι → D)) (i : ι) :
    f (Pi.mulSingle i (DihedralGroup.r 2)) =
      Pi.mulSingle (factorAction f i) (DihedralGroup.r 2) := by
  ext j
  change coordinateHom f i j (DihedralGroup.r 2) = _
  by_cases hji : j = factorAction f i
  · subst j
    rw [Pi.mulSingle_eq_same]
    rcases commutator_cases
        (coordinateHom f i (factorAction f i) (DihedralGroup.r 1))
        (coordinateHom f i (factorAction f i) (DihedralGroup.sr 0)) with h | h
    · exact False.elim ((permutation_nontrivial f i) ((coordinate_halfturn f i _).trans h))
    · exact (coordinate_halfturn f i _).trans h
  · rw [Pi.mulSingle_eq_of_ne hji]
    have hc := off_permutation_central f i j hji (DihedralGroup.r 1)
    have hh := mem_center_iff.mp hc (coordinateHom f i j (DihedralGroup.sr 0))
    rw [coordinate_halfturn, ← hh]
    simp [mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of the factor action fixes the full center pointwise. -/
theorem apply_center_of_factorAction_eq_one (f : MulAut (ι → D))
    (hf : factorAction f = 1) {z : ι → D} (hz : z ∈ center (ι → D)) : f z = z := by
  have hsingle (i : ι) : f (Pi.mulSingle i (z i)) = Pi.mulSingle i (z i) := by
    have hzi : z i ∈ center D := by
      rw [Subgroup.center_pi] at hz
      exact hz i (Set.mem_univ i)
    rcases center_cases (z i) hzi with h | h
    · simp [h]
    · rw [h, apply_single_halfturn, hf]
      rfl
  let := Fintype.ofFinite ι
  rw [← Finset.noncommProd_mulSingle z, Finset.map_noncommProd]
  congr 1 with i
  exact congrFun (hsingle i) _

/-- Pointwise fixation of the center is precisely the kernel of the factor action. -/
theorem factorAction_eq_one_iff (f : MulAut (ι → D)) :
    factorAction f = 1 ↔ ∀ z ∈ center (ι → D), f z = z := by
  constructor
  · intro hf z hz
    exact apply_center_of_factorAction_eq_one f hf hz
  · intro hf
    ext i
    have hz : (Pi.mulSingle i (DihedralGroup.r 2 : D) : ι → D) ∈ center (ι → D) := by
      rw [Subgroup.center_pi]
      change ∀ j ∈ Set.univ, (Pi.mulSingle i (DihedralGroup.r 2 : D) : ι → D) j ∈ center D
      intro j hj
      by_cases hji : j = i
      · subst j; simpa using halfturn_mem_center
      · simp [hji]
    have hh := (apply_single_halfturn f i).symm.trans (hf _ hz)
    change factorAction f i = i
    by_contra hi
    have he := congrFun hh (factorAction f i)
    exact halfturn_ne_one (by simpa [hi] using he)

end DihedralProductCanonical
