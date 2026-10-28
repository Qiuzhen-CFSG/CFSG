module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGeneration
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical.Levi

/-!
# Maximality of the unitary four-space plane and flag stabilizers

The isotropic coordinate-plane stabilizer Q is maximal in SU₄, and the whole
flag stabilizer B = P ∩ Q is maximal inside Q. These results hold over every
finite field of characteristic two with an involution. In particular, they
apply to the quadratic field of order (2ⁿ)² for every n ≥ 1, including n = 1.

For the local statement we use the literal restriction to the coordinate
plane. Its marked projective point has stabilizer B. The existing SL₂ Levi
section supplies upper shears, and elimination gives the two projective-line
cells represented by the identity and the coordinate pair swap.

For ambient maximality, an arbitrary element outside Q has a nonzero entry in
its lower-left block. Pair swaps, the published point radical and a diagonal
Levi element normalize one of its columns to the last basis vector. Unitarity
then conjugates the outer positive root to its negative root. Their product
supplies the missing coordinate reflection. Middle rank-one elimination and
the published parabolic generation theorem finish the argument.

Source: Aschbacher--Smith, Definitions F.1.4–7 and the U₄(q) flag amalgam in
F.1.12(I)(6), printed pp.260–264 of `refs/quasithin.pdf`. This supplies the two
plane-side maximality assertions for that concrete amalgam, independently of
point-parabolic maximality. It does not assert the classification of weak
BN-pairs or the degree-two extension statement.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourGeneration
open UnitaryFourPlaneLocal UnitaryFourPlaneRadical
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneGeometry
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "J" => form F σ hσ
local notation "P" => pointParabolicSU F J
local notation "Q" => planeParabolicSU F J
local notation "B" => borelSU F J

/-- The upper elementary matrix in the literal SL₂ Levi section. -/
def planeShear (t : F) : SU F J :=
  leviSU F σ hσ ⟨!![1,t;0,1], by simp [Matrix.det_fin_two]⟩

omit [Finite F] in
theorem planeShear_val (t : F) :
    (planeShear F σ hσ t).val.val =
      !![1,t,0,0; 0,1,0,0; 0,0,1,σ t; 0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeShear, leviSU, leviMatrix]

theorem planeShear_mem_borel (t : F) : planeShear F σ hσ t ∈ B := by
  constructor
  · change _ ∈ P
    rw [mem_pointParabolicSU, planeShear_val]
    simp
  · change _ ∈ Q
    rw [mem_planeParabolicSU, planeShear_val]
    simp

omit [CharP F 2] in
/-- In the actual restriction action, the full flag fixes the first projective point. -/
theorem mem_borel_iff_restriction (g : Q) :
    g.val ∈ B ↔ (restriction F J g).val 1 0 = 0 := by
  obtain ⟨h20,h30,h21,h31⟩ := (mem_planeParabolicSU F J g.val).mp g.property
  change (g.val ∈ P ∧ g.val ∈ Q) ↔ _
  rw [mem_pointParabolicSU]
  simp [g.property, h20, h30, restriction_val, restrictionMatrix]

/-- Elimination in the second projective-line cell uses the full flag stabilizer. -/
theorem plane_cell (g : Q) (hg : g.val ∉ B) :
    pairSwap F σ hσ * planeShear F σ hσ (g.val.val.val 0 0 / g.val.val.val 1 0) *
      g.val ∈ B := by
  obtain ⟨h20,h30,h21,h31⟩ := (mem_planeParabolicSU F J g.val).mp g.property
  have h10 : g.val.val.val 1 0 ≠ 0 := by
    simpa [mem_borel_iff_restriction, restriction_val, restrictionMatrix] using hg
  constructor
  · change _ ∈ P
    rw [mem_pointParabolicSU]
    change (((pairSwap F σ hσ).val.val * (planeShear F σ hσ _).val.val) *
      g.val.val.val) 1 0 = 0 ∧ _
    rw [planeShear_val]
    simp [planeShear, leviSU, leviMatrix, pairSwap, involutionElement, pairSwapMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, h20, h30, div_mul_cancel₀ _ h10, CharTwo.add_self_eq_zero]
  · exact (Q).mul_mem ((Q).mul_mem (pairSwap_mem_plane F σ hσ)
      (planeShear_mem_borel F σ hσ _).2) g.property

private theorem isCoatom_of_two_cells {G : Type*} [Group G] (S : Subgroup G)
    (a : G) (ha : a ∉ S)
    (hcell : ∀ g : G, g ∉ S → ∃ u : G, u ∈ S ∧ a * u * g ∈ S) :
    IsCoatom S := by
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨fun h => ha (h ▸ Subgroup.mem_top _), ?_⟩
  intro K hK hSK
  by_contra hn
  obtain ⟨g,hg,hgS⟩ := Set.not_subset.mp hn
  obtain ⟨u,hu,hc⟩ := hcell g hgS
  have haK : a ∈ K := (K.mul_mem_cancel_right (hSK hu)).mp
    ((K.mul_mem_cancel_right hg).mp (hSK hc))
  apply hK
  apply top_unique
  intro x _
  by_cases hx : x ∈ S
  · exact hSK hx
  obtain ⟨v,hv,hcv⟩ := hcell x hx
  exact (K.mul_mem_cancel_left (K.mul_mem haK (hSK hv))).mp (hSK hcv)

/-- The full flag stabilizer is maximal inside the actual plane parabolic. -/
theorem borel_isCoatom_in_plane : IsCoatom ((B).subgroupOf Q) := by
  let a : Q := ⟨pairSwap F σ hσ, pairSwap_mem_plane F σ hσ⟩
  apply isCoatom_of_two_cells ((B).subgroupOf Q) a
  · exact fun ha => pairSwap_not_mem_point F σ hσ ha.1
  · intro g hg
    let t := g.val.val.val 0 0 / g.val.val.val 1 0
    let u : Q := ⟨planeShear F σ hσ t, (planeShear_mem_borel F σ hσ t).2⟩
    exact ⟨u, planeShear_mem_borel F σ hσ t, plane_cell F σ hσ g hg⟩


/-- The middle positive root is the diagonal Hermitian unipotent. -/
def middleRoot (t : F) (ht : σ t = t) : SU F J :=
  unipotentSU F σ hσ ⟨!![0,0;0,t], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Representation.OrthogonalFourMinus.adjoint, ht]⟩

omit [Finite F] in
theorem middleRoot_val (t : F) (ht : σ t = t) :
    (middleRoot F σ hσ t ht).val.val =
      !![1,0,0,0; 0,1,t,0; 0,0,1,0; 0,0,0,1] := rfl

theorem middleRoot_mem_plane (t : F) (ht : σ t = t) :
    middleRoot F σ hσ t ht ∈ Q :=
  local_le_planeParabolic F J (unipotentSU_mem_local F σ hσ _)

omit [Finite F] [CharP F 2] in
theorem column_pairing (g : SU F J) (k l : Fin 4) :
    σ (g.val.val 0 k) * g.val.val 3 l + σ (g.val.val 1 k) * g.val.val 2 l +
      σ (g.val.val 2 k) * g.val.val 1 l + σ (g.val.val 3 k) * g.val.val 0 l =
        gram F k l := by
  have hu := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M k l) g.property.1
  change ((form F σ hσ).conjTranspose g.val.val * gram F * g.val.val) k l = _ at hu
  simp [form, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
    Fin.sum_univ_succ] at hu
  linear_combination (norm := (simp [gram]; ring)) hu

omit [CharP F 2] in
theorem point_last_row_zero (g : SU F J) (hg : g ∈ P) :
    g.val.val 3 1 = 0 ∧ g.val.val 3 2 = 0 := by
  obtain ⟨h10,h20,h30⟩ := (mem_pointParabolicSU F J g).mp hg
  have h00 : g.val.val 0 0 ≠ 0 := by
    intro h
    apply GeneralLinearGroup.det_ne_zero g.val
    apply Matrix.det_eq_zero_of_column_eq_zero 0
    intro i
    fin_cases i <;> simp_all
  have hc : σ (g.val.val 0 0) ≠ 0 := by simpa using h00
  have h1 := column_pairing F σ hσ g 0 1
  have h2 := column_pairing F σ hσ g 0 2
  simpa [h10,h20,h30,gram,hc] using And.intro h1 h2

/-- Middle rank-one elimination needs only an involution, including the binary case. -/
theorem point_le_of_plane_and_middleSwap (H : Subgroup (SU F J))
    (hQ : Q ≤ H) (hw : middleSwap F σ hσ ∈ H) : P ≤ H := by
  intro g hg
  obtain ⟨h10,h20,h30⟩ := (mem_pointParabolicSU F J g).mp hg
  obtain ⟨h31,h32⟩ := point_last_row_zero F σ hσ g hg
  by_cases h21 : g.val.val 2 1 = 0
  · exact hQ ((mem_planeParabolicSU F J g).mpr ⟨h20,h30,h21,h31⟩)
  let t := g.val.val 1 1 / g.val.val 2 1
  have ht : σ t = t := by
    have hi := column_isotropic F σ hσ g 1
    simp only [h31, map_zero, mul_zero, zero_mul, zero_add, add_zero] at hi
    dsimp [t]
    rw [map_div₀]
    apply (div_eq_div_iff (by simpa using h21) h21).mpr
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hi
  have hr : middleRoot F σ hσ t ht ∈ H := hQ (middleRoot_mem_plane F σ hσ t ht)
  have hred : middleSwap F σ hσ * middleRoot F σ hσ t ht * g ∈ Q := by
    rw [mem_planeParabolicSU]
    change (((middleSwap F σ hσ).val.val * (middleRoot F σ hσ t ht).val.val) *
      g.val.val) 2 0 = 0 ∧ _
    rw [middleRoot_val]
    simp [middleRoot, unipotentSU, unipotentMatrix, middleSwap, involutionElement, middleSwapMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, h20,h30,h10,h31,t,div_mul_cancel₀ _ h21,
      CharTwo.add_self_eq_zero]
  exact (H.mul_mem_cancel_left (H.mul_mem hw hr)).mp (hQ hred)

/-- A plane stabilizer and its missing coordinate reflection generate the ambient group. -/
theorem eq_top_of_plane_and_middleSwap (H : Subgroup (SU F J))
    (hQ : Q ≤ H) (hw : middleSwap F σ hσ ∈ H) : H = ⊤ :=
  eq_top_of_point_and_pairSwap F σ hσ H
    (point_le_of_plane_and_middleSwap F σ hσ H hQ hw)
    (hQ (pairSwap_mem_plane F σ hσ))

/-- A diagonal SL₂ Levi element normalizes the last coordinate of a vector. -/
def planeScale (d : F) (hd : d ≠ 0) : SU F J :=
  leviSU F σ hσ ⟨!![σ d,0;0,(σ d)⁻¹], by
    simp [Matrix.det_fin_two, hd]⟩

theorem planeScale_mem_plane (d : F) (hd : d ≠ 0) : planeScale F σ hσ d hd ∈ Q :=
  local_le_planeParabolic F J (leviSU_mem_local F σ hσ _)

omit [Finite F] in
theorem planeScale_mulVec (d : F) (hd : d ≠ 0) :
    (planeScale F σ hσ d hd).val.val *ᵥ ![0,0,0,d] = ![0,0,0,1] := by
  ext i
  fin_cases i <;>
    simp [planeScale, leviSU, leviMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, hσ d, hd]

/-- Plane elements send an isotropic column in the opposite point cell to e₃. -/
theorem exists_plane_clear_column (g : SU F J) (hg : g.val.val 3 0 ≠ 0) :
    ∃ u : SU F J, u ∈ Q ∧
      (u * g).val.val *ᵥ Pi.single 0 1 = ![0,0,0,1] := by
  obtain ⟨c,hc⟩ := exists_radical_clear_column F σ hσ g 0 hg
  let d := g.val.val 3 0
  let u := planeScale F σ hσ d hg * radicalElement F σ hσ c
  refine ⟨u, (Q).mul_mem (planeScale_mem_plane F σ hσ d hg)
    (radical_mem_borel F σ hσ c).2, ?_⟩
  change ((planeScale F σ hσ d hg).val.val * (radicalElement F σ hσ c).val.val *
    g.val.val) *ᵥ _ = _
  rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec_single_one]
  rw [show g.val.val.col 0 = (fun i => g.val.val i 0) from rfl, hc]
  exact planeScale_mulVec F σ hσ d hg

/-- The outer positive long-root element has parameter one. -/
def outerRoot : SU F J :=
  unipotentSU F σ hσ ⟨!![1,0;0,0], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Representation.OrthogonalFourMinus.adjoint]⟩

omit [Finite F] in
theorem outerRoot_val : (outerRoot F σ hσ).val.val =
    !![1,0,0,1; 0,1,0,0; 0,0,1,0; 0,0,0,1] := rfl

theorem outerRoot_mem_plane : outerRoot F σ hσ ∈ Q :=
  local_le_planeParabolic F J (unipotentSU_mem_local F σ hσ _)

/-- The reflection exchanging the first and last coordinates. -/
def outerSwap : SU F J :=
  involutionElement F σ hσ !![0,0,0,1; 0,1,0,0; 0,0,1,0; 1,0,0,0]
    (by ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ])
    (by ext i j; fin_cases i <;> fin_cases j <;>
      simp [form, gram, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ])

theorem outerSwap_val : (outerSwap F σ hσ).val.val =
    !![0,0,0,1; 0,1,0,0; 0,0,1,0; 1,0,0,0] := rfl

theorem outerRoot_reflection : outerRoot F σ hσ *
    (outerSwap F σ hσ * outerRoot F σ hσ * outerSwap F σ hσ) *
      outerRoot F σ hσ = outerSwap F σ hσ := by
  apply Subtype.ext
  apply Units.ext
  change (outerRoot F σ hσ).val.val *
    ((outerSwap F σ hσ).val.val * (outerRoot F σ hσ).val.val *
      (outerSwap F σ hσ).val.val) * (outerRoot F σ hσ).val.val = _
  rw [outerRoot_val, outerSwap_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

theorem pairSwap_outerSwap : pairSwap F σ hσ * outerSwap F σ hσ *
    pairSwap F σ hσ = middleSwap F σ hσ := by
  apply Subtype.ext
  apply Units.ext
  change (pairSwap F σ hσ).val.val * (outerSwap F σ hσ).val.val *
    (pairSwap F σ hσ).val.val = (middleSwap F σ hσ).val.val
  rw [outerSwap_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairSwap, middleSwap, involutionElement, pairSwapMatrix,
      middleSwapMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- A unitary element carrying e₀ to e₃ interchanges the two outer root groups. -/
theorem outerRoot_conjugate (g : SU F J)
    (hg : g.val.val *ᵥ Pi.single 0 1 = ![0,0,0,1]) :
    g * outerRoot F σ hσ * g⁻¹ =
      outerSwap F σ hσ * outerRoot F σ hσ * outerSwap F σ hσ := by
  have h00 : g.val.val 0 0 = 0 := by simpa using congrFun hg 0
  have h10 : g.val.val 1 0 = 0 := by simpa using congrFun hg 1
  have h20 : g.val.val 2 0 = 0 := by simpa using congrFun hg 2
  have h30 : g.val.val 3 0 = 1 := by simpa using congrFun hg 3
  have hr (j : Fin 4) : g.val.val 0 j = gram F 0 j := by
    simpa [h00,h10,h20,h30] using column_pairing F σ hσ g 0 j
  have he : g * outerRoot F σ hσ =
      (outerSwap F σ hσ * outerRoot F σ hσ * outerSwap F σ hσ) * g := by
    apply Subtype.ext
    apply Units.ext
    change g.val.val * (outerRoot F σ hσ).val.val =
      ((outerSwap F σ hσ).val.val * (outerRoot F σ hσ).val.val *
        (outerSwap F σ hσ).val.val) * g.val.val
    rw [outerRoot_val, outerSwap_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, h00,h10,h20,h30,hr,gram]
  rw [he, mul_assoc, mul_inv_cancel, mul_one]

/-- One opposite isotropic column forces the missing reflection in any overgroup. -/
theorem middleSwap_mem_of_bottomLeft (H : Subgroup (SU F J))
    (hQ : Q ≤ H) (g : SU F J) (hg : g ∈ H) (h30 : g.val.val 3 0 ≠ 0) :
    middleSwap F σ hσ ∈ H := by
  obtain ⟨u,hu,hc⟩ := exists_plane_clear_column F σ hσ g h30
  have hug : u * g ∈ H := H.mul_mem (hQ hu) hg
  have ht : outerRoot F σ hσ ∈ H := hQ (outerRoot_mem_plane F σ hσ)
  have hl : outerSwap F σ hσ * outerRoot F σ hσ * outerSwap F σ hσ ∈ H := by
    rw [← outerRoot_conjugate F σ hσ (u * g) hc]
    exact H.mul_mem (H.mul_mem hug ht) (H.inv_mem hug)
  have hw : outerSwap F σ hσ ∈ H := by
    rw [← outerRoot_reflection F σ hσ]
    exact H.mul_mem (H.mul_mem ht hl) ht
  rw [← pairSwap_outerSwap F σ hσ]
  exact H.mul_mem (H.mul_mem (hQ (pairSwap_mem_plane F σ hσ)) hw)
    (hQ (pairSwap_mem_plane F σ hσ))

/-- An arbitrary element outside the plane stabilizer generates with it all of SU₄. -/
theorem eq_top_of_plane_and_outside (H : Subgroup (SU F J))
    (hQ : Q ≤ H) (g : SU F J) (hg : g ∈ H) (hgQ : g ∉ Q) : H = ⊤ := by
  apply eq_top_of_plane_and_middleSwap F σ hσ H hQ
  have ha : pairSwap F σ hσ ∈ H := hQ (pairSwap_mem_plane F σ hσ)
  by_cases h30 : g.val.val 3 0 ≠ 0
  · exact middleSwap_mem_of_bottomLeft F σ hσ H hQ g hg h30
  by_cases h20 : g.val.val 2 0 ≠ 0
  · apply middleSwap_mem_of_bottomLeft F σ hσ H hQ (pairSwap F σ hσ * g)
      (H.mul_mem ha hg)
    simpa [pairSwap, involutionElement, pairSwapMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ] using h20
  by_cases h31 : g.val.val 3 1 ≠ 0
  · apply middleSwap_mem_of_bottomLeft F σ hσ H hQ (g * pairSwap F σ hσ)
      (H.mul_mem hg ha)
    simpa [pairSwap, involutionElement, pairSwapMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ] using h31
  have h21 : g.val.val 2 1 ≠ 0 := by
    intro he
    exact hgQ ((mem_planeParabolicSU F J g).mpr
      ⟨not_ne_iff.mp h20, not_ne_iff.mp h30, he, not_ne_iff.mp h31⟩)
  apply middleSwap_mem_of_bottomLeft F σ hσ H hQ
    (pairSwap F σ hσ * g * pairSwap F σ hσ) (H.mul_mem (H.mul_mem ha hg) ha)
  simpa [pairSwap, involutionElement, pairSwapMatrix, Matrix.mul_apply,
    Matrix.vecMul, dotProduct, Fin.sum_univ_succ] using h21

/-- The isotropic coordinate-plane stabilizer is a maximal proper subgroup of SU₄. -/
theorem plane_isCoatom : IsCoatom Q := by
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨plane_ne_top F σ hσ, ?_⟩
  intro H hH hQ g hg
  by_contra hgQ
  exact hH (eq_top_of_plane_and_outside F σ hσ H hQ g hg hgQ)

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneGeometry
