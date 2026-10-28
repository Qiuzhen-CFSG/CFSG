module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.GenerationReduction
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneCoordinates
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Plane
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRectangleOrbits

/-!
# The marked pair centralizer and the weak-closure transporter step

Commuting with both I + E₀₄ and I + E₀₃ + E₁₄ forces a matrix to be
upper unitriangular. Under the original marking this puts C_G(z,t) inside
the literal source Sylow, with no ambient-generation assumption. Weak
closure then traps every t-centralizing transporter returning z to either
rectangle in that rectangle's full normalizer.

A rank-one tensor symmetry fixing t preserves the actual common four-space:
it is spanned by rank-one vectors whose sum with t has rank one. Therefore
C_{N_G(A₁)}(t) normalizes A₂. Combining these statements gives the actual
G₃ containment for transporters returning z to either marked rectangle.
The remaining local-orbit calculation must still place general returning
points there; this module does not assert full second-centralizer containment.

Source: Aschbacher, *Sporadic Groups* (1994), 41.2, printed pp.220–221.
The internal imports reuse the marked coordinate definitions and the
21-point tensor-action theorem, without imposing linear-branch fusion.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer
open Theory.SpecificGroups.LinearSylowNormalizers
private abbrev Mat := Matrix (Fin 5) (Fin 5) (ZMod 2)

private theorem model_pair_upper (g : SL) (hz : g ∈ centralizer)
    (ht : g.val * (1 + Matrix.single 0 3 1 + Matrix.single 1 4 1) =
      (1 + Matrix.single 0 3 1 + Matrix.single 1 4 1) * g.val) :
    g ∈ unipotent 5 (ZMod 2) := by
  have hz' := congrArg (fun a : SL => a.val) (mem_centralizer_singleton_iff.mp hz)
  change g.val * (1 + Matrix.single 0 4 1) =
    (1 + Matrix.single 0 4 1) * g.val at hz'
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at hz' ht
  have hz0 (i : Fin 5) (hi : i ≠ 0) : g i 0 = 0 := by
    have h := congrFun (congrFun hz' i) 4
    simpa [Matrix.single_mul_apply_of_ne, hi] using h
  have hz4 (j : Fin 5) (hj : j ≠ 4) : g 4 j = 0 := by
    have h := congrFun (congrFun hz' 0) j
    simpa [Matrix.mul_single_apply_of_ne, hj] using h.symm
  have h21 : g 2 1 = 0 := by
    have h := congrFun (congrFun ht 2) 4
    simpa [Matrix.mul_single_apply_of_ne, Matrix.single_mul_apply_of_ne] using h
  have h31 : g 3 1 = 0 := by
    have h := congrFun (congrFun ht 3) 4
    simpa [Matrix.mul_single_apply_of_ne, Matrix.single_mul_apply_of_ne] using h
  have h32 : g 3 2 = 0 := by
    have h := congrFun (congrFun ht 0) 2
    simpa [Matrix.mul_single_apply_of_ne, Matrix.single_mul_apply_of_ne] using h.symm
  have hu : g.val.BlockTriangular id := by
    intro i j hij
    change j < i at hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.lt_def]
  apply (mem_unipotent 5 (ZMod 2) g).mpr
  refine ⟨(mem_borel 5 (ZMod 2) g).mpr hu, fun i => ?_⟩
  have hd := g.property
  rw [Matrix.det_of_isUpperTriangular hu] at hd
  have hn : g.val i i ≠ 0 := Finset.prod_ne_zero_iff.mp
    (show (∏ j, g.val j j) ≠ 0 by rw [hd]; exact one_ne_zero) i (Finset.mem_univ i)
  exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hn

variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

/-- The simultaneous centralizer of the marked pair lies in the original Sylow. -/
theorem point_second_centralizer_le_sylow :
    Subgroup.centralizer ({z, planeSecondPoint F} : Set G) ≤ (sourceSylow F : Subgroup G) := by
  intro g hg
  have hgz : g ∈ Subgroup.centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hg z (by simp)).symm
  let gH : Subgroup.centralizer ({z} : Set G) := ⟨g,hgz⟩
  let tH : Subgroup.centralizer ({z} : Set G) :=
    ⟨planeSecondPoint F,F.pullback_le _ (planeSecondPoint_mem F)⟩
  have ht : gH * tH = tH * gH :=
    Subtype.ext (mem_centralizer_iff.mp hg (planeSecondPoint F) (by simp)).symm
  have he := congrArg (fun a : Subgroup.centralizer ({z} : Set G) => (F.equiv a : SL).val) ht
  have hm : (F.equiv tH : SL).val = 1 + Matrix.single 0 3 1 + Matrix.single 1 4 1 := by
    change (F.equiv ⟨PlaneTensor.element F 34, _⟩ : SL).val = _
    rw [PlaneTensor.element_model, modelPlaneCoordinates_matrix, modelPlaneCoordinates.apply_symm_apply]
    decide
  simp only [map_mul, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hm] at he
  rw [coe_sourceSylow]
  exact (F.mem_pullback_iff _ gH).mpr (model_pair_upper (F.equiv gH) (F.equiv gH).property he)

/-- In particular this literal simultaneous centralizer is a two-group. -/
theorem point_second_centralizer_isPGroup :
    IsPGroup 2 (Subgroup.centralizer ({z, planeSecondPoint F} : Set G)) :=
  (sourceSylow F).isPGroup'.of_injective (inclusion (point_second_centralizer_le_sylow F))
    (inclusion_injective _)

private theorem pair_transporter_normalizes (A : Subgroup G)
    (hc : Subgroup.centralizer (A : Set G) = A)
    (hweak : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤
      (sourceSylow F : Subgroup G) → g ∈ normalizer (A : Set G))
    (ht : planeSecondPoint F ∈ A) (g : G)
    (hgt : g * planeSecondPoint F * g⁻¹ = planeSecondPoint F)
    (hgz : g * z * g⁻¹ ∈ A) : g ∈ normalizer (A : Set G) := by
  have hinv : g⁻¹ ∈ normalizer (A : Set G) := by
    apply hweak
    rintro _ ⟨a,ha,rfl⟩
    apply point_second_centralizer_le_sylow F
    apply mem_centralizer_iff.mpr
    intro x hx
    have haC : a ∈ Subgroup.centralizer (A : Set G) := hc.symm ▸ ha
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · subst x
      have hh := congrArg (fun b : G => g⁻¹ * b * g)
        (mem_centralizer_iff.mp haC _ hgz)
      change z * (g⁻¹ * a * (g⁻¹)⁻¹) = (g⁻¹ * a * (g⁻¹)⁻¹) * z
      rw [inv_inv]
      simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
        inv_mul_cancel, mul_inv_cancel, one_mul, mul_one] using hh
    · have hxt : x = planeSecondPoint F := Set.mem_singleton_iff.mp hx
      subst x
      have hh := congrArg (fun b : G => g⁻¹ * b * g)
        (mem_centralizer_iff.mp haC _ (hgt.symm ▸ ht))
      change planeSecondPoint F * (g⁻¹ * a * (g⁻¹)⁻¹) =
        (g⁻¹ * a * (g⁻¹)⁻¹) * planeSecondPoint F
      rw [inv_inv]
      simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
        inv_mul_cancel, mul_inv_cancel, one_mul, mul_one] using hh
  simpa only [inv_inv] using (normalizer (A : Set G)).inv_mem hinv

/-- Weak closure traps every t-centralizing transporter returning z to A₁. -/
theorem point_second_transporter_plane (hfusion : F.MathieuFusion) (g : G)
    (hgt : g * planeSecondPoint F * g⁻¹ = planeSecondPoint F)
    (hgz : g * z * g⁻¹ ∈ F.plane) : g ∈ planeNormalizer F :=
  pair_transporter_normalizes F F.plane (plane_centralizer_eq F)
    (plane_weakly_closed F hfusion) (planeSecondPoint_mem F) g hgt hgz

omit [Finite G] in
/-- The second marked involution belongs to the literal common rectangle. -/
theorem secondPoint_mem_threeSpace : planeSecondPoint F ∈ F.threeSpace :=
  (plane_element_mem_threeSpace_iff F 34).mpr (by decide)

/-- Weak closure also traps transporters returning z to the original A₂. -/
theorem point_second_transporter_threeSpace (hfusion : F.MathieuFusion) (g : G)
    (hgt : g * planeSecondPoint F * g⁻¹ = planeSecondPoint F)
    (hgz : g * z * g⁻¹ ∈ F.threeSpace) : g ∈ threeSpaceNormalizer F :=
  pair_transporter_normalizes F F.threeSpace (threeSpace_centralizer_eq F)
    (threeSpace_weakly_closed F hfusion) (secondPoint_mem_threeSpace F) g hgt hgz

private def commonCode (c : PlaneCensus.Code) : Prop := c &&& 9 = 0
private instance (c : PlaneCensus.Code) : Decidable (commonCode c) :=
  inferInstanceAs (Decidable (c &&& 9 = 0))

private theorem commonCode_pair : ∀ c : PlaneCensus.Code,
    PlaneCensus.pure c = true → PlaneCensus.pure (34 ^^^ c) = true → commonCode c := by decide

private theorem commonCode_xor : ∀ c d : PlaneCensus.Code,
    commonCode c → commonCode d → commonCode (c ^^^ d) := by decide

private def commonBasis (i : Fin 4) : PlaneCensus.Code := ![2,6,18,32] i
private theorem commonCode_preserved (f : Equiv.Perm PlaneCensus.Code)
    (hf : ∀ c d, f (c ^^^ d) = f c ^^^ f d)
    (hp : ∀ c, PlaneCensus.pure (f c) = PlaneCensus.pure c)
    (ht : f 34 = 34) (c : PlaneCensus.Code) (hc : commonCode c) : commonCode (f c) := by
  have hzero : f 0 = 0 := by
    simpa using hf 0 0
  have hb (i : Fin 4) : commonCode (f (commonBasis i)) := by
    apply commonCode_pair
    · rw [hp]
      fin_cases i <;> decide
    · rw [← ht, ← hf, hp]
      fin_cases i <;> decide
  have h0 : commonCode (0 : PlaneCensus.Code) := by decide
  have hdecomp : ∃ a b d e : Bool,
      c = (if a then commonBasis 0 else 0) ^^^
        (if b then commonBasis 1 else 0) ^^^
        (if d then commonBasis 2 else 0) ^^^ (if e then commonBasis 3 else 0) :=
    (by decide : ∀ c : PlaneCensus.Code, commonCode c → ∃ a b d e : Bool,
      c = (if a then commonBasis 0 else 0) ^^^
        (if b then commonBasis 1 else 0) ^^^
        (if d then commonBasis 2 else 0) ^^^ (if e then commonBasis 3 else 0)) c hc
  obtain ⟨a,b,d,e,rfl⟩ := hdecomp
  have hterm (i : Fin 4) (b : Bool) : commonCode (f (if b then commonBasis i else 0)) := by
    cases b
    · simpa only [Bool.false_eq_true, ↓reduceIte, hzero] using h0
    · exact hb i
  simp only [hf]
  exact commonCode_xor _ _ (commonCode_xor _ _
    (commonCode_xor _ _ (hterm 0 a) (hterm 1 b)) (hterm 2 d)) (hterm 3 e)

/-- Fixing the rank-two rectangle element preserves its actual four-dimensional
common block, and hence the full second rectangle by weak closure. -/
theorem plane_second_centralizer_le_threeSpace (D : LocalData F) :
    planeNormalizer F ⊓ Subgroup.centralizer ({planeSecondPoint F} : Set G) ≤
      threeSpaceNormalizer F := by
  rintro g ⟨hg,hgt⟩
  let n : planeNormalizer F := ⟨g,hg⟩
  let f := PlaneTensor.normalizerAction F n
  have hf := (PlaneCensus.mem_rankOneGroup f).mp
    (SourceNormalizer.normalizer_rankOne F D.orientation.1 n)
  have ht : f 34 = 34 := by
    apply PlaneTensor.element_injective F
    rw [PlaneTensor.normalizerAction_element]
    change g * planeSecondPoint F * g⁻¹ = planeSecondPoint F
    rw [mem_centralizer_singleton_iff.mp hgt, mul_inv_cancel_right]
  have hE : g ∈ normalizer ((F.plane ⊓ F.threeSpace : Subgroup G) : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨a,ha,rfl⟩
      obtain ⟨c,hc⟩ := (PlaneTensor.sourceEquiv F).surjective ⟨a,ha.1⟩
      have he : PlaneTensor.element F c = a := congrArg Subtype.val hc
      have hcommon : commonCode c := by
        have hh := (plane_element_mem_threeSpace_iff F c).mp (he.symm ▸ ha.2)
        exact (by decide : ∀ c : PlaneCensus.Code,
          (∀ i : Fin 2, PlaneTensor.decode c i 0 = 0) → commonCode c) c hh
      have hcommon' := commonCode_preserved f hf.1 hf.2 ht c hcommon
      have hthree : PlaneTensor.element F (f c) ∈ F.threeSpace := by
        apply (plane_element_mem_threeSpace_iff F _).mpr
        exact (by decide : ∀ c : PlaneCensus.Code,
          commonCode c → ∀ i : Fin 2, PlaneTensor.decode c i 0 = 0) _ hcommon'
      refine ⟨(mem_normalizer_iff.mp hg a).mp ha.1, ?_⟩
      change g * a * g⁻¹ ∈ F.threeSpace
      simpa only [f, PlaneTensor.normalizerAction_element, he] using hthree
    · rw [card_map_of_injective (MulAut.conj g).injective]
  rw [planes_intersection_normalizer F (Or.inl D.orientation)] at hE
  exact hE.2

/-- The returning transporter lies in G₃ whenever its endpoint lies in either
of the original rectangles. This is the weak-closure step in source 41.2. -/
theorem point_second_transporter_rectangles (D : LocalData F) (g : G)
    (hgt : g * planeSecondPoint F * g⁻¹ = planeSecondPoint F)
    (hgz : g * z * g⁻¹ ∈ F.plane ∨ g * z * g⁻¹ ∈ F.threeSpace) :
    g ∈ threeSpaceNormalizer F := by
  rcases hgz with hp | hp
  · exact plane_second_centralizer_le_threeSpace F D
      ⟨point_second_transporter_plane F (Or.inl D.orientation) g hgt hp,
        mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hgt)⟩
  · exact point_second_transporter_threeSpace F (Or.inl D.orientation) g hgt hp

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
