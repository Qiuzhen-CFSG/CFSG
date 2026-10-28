module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneImage
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceIntersections
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.LineAction
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceTensorProduct

/-!
# The three-point line action in the linear source geometry

The second tensor factor of the proved rectangle quotient induces the full
symmetric group on its three row directions. Its point stabilizer is exactly
the intersection with the original row normalizer. Thus the actual source
line residue has three points and the point stabilizer is transitive on the
other two. All cosets and left actions are literal.

This is the line-action part of Aschbacher, *Sporadic Groups* (1994),
41.1–41.4, pp.219–222. It uses the linear fusion counts directly; the shared
coset definitions and independent coordinate lemma do not use Mathieu data.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear.SourceGeometry
open PlaneTensor PlaneCensus GraphUniquenessSystem.Cosets
open UniquenessMathieu.OctadSource (Point)
open UniquenessMathieu.SourceNormalizer (plane_element_mem_row_iff)

private theorem tensor_row : ∀ (i : Fin 3) (v : Fin 3 → ZMod 2),
    tensorCode i v >>> 3 = 0 ↔ i = 0 ∨ v = 0 := by decide

private theorem row_tensor : ∀ x : Code, x >>> 3 = 0 →
    ∃ v : Fin 3 → ZMod 2, tensorCode 0 v = x := by decide

variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

/-- The first tensor direction is the original row–rectangle intersection. -/
theorem tensor_element_mem_row_iff (i : Fin 3) (v : Fin 3 → ZMod 2) :
    element F (tensorCode i v) ∈ F.row ↔ i = 0 ∨ v = 0 := by
  rw [plane_element_mem_row_iff]
  exact tensor_row i v

variable [Finite G] (hlinear : F.LinearFusion)

/-- The actual permutation action on the three row directions of A₁. -/
@[expose] def lineAction : sourcePlaneNormalizer F →* Equiv.Perm (Fin 3) :=
  (MonoidHom.snd _ _).comp
    ((linearPlaneQuotientEquiv F hlinear).toMonoidHom.comp (QuotientGroup.mk' _))

theorem lineAction_surjective : Function.Surjective (lineAction F hlinear) := by
  intro p
  obtain ⟨q, hq⟩ := (linearPlaneQuotientEquiv F hlinear).surjective (1, p)
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨n, congrArg Prod.snd hq⟩

/-- Source conjugation and the line permutation are the two factors of the
same tensor action, with the literal quotient map. -/
theorem lineAction_tensor (n : sourcePlaneNormalizer F) (i : Fin 3) (v : Fin 3 → ZMod 2) :
    element F (tensorCode (lineAction F hlinear n i)
      ((linearPlaneQuotientEquiv F hlinear (QuotientGroup.mk n)).1 v)) =
      (n : G) * element F (tensorCode i v) * (n : G)⁻¹ :=
  linearPlaneQuotientEquiv_action F hlinear n i v

/-- The point-line flag stabilizer is exactly the preimage of a point
stabilizer in the symmetric-three action. -/
theorem lineAction_fix_iff (n : sourcePlaneNormalizer F) :
    lineAction F hlinear n 0 = 0 ↔ (n : G) ∈ rowNormalizer F := by
  constructor
  · intro hn
    have hnI : (n : G) ∈ normalizer ((F.row ⊓ F.plane : Subgroup G) : Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      apply eq_of_le_of_card_ge
      · rintro _ ⟨a, ha, rfl⟩
        obtain ⟨x, hx⟩ := (sourceEquiv F).surjective ⟨a, ha.2⟩
        have hxa : element F x = a := congrArg Subtype.val hx
        obtain ⟨v, hv⟩ := row_tensor x ((plane_element_mem_row_iff F x).mp (hxa.symm ▸ ha.1))
        have hva : element F (tensorCode 0 v) = a := (congrArg (element F) hv).trans hxa
        refine ⟨?_, (mem_normalizer_iff.mp n.property a).mp ha.2⟩
        change (n : G) * a * (n : G)⁻¹ ∈ F.row
        rw [← hva, ← lineAction_tensor F hlinear n, hn]
        exact (tensor_element_mem_row_iff F 0 _).mpr (Or.inl rfl)
      · rw [card_map_of_injective (MulAut.conj (n : G)).injective]
    rw [source_row_plane_normalizer] at hnI
    exact hnI.1
  · intro hn
    let v : Fin 3 → ZMod 2 := fun _ => 1
    have hv : v ≠ 0 := by intro h; have := congrFun h 0; exact zero_ne_one this.symm
    have hm := (mem_normalizer_iff.mp hn (element F (tensorCode 0 v))).mp
      ((tensor_element_mem_row_iff F 0 v).mpr (Or.inl rfl))
    rw [← lineAction_tensor F hlinear n, tensor_element_mem_row_iff] at hm
    rcases hm with hm | hm
    · exact hm
    · exact False.elim (hv ((linearPlaneQuotientEquiv F hlinear
        (QuotientGroup.mk n)).1.map_eq_zero_iff.mp hm))

/-- Equality of point representatives on the base line is detected by the
literal symmetric-three action. -/
theorem lineAction_eq_iff (a b : sourcePlaneNormalizer F) :
    lineAction F hlinear a 0 = lineAction F hlinear b 0 ↔
      vertex (rowNormalizer F) (a : G) = vertex (rowNormalizer F) (b : G) := by
  rw [vertex_eq_iff]
  change _ ↔ ((a⁻¹ * b : sourcePlaneNormalizer F) : G) ∈ rowNormalizer F
  rw [← lineAction_fix_iff F hlinear (a⁻¹ * b), map_mul, map_inv]
  change _ ↔ (lineAction F hlinear a).symm (lineAction F hlinear b 0) = 0
  constructor
  · intro h; rw [← h, Equiv.symm_apply_apply]
  · intro h
    exact ((lineAction F hlinear a).apply_symm_apply (lineAction F hlinear b 0)).symm.trans
      (congrArg (lineAction F hlinear a) h) |>.symm

private def linePointMap :
    (sourcePlaneNormalizer F ⧸ (rowNormalizer F).subgroupOf (sourcePlaneNormalizer F)) → Fin 3 :=
  Quotient.lift (fun a : sourcePlaneNormalizer F => lineAction F hlinear a 0) (by
    intro a b hab
    apply (lineAction_eq_iff F hlinear a b).mpr
    have hh := QuotientGroup.leftRel_apply.mp hab
    exact QuotientGroup.eq.mpr hh)

private theorem linePointMap_bijective : Function.Bijective (linePointMap F hlinear) := by
  constructor
  · intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        intro h
        apply QuotientGroup.eq.mpr
        have hh := (vertex_eq_iff (rowNormalizer F) (a : G) (b : G)).mp
          ((lineAction_eq_iff F hlinear a b).mp h)
        exact hh
  · intro i
    obtain ⟨a, ha⟩ := lineAction_surjective F hlinear (Equiv.swap 0 i)
    exact ⟨QuotientGroup.mk a, by change lineAction F hlinear a 0 = i; rw [ha, Equiv.swap_apply_left]⟩

/-- Literal cosets of G₁₂ in G₂ are the three points on the source line. -/
def linePointEquiv :
    (sourcePlaneNormalizer F ⧸ (rowNormalizer F).subgroupOf (sourcePlaneNormalizer F)) ≃ Fin 3 :=
  Equiv.ofBijective (linePointMap F hlinear) (linePointMap_bijective F hlinear)

@[simp] theorem linePointEquiv_mk (a : sourcePlaneNormalizer F) :
    linePointEquiv F hlinear (QuotientGroup.mk a) = lineAction F hlinear a 0 := by rfl

/-- The points incident with the base line, as actual ambient point cosets. -/
def linePointResidueEquiv :
    Residue (sourcePlaneNormalizer F) (rowNormalizer F) ≃ Fin 3 :=
  (residueEquiv (sourcePlaneNormalizer F) (rowNormalizer F)).symm.trans (linePointEquiv F hlinear)

@[simp] theorem linePointResidueEquiv_representative (a : sourcePlaneNormalizer F) :
    linePointResidueEquiv F hlinear (residueEquiv (sourcePlaneNormalizer F) (rowNormalizer F)
      (QuotientGroup.mk a)) = lineAction F hlinear a 0 := by
  simp [linePointResidueEquiv]

include hlinear in
/-- Source 41.1: each base line has exactly three actual points. -/
theorem line_point_card : Nat.card (Residue (sourcePlaneNormalizer F) (rowNormalizer F)) = 3 := by
  rw [Nat.card_congr (linePointResidueEquiv F hlinear)]
  simp

/-- The line coordinates respect the original left action. -/
theorem linePointEquiv_smul (a : sourcePlaneNormalizer F)
    (q : sourcePlaneNormalizer F ⧸ (rowNormalizer F).subgroupOf (sourcePlaneNormalizer F)) :
    linePointEquiv F hlinear (a • q) = lineAction F hlinear a (linePointEquiv F hlinear q) := by
  induction q using QuotientGroup.induction_on with
  | H b =>
    change linePointEquiv F hlinear (QuotientGroup.mk (a * b)) = _
    rw [linePointEquiv_mk, linePointEquiv_mk, map_mul]
    rfl

include hlinear in
/-- Every line element outside its point stabilizer can be the second endpoint.
The point stabilizer acts transitively on the other two actual line points. -/
theorem line_transitive (t : G) (ht : t ∈ sourcePlaneNormalizer F)
    (htR : t ∉ rowNormalizer F) :
    LineTransitive (rowNormalizer F) t (sourcePlaneNormalizer F) := by
  intro u hu huR
  let a : sourcePlaneNormalizer F := ⟨t, ht⟩
  let b : sourcePlaneNormalizer F := ⟨u, hu⟩
  have hi : lineAction F hlinear a 0 ≠ 0 := fun h => htR ((lineAction_fix_iff F hlinear a).mp h)
  have hj : lineAction F hlinear b 0 ≠ 0 := fun h => huR ((lineAction_fix_iff F hlinear b).mp h)
  obtain ⟨p, hp⟩ := lineAction_surjective F hlinear
    (Equiv.swap (lineAction F hlinear a 0) (lineAction F hlinear b 0))
  refine ⟨p, p.property, (vertex_eq_base _ _).mpr
    ((lineAction_fix_iff F hlinear p).mp ?_), ?_⟩
  · rw [hp]
    exact Equiv.swap_apply_of_ne_of_ne hi.symm hj.symm
  · apply (lineAction_eq_iff F hlinear (p * a) b).mp
    rw [map_mul]
    change lineAction F hlinear p (lineAction F hlinear a 0) = _
    rw [hp, Equiv.swap_apply_left]

/-- An actual line element inducing a transposition on its three points. -/
def lineSwap : sourcePlaneNormalizer F :=
  Classical.choose (lineAction_surjective F hlinear (Equiv.swap 0 1))

theorem lineSwap_action : lineAction F hlinear (lineSwap F hlinear) = Equiv.swap 0 1 :=
  Classical.choose_spec (lineAction_surjective F hlinear (Equiv.swap 0 1))

/-- The chosen edge has distinct endpoints on the literal base line. -/
theorem lineSwap_not_row : (lineSwap F hlinear : G) ∉ rowNormalizer F := by
  intro h
  have he := (lineAction_fix_iff F hlinear (lineSwap F hlinear)).mpr h
  rw [lineSwap_action] at he
  simp at he

/-- Its square fixes the source point; no order-two lift is assumed. -/
theorem lineSwap_square_mem :
    (lineSwap F hlinear : G) * (lineSwap F hlinear : G) ∈ rowNormalizer F := by
  change ((lineSwap F hlinear * lineSwap F hlinear : sourcePlaneNormalizer F) : G) ∈ rowNormalizer F
  apply (lineAction_fix_iff F hlinear _).mp
  rw [map_mul, lineSwap_action]
  simp

/-- The three actual ambient point cosets on the marked source line. -/
def linePoint (i : Fin 3) : Point F := (linePointResidueEquiv F hlinear).symm i |>.val

theorem linePoint_injective : Function.Injective (linePoint F hlinear) := by
  intro i j h
  apply (linePointResidueEquiv F hlinear).symm.injective
  exact Subtype.ext h

/-- Every coordinate retains its ambient coset representative. -/
theorem linePoint_representative (a : sourcePlaneNormalizer F) :
    linePoint F hlinear (lineAction F hlinear a 0) = vertex (rowNormalizer F) (a : G) := by
  rw [← linePointResidueEquiv_representative F hlinear a]
  change ((linePointResidueEquiv F hlinear).symm
    (linePointResidueEquiv F hlinear (residueEquiv _ _ (QuotientGroup.mk a)))).val = _
  rw [Equiv.symm_apply_apply, residueEquiv_mk]

theorem linePoint_zero : linePoint F hlinear 0 = vertex (rowNormalizer F) 1 := by
  simpa using linePoint_representative F hlinear 1

theorem linePoint_one : linePoint F hlinear 1 = vertex (rowNormalizer F) (lineSwap F hlinear : G) := by
  have h := linePoint_representative F hlinear (lineSwap F hlinear)
  rw [lineSwap_action] at h
  simpa using h

/-- The full three-point action is realized on ambient source cosets. -/
theorem linePoint_smul (a : sourcePlaneNormalizer F) (i : Fin 3) :
    (a : G) • linePoint F hlinear i = linePoint F hlinear (lineAction F hlinear a i) := by
  obtain ⟨b, hb⟩ := lineAction_surjective F hlinear (Equiv.swap 0 i)
  have hi : lineAction F hlinear b 0 = i := by rw [hb, Equiv.swap_apply_left]
  rw [← hi, linePoint_representative]
  have hm := linePoint_representative F hlinear (a * b)
  rw [map_mul] at hm
  exact hm.symm

/-- Incidence with the base line is exhausted by these three literal points. -/
theorem incident_base_line_iff (x : Point F) :
    Incident (sourcePlaneNormalizer F) (rowNormalizer F) (vertex (sourcePlaneNormalizer F) 1) x ↔
      ∃ i : Fin 3, linePoint F hlinear i = x := by
  constructor
  · intro hx
    refine ⟨linePointResidueEquiv F hlinear ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((linePointResidueEquiv F hlinear).symm_apply_apply ⟨x, hx⟩)
  · rintro ⟨i, rfl⟩
    exact ((linePointResidueEquiv F hlinear).symm i).property

end Theory.GroupTheory.TransvectionFive.UniquenessLinear.SourceGeometry
