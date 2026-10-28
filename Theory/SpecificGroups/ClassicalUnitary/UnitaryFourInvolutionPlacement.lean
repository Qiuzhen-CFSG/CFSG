module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointQuotient
/-!
# Placing upper-unitary involutions in the plane radical

An involution in the standard upper unitriangular SU4 subgroup is conjugate
into the plane radical by an element of the point parabolic. If its first
upper entry vanishes, it already lies there. Otherwise its square forces the
middle upper entry to vanish, placing it in the point radical. The radical's
involution equation makes its two coordinates dependent over the fixed field;
an actual middle SL2 Levi matrix then kills the second coordinate.

All conjugators are in the literal matrix parabolic, and the target is the
actual kernel of plane restriction. The argument works over any finite field
of characteristic two with the stored involution.

Source: the involution placement used in Aschbacher--Smith F.4.27(3), F.4.30
and the unitary branch of F.4.35, printed pp.289--292.
-/

@[expose] public section
noncomputable section
open Matrix BenderSuzuki.MatrixGroups Subgroup
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourInvolutionPlacement
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
  (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "J" => form F σ hσ
local notation "R" => UnitaryFourPointLocal.radical F σ hσ
local notation "P" => pointParabolicSU F J
local notation "L" => UnitaryFourPlaneLocal.localFactor F J
local notation "V" => Subgroup.map (Subgroup.subtype (UnitaryFourPlaneLocal.localFactor F J)) (UnitaryFourPlaneRadical.radical F σ hσ)

omit [Finite F] in
theorem radical_involution_pairing (c : RadicalCoordinates F σ)
    (hc : (radicalElement F σ hσ c) ^ 2 = 1) :
    σ c.x * c.y = σ c.y * c.x := by
  have he := congrArg (fun a : SU F J => a.val.val 0 3) hc
  change ((radicalMatrix F σ c) ^ 2) 0 3 = 0 at he
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_succ, radicalMatrix] at he
  have hh : σ c.y * c.x + σ c.x * c.y = 0 := by
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) he
  exact (CharTwo.add_eq_zero.mp hh).symm

omit [Finite F] in
theorem radical_involution_levi (c : RadicalCoordinates F σ)
    (hc : (radicalElement F σ hσ c) ^ 2 = 1) :
    ∃ B : SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ),
      (coordinatesOfRadical F σ hσ
        (leviConjugate F σ hσ ((middleEquivSL F σ hσ).symm B) c)).y = 0 := by
  by_cases hx : c.x = 0
  · let B : SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ) :=
      ⟨!![0,1;1,0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩
    refine ⟨B, ?_⟩
    rw [(leviSL_conjugation_coordinates F σ hσ B c).2.1]
    simp [B, hx]
  · have ht : σ (c.y / c.x) = c.y / c.x := by
      rw [map_div₀]
      apply (div_eq_div_iff ((map_ne_zero σ).mpr hx) hx).mpr
      exact (radical_involution_pairing F σ hσ c hc).symm.trans (mul_comm _ _)
    let t : FixedBy.subfield F σ := ⟨c.y / c.x, ht⟩
    let B : SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ) :=
      ⟨!![1,0;t,1], by simp [Matrix.det_fin_two]⟩
    refine ⟨B, ?_⟩
    rw [(leviSL_conjugation_coordinates F σ hσ B c).2.1]
    simp [B, t, div_mul_cancel₀ _ hx, CharTwo.add_self_eq_zero]

theorem mem_plane_radical_of_upper_and_entry_zero
    (a : SU F J) (ha : a ∈ UnitaryFourSylow.upper F σ hσ)
    (h01 : a.val.val 0 1 = 0) : a ∈ V := by
  obtain ⟨ht,hd⟩ := (UnitaryFourSylow.mem_upper_iff_entries F σ hσ a).mp ha
  have hP : a ∈ planeParabolicSU F J := by
    rw [mem_planeParabolicSU]
    exact ⟨ht 2 0 (by decide), ht 3 0 (by decide), ht 2 1 (by decide), ht 3 1 (by decide)⟩
  have hL : a ∈ L := by
    apply (UnitaryFourPlaneLocal.mem_localFactor F J a).mpr
    refine ⟨hP, ?_⟩
    simp [UnitaryFourPlaneLocal.restrictionMatrix, Matrix.det_fin_two, hd, h01, ht 1 0 (by decide)]
  refine ⟨⟨a,hL⟩, ?_, rfl⟩
  exact (UnitaryFourPlaneRadical.mem_radical F σ hσ ⟨a,hL⟩).mpr
    ⟨hd 0, h01, ht 1 0 (by decide), hd 1⟩

theorem radical_y_zero_mem_plane (c : RadicalCoordinates F σ) (hy : c.y = 0) :
    radicalElement F σ hσ c ∈ V := by
  apply mem_plane_radical_of_upper_and_entry_zero F σ hσ _
    (UnitaryFourSylow.radicalElement_mem_upper F σ hσ c)
  change σ c.y = 0
  rw [hy, map_zero]

theorem radical_involution_point_conjugate_plane (c : RadicalCoordinates F σ)
    (hc : (radicalElement F σ hσ c) ^ 2 = 1) :
    ∃ g : P, g.val * radicalElement F σ hσ c * g.val⁻¹ ∈ V := by
  obtain ⟨B,hB⟩ := radical_involution_levi F σ hσ c hc
  let g := leviSL F σ hσ B
  let d := leviConjugate F σ hσ ((middleEquivSL F σ hσ).symm B) c
  refine ⟨⟨g.val, localSU_le_pointParabolicSU F J g.property⟩, ?_⟩
  have hd := (radicalCoordinatesEquiv F σ hσ).apply_symm_apply d
  have hm := radical_y_zero_mem_plane F σ hσ (coordinatesOfRadical F σ hσ d) hB
  have he := congrArg (fun r : R => r.val.val) hd
  change radicalElement F σ hσ (coordinatesOfRadical F σ hσ d) =
    g.val * radicalElement F σ hσ c * g.val⁻¹ at he
  rwa [← he]

theorem upper_involution_point_conjugate_plane (a : SU F J)
    (ha : a ∈ UnitaryFourSylow.upper F σ hσ) (ha2 : a ^ 2 = 1) :
    ∃ g : P, g.val * a * g.val⁻¹ ∈ V := by
  by_cases h01 : a.val.val 0 1 = 0
  · refine ⟨1, ?_⟩
    simpa using mem_plane_radical_of_upper_and_entry_zero F σ hσ a ha h01
  · obtain ⟨ht,hd⟩ := (UnitaryFourSylow.mem_upper_iff_entries F σ hσ a).mp ha
    have he := congrArg (fun b : SU F J => b.val.val 0 2) ha2
    change ((a.val.val) ^ 2) 0 2 = 0 at he
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_succ, hd, ht 3 2 (by decide)] at he
    have had : a.val.val 0 1 * a.val.val 1 2 = 0 := by
      linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) he
    have h12 : a.val.val 1 2 = 0 := (mul_eq_zero.mp had).resolve_left h01
    have hl : a ∈ localSU F J := ((UnitaryFourSylow.mem_upper F σ hσ a).mp ha).1
    have hr : (⟨a,hl⟩ : localSU F J) ∈ UnitaryFourPointLocal.radical F σ hσ :=
      (UnitaryFourPointLocal.mem_radical F σ hσ ⟨a,hl⟩).mpr
        ⟨hd 1, h12, ht 2 1 (by decide), hd 2⟩
    obtain ⟨c,hc⟩ := (radicalCoordinatesEquiv F σ hσ).surjective ⟨⟨a,hl⟩,hr⟩
    have hmat : radicalElement F σ hσ c = a := congrArg (fun r : R => r.val.val) hc
    obtain ⟨g,hg⟩ := radical_involution_point_conjugate_plane F σ hσ c (by rwa [hmat])
    exact ⟨g, by rwa [hmat] at hg⟩
end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourInvolutionPlacement
