module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local.Basic
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct

/-!
# Two transvections generating the actual seed parabolic modulo its core

The intrinsic two-cores commute with the original quotient projection, whose
kernel is a two-group. For the standard point stabilizer, the other flag core
contains a transvection t, and a Levi reflection s conjugates it to the opposite
transvection. These two elements generate the six-element Levi factor; together
with the point core they generate the whole parabolic. The checked Bruhat
normal form reduces this calculation to eight upper matrices and six permutation
matrices. The diagram automorphism and flag conjugation transport both cores
and generators together, preserving the original quotient marking.

This is the concrete group input to the binary plane argument in the first
paragraph following (4.6.12)(3), printed p.910 of Meierfrankenfeld--Stellmacher,
*Pushing up weak BN-pairs of rank two* (1993).
-/

public section

open Subgroup Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed

private theorem line_core_eq : lineParabolicSL.pCoreIn 2 = lineV := by
  rw [← pointParabolic_map_diagram, ← map_pCoreIn_of_injective 2 _ _ diagram.injective,
    MarkedProduct.pointParabolic_core, pointV_map_diagram]

private theorem point_core_le_line : pointParabolicSL.pCoreIn 2 ≤ lineParabolicSL := by
  rw [MarkedProduct.pointParabolic_core]
  intro x hx
  exact (mem_lineParabolicSL_iff x).mpr ⟨hx.2.2.1, hx.2.2.2.2.2.1⟩

private theorem line_core_le_point : lineParabolicSL.pCoreIn 2 ≤ pointParabolicSL := by
  rw [line_core_eq]
  intro x hx
  have h := point_core_le_line (show diagram x ∈ pointParabolicSL.pCoreIn 2 by
    rw [MarkedProduct.pointParabolic_core]; exact hx)
  exact (diagram_point_line x).mp h

private def t : SL := Bruhat.upper 4
private def s : SL := Bruhat.perm 1
private def u : SL := s * t * s⁻¹

private theorem point_generation (H : Subgroup SL)
    (hQ : pointParabolicSL.pCoreIn 2 ≤ H) (ht : t ∈ H) (hu : u ∈ H) :
    pointParabolicSL ≤ H := by
  have hs : s ∈ H := by
    have he : s = t * u * t := by decide +kernel
    rw [he]
    exact H.mul_mem (H.mul_mem ht hu) ht
  have hupper (i : Fin 8) : Bruhat.upper i ∈ H := by
    have he : ∀ i : Fin 8, Bruhat.upper i ∈ pointV ∨ Bruhat.upper i * t ∈ pointV := by
      decide +kernel
    rw [MarkedProduct.pointParabolic_core] at hQ
    rcases he i with hi | hi
    · exact hQ hi
    · have htt : t * t = 1 := by decide +kernel
      have hh := H.mul_mem (hQ hi) ht
      simpa only [mul_assoc, htt, mul_one] using hh
  intro x hx
  obtain ⟨i, j, k, rfl⟩ := Bruhat.decomposition x
  have hj : Bruhat.perm j ∈ pointParabolicSL := by
    have hi := (show borelSL ≤ pointParabolicSL from inf_le_left) (Bruhat.upper_mem i)
    have hk := (show borelSL ≤ pointParabolicSL from inf_le_left) (Bruhat.upper_mem k)
    exact (pointParabolicSL.mul_mem_cancel_left hi).mp
      ((pointParabolicSL.mul_mem_cancel_right hk).mp hx)
  have hj' : Bruhat.perm j = 1 ∨ Bruhat.perm j = s := by
    have he : ∀ j : Fin 6, Bruhat.perm j ∈ pointParabolicSL →
        Bruhat.perm j = 1 ∨ Bruhat.perm j = s := by decide +kernel
    exact he j hj
  apply H.mul_mem (H.mul_mem (hupper i) _) (hupper k)
  rcases hj' with hj' | hj'
  · rw [hj']; exact H.one_mem
  · rw [hj']; exact hs

private theorem standard_generation :
    ∃ t s : SL, t ∈ lineParabolicSL.pCoreIn 2 ∧ s ∈ pointParabolicSL ∧
      (∀ H : Subgroup SL, pointParabolicSL.pCoreIn 2 ≤ H → t ∈ H →
        s * t * s⁻¹ ∈ H → pointParabolicSL ≤ H) := by
  refine ⟨t, s, ?_, ?_, fun H hQ ht hu => point_generation H hQ ht hu⟩
  · rw [line_core_eq]; decide +kernel
  · decide +kernel

private theorem transport_generation (e : SL ≃* SL) :
    let P := pointParabolicSL.map e.toMonoidHom
    let Q := lineParabolicSL.map e.toMonoidHom
    Q.pCoreIn 2 ≤ P ∧
    ∃ t s : SL, t ∈ Q.pCoreIn 2 ∧ s ∈ P ∧
      (∀ H : Subgroup SL, P.pCoreIn 2 ≤ H → t ∈ H →
        s * t * s⁻¹ ∈ H → P ≤ H) := by
  dsimp only
  rw [← map_pCoreIn_of_injective 2 _ _ e.injective]
  refine ⟨map_mono line_core_le_point, ?_⟩
  obtain ⟨t, s, ht, hs, hgen⟩ := standard_generation
  refine ⟨e t, e s, mem_map_of_mem _ ht, mem_map_of_mem _ hs, ?_⟩
  intro H hQ ht hs
  have hle : pointParabolicSL ≤ H.comap e.toMonoidHom := by
    apply hgen
    · intro q hq
      apply hQ
      rw [← map_pCoreIn_of_injective 2 _ _ e.injective]
      exact mem_map_of_mem _ hq
    · exact ht
    · change e (s * t * s⁻¹) ∈ H
      simpa only [map_mul, map_inv] using hs
  rintro _ ⟨x, hx, rfl⟩
  exact hle hx

private theorem model_generation (g : SL) (i : Bool) :
    (modelParabolic g (!i)).pCoreIn 2 ≤ modelParabolic g i ∧
    ∃ t s : SL, t ∈ (modelParabolic g (!i)).pCoreIn 2 ∧ s ∈ modelParabolic g i ∧
      (∀ H : Subgroup SL, (modelParabolic g i).pCoreIn 2 ≤ H → t ∈ H →
        s * t * s⁻¹ ∈ H → modelParabolic g i ≤ H) := by
  cases i
  · exact transport_generation (MulAut.conj g)
  · have hline : lineParabolicSL.map diagram.toMonoidHom = pointParabolicSL := by
      rw [← pointParabolic_map_diagram, map_map]
      have he : diagram.toMonoidHom.comp diagram.toMonoidHom = MonoidHom.id SL := by
        ext x : 1; exact diagram_involutive x
      rw [he, map_id]
    have h := transport_generation (diagram.trans (MulAut.conj g))
    have hp : pointParabolicSL.map (diagram.trans (MulAut.conj g)).toMonoidHom =
        modelParabolic g true := by
      change pointParabolicSL.map ((MulAut.conj g).toMonoidHom.comp diagram.toMonoidHom) = _
      rw [← map_map, pointParabolic_map_diagram]
      rfl
    have hq : lineParabolicSL.map (diagram.trans (MulAut.conj g)).toMonoidHom =
        modelParabolic g false := by
      change lineParabolicSL.map ((MulAut.conj g).toMonoidHom.comp diagram.toMonoidHom) = _
      rw [← map_map, hline]
      rfl
    simpa only [hp, hq, Bool.not_true] using h

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R}

omit [Finite M] in
/-- The image of each parabolic preimage is its specified flag stabilizer. -/
theorem frame_parabolic_image (f : Frame source) (i : Bool) :
    (f.parabolic i).map source.projection =
      modelParabolic f.flag (if i then !f.first else f.first) :=
  map_comap_eq_self_of_surjective source.projection_surjective _

/-- The intrinsic parabolic core maps onto the intrinsic core of its actual image. -/
theorem frame_core_image (f : Frame source) (i : Bool) :
    (f.core i).map source.projection = ((f.parabolic i).map source.projection).pCoreIn 2 := by
  exact map_pCoreIn_of_ker_isPGroup source.projection
    (by rw [source.projection_kernel]; exact pCore_isPGroup) (f.parabolic i)

/-- The opposite core lies in the parabolic, and one of its transvections,
with a parabolic conjugate, generates modulo the parabolic's intrinsic core. -/
theorem frame_transvection_generators (f : Frame source) :
    (f.core false).map source.projection ≤ (f.parabolic true).map source.projection ∧
    ∃ t s : SL, t ∈ (f.core false).map source.projection ∧
      s ∈ (f.parabolic true).map source.projection ∧
      (∀ H : Subgroup SL, (f.core true).map source.projection ≤ H → t ∈ H →
        s * t * s⁻¹ ∈ H → (f.parabolic true).map source.projection ≤ H) := by
  simp only [frame_core_image, frame_parabolic_image, Bool.false_eq_true, if_false, if_true]
  have h := model_generation f.flag (!f.first)
  simpa only [Bool.not_not] using h
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
