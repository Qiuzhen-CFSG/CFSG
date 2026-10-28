module

public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicGeneration.FirstPlane
public import CFSG.Quasithin.ChapterJ.Section04To05.Setup.Flag

/-!
# The second parabolic generates the original plane from Z

The selected element of L₂ moves the order-two point Z, and the two points
span V₂. The original S centralizes V₂. Consequently any supplement to S in
G₂ has the same point span V₂. In particular the later constructed F₂ does.
This is the second-parabolic generation step in J.4.5(1), with the literal
source subgroups and conjugator.

Source: Aschbacher–Smith, J.4.5, printed p.442.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} {p : Plane d}

/-- The original parabolic point span is the chosen plane. -/
theorem SourceChoice.point_span_parabolic (s : SourceChoice p) :
    conjugateSpanBy d.toTypeRuSetup.Z p.parabolic = p.group := by
  apply le_antisymm
  · exact conjugateSpanBy_le p.point_le (fun x hx => ((p.mem_parabolic x).mp hx).2)
  · rw [s.plane_eq_join_points]
    refine sup_le (le_conjugateSpanBy _ _) ?_
    rintro x ⟨z,hz,rfl⟩
    exact subset_closure ⟨s.g,p.L₂_le_parabolic s.in_residual,z,hz,rfl⟩

/-- A supplement to S has the same literal point span as G₂. -/
theorem SourceChoice.point_span_supplement (s : SourceChoice p) (J : Subgroup G)
    (hJS : J ⊔ d.toTypeRuSetup.S = p.parabolic) :
    conjugateSpanBy d.toTypeRuSetup.Z J = p.group := by
  let M := conjugateSpanBy d.toTypeRuSetup.Z J
  have hJP : J ≤ p.parabolic := hJS ▸ le_sup_left
  have hMP : M ≤ p.group := (conjugateSpanBy_mono le_rfl hJP).trans_eq s.point_span_parabolic
  have hS : d.toTypeRuSetup.S ≤ centralizer (M : Set G) := by
    have he : centralizer (d.V : Set G) = d.toTypeRuSetup.S := d.ru1.centralizer_V
    rw [← he]
    exact centralizer_le (hMP.trans p.le_seed)
  have hP : p.parabolic ≤ normalizer (M : Set G) := by
    rw [← hJS]
    exact sup_le (le_normalizer_conjugateSpanBy _ _) (hS.trans (Subgroup.centralizer_le_normalizer _))
  apply le_antisymm hMP
  rw [← s.point_span_parabolic]
  exact conjugateSpanBy_le (le_conjugateSpanBy _ _) hP

/-- The generation statement used to push Z into the normal two-core of F. -/
theorem SourceChoice.plane_le_of_supplement_normalized (s : SourceChoice p)
    (J N : Subgroup G) (hJS : J ⊔ d.toTypeRuSetup.S = p.parabolic)
    (hZ : d.toTypeRuSetup.Z ≤ N) (hJ : J ≤ normalizer (N : Set G)) :
    p.group ≤ N := by
  rw [← s.point_span_supplement J hJS]
  exact conjugateSpanBy_le hZ hJ

open scoped Pointwise in
/-- The same supplement transfers every original U-conjugate into N. -/
theorem SourceChoice.conjugate_U_le_of_supplement_normalized (s : SourceChoice p)
    (J N : Subgroup G) (hJS : J ⊔ d.toTypeRuSetup.S = p.parabolic)
    (hU : d.toTypeRuSetup.U ≤ N) (hJ : J ≤ normalizer (N : Set G)) :
    d.toTypeRuSetup.U.map (MulAut.conj s.g).toMonoidHom ≤ N := by
  have hJP : J ≤ p.parabolic := hJS ▸ le_sup_left
  have hJSn : J ≤ normalizer (d.toTypeRuSetup.S : Set G) :=
    (hJP.trans (fun x hx => ((p.mem_parabolic x).mp hx).1)).trans d.ru1.steinberg.normalized
  have hg : s.g ∈ (J : Set G) * (d.toTypeRuSetup.S : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right J d.toTypeRuSetup.S hJSn,hJS]
    exact p.L₂_le_parabolic s.in_residual
  obtain ⟨j,hj,t,ht,hjt⟩ := hg
  rintro x ⟨u,hu,rfl⟩
  have htu : t*u*t⁻¹ ∈ d.toTypeRuSetup.U :=
    mem_normalizer_iff.mp (d.ru2.natural.normalized (d.S_le_H ht)) u |>.mp hu
  have hout := mem_normalizer_iff.mp (hJ hj) (t*u*t⁻¹) |>.mp (hU htu)
  change s.g*u*s.g⁻¹ ∈ N
  rw [← hjt]
  simpa only [mul_inv_rev,mul_assoc] using hout

/-- No subgroup of Q normalized by both source actors can contain Z.
This is the terminal contradiction in the original O₂(F) argument. -/
theorem SourceChoice.not_point_le_of_supplement_normalized (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H) (J N : Subgroup G)
    (hJS : J ⊔ d.toTypeRuSetup.S = p.parabolic)
    (hNQ : N ≤ d.toTypeRuSetup.Q) (hJ : J ≤ normalizer (N : Set G))
    (hB : Centralizers.Choices.B5Image B5 ≤ normalizer (N : Set G)) :
    ¬ d.toTypeRuSetup.Z ≤ N := by
  intro hZ
  have hp := s.plane_le_of_supplement_normalized J N hJS hZ hJ
  have hU := p.U_le_of_five_normalized B5 N hp hB
  exact s.v_not_Q (hNQ (s.conjugate_U_le_of_supplement_normalized J N hJS hU hJ s.v_mem))

end CFSG.Quasithin.ChapterJ.RuSubgroup
