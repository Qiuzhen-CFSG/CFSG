module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryCore

/-!
# The reduced image of the literal escaping quotient action

The kernel of I acting on U/Z_S is the preimage of the centralizer of
the image of U in I/Z_S. Both comparisons use the original quotient maps
and conjugation on representatives. Reducedness of that image therefore
proves O₂(I*) = 1 for I* = range(NaturalEscape.action).

An element of the action kernel preserves V_L because Z_S ≤ V_L.
The E.6.1 normalizer bound consequently puts that kernel in M. In the
escaping branch the image of M ∩ I is thus proper in I*, as required
before selecting the source component. No component is assumed or
constructed by these kernel calculations.

The initial natural action and remaining component geometry stay with
qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith, 6.1.24(4) and the following paragraph,
printed pp.676–677.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- The action kernel is the exact preimage of the centralizer in I/Z_S. -/
theorem natural_escape_action_kernel
    (h : Hypothesis611 κ T L M V n) :
    letI := h.ZS_normal_in_escape_U
    letI := natural_escape_central_line_normal (T := T) (L := L) (V := V)
    let q := QuotientGroup.mk' ((ZS (T : Subgroup G) L V).subgroupOf (Escape.I (T : Subgroup G) L V))
    (NaturalEscape.action (T : Subgroup G) L V).ker =
      (centralizer (((Escape.U (T : Subgroup G) L V).subgroupOf
        (Escape.I (T : Subgroup G) L V)).map q : Set _)).comap q := by
  let := h.ZS_normal_in_escape_U
  let := natural_escape_central_line_normal (T := T) (L := L) (V := V)
  let I := Escape.I (T : Subgroup G) L V
  let U := Escape.U (T : Subgroup G) L V
  let Z := ZS (T : Subgroup G) L V
  let a := NaturalEscape.action (T : Subgroup G) L V
  let q := QuotientGroup.mk' (Z.subgroupOf I)
  let qU := QuotientGroup.mk' (Z.subgroupOf U)
  have hUI : U ≤ I := Escape.U_centralizes_ZS h.layer_centralizes_ZS
  have hfix (i : I) (u : U) :
      a i (qU u) = qU u ↔
        q ⟨u,hUI u.property⟩ * q i = q i * q ⟨u,hUI u.property⟩ := by
    rw [NaturalEscape.action_mk]
    have he : q (i * (⟨u,hUI u.property⟩ : I) * i⁻¹) = q ⟨u,hUI u.property⟩ ↔
        q ⟨u,hUI u.property⟩ * q i = q i * q ⟨u,hUI u.property⟩ := by
      rw [map_mul,map_mul,map_inv,mul_inv_eq_iff_eq_mul,eq_comm]
    rw [← he]
    constructor
    · intro hh
      have hz := (QuotientGroup.eq_iff_div_mem (N := Z.subgroupOf U)).mp hh
      exact QuotientGroup.eq_iff_div_mem.mpr hz
    · intro hh
      have hz := (QuotientGroup.eq_iff_div_mem (N := Z.subgroupOf I)).mp hh
      exact QuotientGroup.eq_iff_div_mem.mpr hz
  ext i
  change a i = 1 ↔ q i ∈ centralizer ((U.subgroupOf I).map q : Set (I ⧸ Z.subgroupOf I))
  rw [mem_centralizer_iff]
  constructor
  · intro hi x hx
    obtain ⟨u,hu,rfl⟩ := hx
    exact (hfix i ⟨u,hu⟩).mp (by rw [hi]; rfl)
  · intro hi
    ext x
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) x
    exact (hfix i u).mpr (hi _ (mem_map_of_mem q u.property))

/-- Fixing U/Z_S preserves the original natural seed, since its denominator lies in that seed. -/
theorem natural_escape_action_kernel_normalizes_layer
    (h : Hypothesis611 κ T L M V n) :
    letI := h.ZS_normal_in_escape_U
    (NaturalEscape.action (T : Subgroup G) L V).ker.map
      (Escape.I (T : Subgroup G) L V).subtype ≤ normalizer (layer L V : Set G) := by
  let := h.ZS_normal_in_escape_U
  apply le_normalizer_iff.mpr
  rintro i ⟨j,hj,rfl⟩ b hb
  let u : Escape.U (T : Subgroup G) L V := ⟨b,Escape.layer_le_U _ _ _ hb⟩
  have hh := congrArg (fun f : MulAut (NaturalEscape.Quotient (T : Subgroup G) L V) =>
    f (QuotientGroup.mk' ((ZS (T : Subgroup G) L V).subgroupOf
      (Escape.U (T : Subgroup G) L V)) u)) (MonoidHom.mem_ker.mp hj)
  rw [NaturalEscape.action_mk] at hh
  have hz := QuotientGroup.eq_iff_div_mem.mp hh
  change (j : G) * b * (j : G)⁻¹ / b ∈ ZS (T : Subgroup G) L V at hz
  change (j : G) * b * (j : G)⁻¹ ∈ layer L V
  simpa only [div_mul_cancel] using (layer L V).mul_mem ((show ZS (T : Subgroup G) L V ≤ layer L V from inf_le_left) hz) hb

/-- Kernel containment preserves the escaping condition in the actual action image. -/
theorem natural_escape_action_image_proper
    (h : Hypothesis611 κ T L M V n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hI : ¬ Escape.I (T : Subgroup G) L V ≤ M) :
    letI := h.ZS_normal_in_escape_U
    (M.subgroupOf (Escape.I (T : Subgroup G) L V)).map
      (NaturalEscape.action (T : Subgroup G) L V) <
      (NaturalEscape.action (T : Subgroup G) L V).range := by
  let := h.ZS_normal_in_escape_U
  let I := Escape.I (T : Subgroup G) L V
  let a := NaturalEscape.action (T : Subgroup G) L V
  have hk : a.ker ≤ M.subgroupOf I := by
    intro i hi
    exact hE.normalizer_le (natural_escape_action_kernel_normalizes_layer h
      (mem_map_of_mem I.subtype hi))
  apply lt_of_le_not_ge (map_le_range a _)
  intro hr
  apply hI
  intro i hi
  have hm : (⟨i,hi⟩ : I) ∈ ((M.subgroupOf I).map a).comap a :=
    hr ⟨⟨i,hi⟩,rfl⟩
  rwa [comap_map_eq_self hk] at hm

/-- Source 6.1.24(4) on the literal I-action image, from the proved reduced image in I/Z_S. -/
theorem natural_escape_action_twoCore_eq_bot
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n) :
    letI := h.ZS_normal_in_escape_U
    pCore 2 (NaturalEscape.action (T : Subgroup G) L V).range = ⊥ := by
  let := h.ZS_normal_in_escape_U
  let := natural_escape_central_line_normal (T := T) (L := L) (V := V)
  let I := Escape.I (T : Subgroup G) L V
  let U := Escape.U (T : Subgroup G) L V
  let Z := ZS (T : Subgroup G) L V
  let q := QuotientGroup.mk' (Z.subgroupOf I)
  let B := (U.subgroupOf I).map q
  have hred : IsPReduced 2 B := (natural_escape_reduced_core h hnatural).1
  let := hred.normal
  let b := (QuotientGroup.mk' (centralizer (B : Set (I ⧸ Z.subgroupOf I)))).comp q
  have hb : Function.Surjective b := (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  let a := NaturalEscape.action (T : Subgroup G) L V
  have hk : a.ker = b.ker := by
    change a.ker = ((QuotientGroup.mk' (centralizer (B : Set _))).comp q).ker
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact natural_escape_action_kernel h
  let e : (I ⧸ a.ker) ≃* ((I ⧸ Z.subgroupOf I) ⧸ centralizer (B : Set (I ⧸ Z.subgroupOf I))) :=
    (QuotientGroup.quotientMulEquivOfEq hk).trans (QuotientGroup.quotientKerEquivOfSurjective b hb)
  let f := e.symm.trans (QuotientGroup.quotientKerEquivRange a)
  have hm := pCore_map_iso 2 f
  rw [hred.quotient_pCore_eq_bot,Subgroup.map_bot] at hm
  exact hm.symm

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
