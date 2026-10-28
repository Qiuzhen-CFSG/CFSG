module

public import Theory.Mathieu.M23.QuasithinGeometry.CommonFour.Checks
public import Theory.Representation.MathieuCodeRestriction.CodeLocal

/-!
# A compatible native M23 Sylow marking

The certified coordinate witnesses place the enumerated Sylow subgroup in
both the standard quintet and heptad stabilizers. Its two E16 subgroups lie
in the restrictions of the actual sextet and octad cores. The two local
conjugators give the Sylow-intersection bounds used to identify the intrinsic
cores in `Cores.lean`.

Source: Aschbacher–Smith, H.14.2(1), printed p.397. See `source/README.md`
for the witness discovery and kernel certificate provenance.
-/

@[expose] public section
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.CommonFour
open M24LocalGeometry MathieuCode FusionCertificate ElementarySylow
set_option maxRecDepth 100000
set_option Elab.async false

noncomputable def standardSylow : Sylow 2 M23 := transport • sylow
noncomputable def standardCandidate (b : Fin 2) : Subgroup M23 :=
  (candidate b).map (MulAut.conj transport).toMonoidHom

noncomputable def markedElement (i : Fin 128) : M23 :=
  (MulAut.conj transport) ⟨perm i, rawSubgroup_le (perm_mem i)⟩

theorem markedElement_val (i : Fin 128) : (markedElement i).val = markedPerm i := rfl

theorem mem_standardCandidate (b : Fin 2) (x : M23) :
    x ∈ standardCandidate b ↔ ∃ i, markedPerm (candidateIndex b i) = x.val := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨i,hi⟩ := (mem_candidate b y).mp hy
    exact ⟨i, congrArg (fun p => transportPerm * p * transportPerm⁻¹) hi⟩
  · rintro ⟨i,hi⟩
    refine ⟨⟨perm (candidateIndex b i), rawSubgroup_le (perm_mem _)⟩, ⟨i,rfl⟩, ?_⟩
    exact Subtype.ext hi

theorem mem_standardSylow (x : M23) :
    x ∈ standardSylow.toSubgroup ↔ ∃ i, markedPerm i = x.val := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨i,hi⟩ := exists_perm ⟨y.val,hy⟩
    exact ⟨i, congrArg (fun p => transportPerm * p * transportPerm⁻¹) hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨⟨perm i,rawSubgroup_le (perm_mem i)⟩, perm_mem i, Subtype.ext hi⟩

theorem standardCandidate_le_sylow (b : Fin 2) :
    standardCandidate b ≤ standardSylow.toSubgroup := Subgroup.map_mono (candidate_le_sylow b)

theorem standardCandidate_card (b : Fin 2) : Nat.card (standardCandidate b) = 16 := by
  rw [standardCandidate, Subgroup.card_map_of_injective (MulAut.conj transport).injective,
    candidate_card]

theorem standardCandidate_elementary (b : Fin 2) : IsElementaryAbelian 2 (standardCandidate b) := by
  let _ := candidate_elementary b
  exact IsElementaryAbelian.map _

noncomputable def quintetStabilizer : Subgroup M23 :=
  (sextetStabilizer standardSextet).comap pointEmbedding
noncomputable def markedHeptadStabilizer : Subgroup M23 :=
  (octadStabilizer standardOctad).comap pointEmbedding

private theorem subgroup_le_of_generators (H : Subgroup M23)
    (h : ∀ j, (⟨gen j, gen_mem j⟩ : M23) ∈ H) : subgroup ≤ H := by
  have hr : rawSubgroup ≤ H.map M23.subtype := by
    rintro _ ⟨w,rfl⟩
    induction w with
    | nil => exact (H.map M23.subtype).one_mem
    | cons j w ih => exact (H.map M23.subtype).mul_mem ⟨⟨gen j,gen_mem j⟩,h j,rfl⟩ ih
  intro x hx
  obtain ⟨y,hy,he⟩ := hr hx
  exact (Subtype.ext he : y = x) ▸ hy

private theorem standardSylow_le_both : standardSylow.toSubgroup ≤
    quintetStabilizer ⊓ markedHeptadStabilizer := by
  change subgroup.map (MulAut.conj transport).toMonoidHom ≤ _
  rw [Subgroup.map_le_iff_le_comap]
  apply subgroup_le_of_generators
  intro j
  constructor
  · change (standardSextet.parts.image (fun A => A.image
      ((pointEmbedding ((MulAut.conj transport) ⟨gen j,gen_mem j⟩)).val))) = _
    have hv : (((MulAut.conj transport) ⟨gen j,gen_mem j⟩) : M23).val =
        transportPerm * gen j * transportPerm⁻¹ := rfl
    have he := funext (pointEmbedding_apply_all
      ((MulAut.conj transport) ⟨gen j,gen_mem j⟩))
    rw [hv] at he
    rw [he]
    exact (stabilizes_generators j).1
  · change standardOctad.val.image
      ((pointEmbedding ((MulAut.conj transport) ⟨gen j,gen_mem j⟩)).val) = _
    have hv : (((MulAut.conj transport) ⟨gen j,gen_mem j⟩) : M23).val =
        transportPerm * gen j * transportPerm⁻¹ := rfl
    have he := funext (pointEmbedding_apply_all
      ((MulAut.conj transport) ⟨gen j,gen_mem j⟩))
    rw [hv] at he
    rw [he]
    exact (stabilizes_generators j).2

theorem standardSylow_le_quintet : standardSylow.toSubgroup ≤ quintetStabilizer :=
  standardSylow_le_both.trans inf_le_left

theorem standardSylow_le_heptad : standardSylow.toSubgroup ≤ markedHeptadStabilizer :=
  standardSylow_le_both.trans inf_le_right

theorem candidate0_le_sextetCore : standardCandidate 0 ≤ SextetCore.core.comap pointEmbedding := by
  let P := (standardCandidate 0).map pointEmbedding
  have hp : IsPGroup 2 P := ((standardCandidate_elementary 0).isPGroup 2 _).map pointEmbedding
  have hPS : P ≤ sextetStabilizer standardSextet := by
    rintro _ ⟨x,hx,rfl⟩
    exact standardSylow_le_quintet (standardCandidate_le_sylow 0 hx)
  have hPF : P ≤ SextetCore.partFixers := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨i,hi⟩ := (mem_standardCandidate 0 x).mp hx
    apply Subgroup.mem_iInf.mpr
    intro j
    change (standardTetrad j).image ((pointEmbedding x).val) = _
    have he : ⇑(pointEmbedding x).val = extendPoint (markedPerm (candidateIndex 0 i)) := by
      funext a
      rw [pointEmbedding_apply_all, hi]
    rw [he]
    exact candidate0_fixes i j
  intro x hx
  exact SextetCore.two_subgroup_le_core P hp hPS hPF ⟨x,hx,rfl⟩

theorem candidate1_le_octadCore : standardCandidate 1 ≤
    ((pCore 2 (octadStabilizer standardOctad)).map
      (octadStabilizer standardOctad).subtype).comap pointEmbedding := by
  rw [octad_core_map_eq_pointwise]
  intro x hx
  obtain ⟨i,hi⟩ := (mem_standardCandidate 1 x).mp hx
  apply (mem_octadPointwiseKernel standardOctad (pointEmbedding x)).mpr
  intro a ha
  change (pointEmbedding x).val a = a
  rw [pointEmbedding_apply_all, ← hi]
  exact candidate1_fixes i a ha

noncomputable def move (b : Fin 2) : M23 := if b = 0 then quintetMove else heptadMove

theorem move_mem (b : Fin 2) : move b ∈
    (if b = 0 then quintetStabilizer else markedHeptadStabilizer) := by
  fin_cases b
  · change (standardSextet.parts.image (fun A => A.image ((pointEmbedding quintetMove).val))) = _
    rw [quintetMove_embedding]
    decide +kernel
  · change standardOctad.val.image ((pointEmbedding heptadMove).val) = _
    rw [heptadMove_embedding]
    decide +kernel

/-- Two conjugate Sylow groups have intersection contained in the specified E16. -/
theorem sylow_intersection_le_candidate (b : Fin 2) (x : M23)
    (hx : x ∈ standardSylow.toSubgroup)
    (hy : move b * x * (move b)⁻¹ ∈ standardSylow.toSubgroup) :
    x ∈ standardCandidate b := by
  obtain ⟨i,hi⟩ := (mem_standardSylow x).mp hx
  obtain ⟨j,hj⟩ := (mem_standardSylow _).mp hy
  have hconj : relativePerm b * perm i * (relativePerm b)⁻¹ = perm j := by
    have hr : relativePerm b = transportPerm⁻¹ * (move b).val * transportPerm := by
      fin_cases b <;> exact relative_correct _
    rw [hr]
    have he : (move b).val * markedPerm i * ((move b).val)⁻¹ = markedPerm j := by
      rw [hi]
      exact hj.symm
    have hh := congrArg (fun p => transportPerm⁻¹ * p * transportPerm) he
    simpa [markedPerm, mul_assoc] using hh
  obtain ⟨a,ha⟩ := intersection_indices b i j hconj
  exact (mem_standardCandidate b x).mpr ⟨a, ha ▸ hi⟩

end Sporadic.Mathieu.M23Geometry.CommonFour
