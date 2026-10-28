module

public import Theory.Representation.G2BinaryModelOffenders

/-!
# Offender geometry on the full binary G₂ Weyl module

The scalar quotient preserves offender codimensions. Every offender is thus
conjugate to the A–B–C elementary eight. On the full trace-zero octonion space
its commutator equals its four-dimensional fixed space: the last octonion
coordinate supplies the scalar direction as well as the first three coordinates.
The fixed spaces already form one orbit under the actual derived subgroup.

Source: Aschbacher–Smith B.4.6(3),(13), pp.88–90, and the module geometry used
in 12.4.9, p.816. Coordinates use the existing ATLAS-attributed root maps.
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender Atlas.SplitOctonion
namespace Atlas.G2.Natural.OrthogonalCover.BinaryOffenders
open Explicit NaturalOffenders
local notation "𝔽" => ZMod 2
local notation "σ" => traceZeroAction 𝔽
local notation "τ" => Natural.action 𝔽
local notation "E" => EvenTwoRank.elementary 𝔽

/-- All scalar vectors are fixed by every subgroup of the full G₂ group. -/
theorem scalarLine_le_fixedSpace (A : Subgroup (Model 𝔽)) :
    scalarLine 𝔽 ≤ fixedSpace σ A := by
  rw [scalarLine, Submodule.span_singleton_le_iff_mem]
  intro g
  exact traceZeroAction_identity 𝔽 g.val

/-- Passing to the actual natural quotient preserves the offender inequality. -/
theorem offender_iff_natural (A : Subgroup (Model 𝔽)) :
    IsOffender σ A ↔ IsOffender τ A := by
  simp only [IsOffender, BinaryModelOffenders.weyl_fixedCodim]

/-- Every full Weyl offender is a conjugate of the actual A–B–C eight. -/
theorem offender_conjugate (A : Subgroup (Model 𝔽)) (hA : IsOffender σ A) :
    ∃ g : Model 𝔽, A = (E).map (MulAut.conj g).toMonoidHom :=
  natural_offender_conjugate_elementary (n := 1) (by norm_num) (by decide) A
    ((offender_iff_natural A).mp hA)

/-- Weyl offenders have binary rank three. -/
theorem offender_rank (A : Subgroup (Model 𝔽)) (hA : IsOffender σ A) :
    rank A = 3 := by
  exact natural_offender_rank (n := 1) (by norm_num) (by decide) A
    ((offender_iff_natural A).mp hA)

/-- Weyl offenders have fixed codimension three. -/
theorem offender_fixedCodim (A : Subgroup (Model 𝔽)) (hA : IsOffender σ A) :
    fixedCodim σ A = 3 := by
  rw [BinaryModelOffenders.weyl_fixedCodim]
  exact natural_offender_fixedCodim (n := 1) (by norm_num) (by decide) A
    ((offender_iff_natural A).mp hA)

/-- The full fixed space has dimension four, including the scalar radical. -/
theorem offender_fixed_finrank (A : Subgroup (Model 𝔽)) (hA : IsOffender σ A) :
    Module.finrank 𝔽 (fixedSpace σ A) = 4 := by
  have hh := fixedCodim_add_finrank σ A
  rw [offender_fixedCodim A hA, finrank_traceZero] at hh
  omega

private theorem trace_coordinates (x : TraceZero 𝔽) : x.val 4 = x.val 3 := by
  have hx : x.val 3 + x.val 4 = 0 := x.property
  simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hx

/-- The standard fixed four-space is the preimage of the natural upper space. -/
theorem mem_fixed_elementary_iff (x : TraceZero 𝔽) :
    x ∈ fixedSpace σ E ↔ x.val 5 = 0 ∧ x.val 6 = 0 ∧ x.val 7 = 0 := by
  constructor
  · intro hx
    have hA := hx ⟨rootA 1, rootA_mem_elementary 1⟩
    have hB := hx ⟨rootB 1, rootB_mem_elementary 1⟩
    change σ (rootA 1) x = x at hA
    change σ (rootB 1) x = x at hB
    have h5 := congrArg (fun y : TraceZero 𝔽 => y.val 0) hB
    have h6 := congrArg (fun y : TraceZero 𝔽 => y.val 0) hA
    have h7 := congrArg (fun y : TraceZero 𝔽 => y.val 1) hA
    change x.val 0 - (1 : 𝔽) * x.val 5 = x.val 0 at h5
    change x.val 0 - (1 : 𝔽) * x.val 6 = x.val 0 at h6
    change x.val 1 + (1 : 𝔽) * x.val 7 = x.val 1 at h7
    simp only [one_mul] at h5 h6 h7
    exact ⟨sub_eq_self.mp h5, sub_eq_self.mp h6, add_eq_left.mp h7⟩
  · rintro ⟨h5, h6, h7⟩ ⟨g, hg⟩
    obtain ⟨p, rfl⟩ := hg
    apply Subtype.ext
    ext i
    fin_cases i <;>
      simp [EvenTwoRank.elementaryEmbedding, EvenTwoRank.elementaryParameters,
        unipotentProduct, traceZeroAction_val, rootA, rootB, rootC,
        rootAEquiv, rootBEquiv, rootCEquiv, rootALinear, rootBLinear, rootCLinear,
        rootAApply, rootBApply, rootCApply, h5, h6, h7, trace_coordinates x,
        CharTwo.neg_eq]

private def fifthVector (t : 𝔽) : TraceZero 𝔽 :=
  ⟨![0,0,0,0,0,t,0,0], by simp [trace]⟩

private def sixthVector (t : 𝔽) : TraceZero 𝔽 :=
  ⟨![0,0,0,0,0,0,t,0], by simp [trace]⟩

private def seventhVector (t : 𝔽) : TraceZero 𝔽 :=
  ⟨![0,0,0,0,0,0,0,t], by simp [trace]⟩

/-- The full standard Weyl commutator contains its scalar radical. -/
theorem elementary_commutator_eq_fixed :
    subspaceCommutator σ ⊤ E = fixedSpace σ E := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, x, _, rfl⟩
    apply (mem_fixed_elementary_iff _).mpr
    obtain ⟨p, rfl⟩ := hg
    simp [EvenTwoRank.elementaryEmbedding, EvenTwoRank.elementaryParameters,
      unipotentProduct, traceZeroAction_val, rootA, rootB, rootC,
      rootAEquiv, rootBEquiv, rootCEquiv, rootALinear, rootBLinear, rootCLinear,
      rootAApply, rootBApply, rootCApply]
  · intro x hx
    obtain ⟨h5, h6, h7⟩ := (mem_fixed_elementary_iff x).mp hx
    have hm (a : Model 𝔽) (ha : a ∈ E) (y : TraceZero 𝔽) :
        σ a y - y ∈ subspaceCommutator σ ⊤ E :=
      Submodule.subset_span ⟨a, ha, y, Submodule.mem_top, rfl⟩
    have h0 := hm (rootA 1) (rootA_mem_elementary 1) (sixthVector (x.val 0 + x.val 3))
    have h1 := hm (rootC 1) (rootC_mem_elementary 1) (fifthVector (x.val 1))
    have h2 := hm (rootC 1) (rootC_mem_elementary 1) (sixthVector (x.val 2))
    have hs := hm (rootC 1) (rootC_mem_elementary 1) (seventhVector (x.val 3))
    have he : ((σ (rootA 1) (sixthVector (x.val 0 + x.val 3)) -
        sixthVector (x.val 0 + x.val 3)) +
        (σ (rootC 1) (fifthVector (x.val 1)) - fifthVector (x.val 1)) +
        (σ (rootC 1) (sixthVector (x.val 2)) - sixthVector (x.val 2))) +
        (σ (rootC 1) (seventhVector (x.val 3)) - seventhVector (x.val 3)) = x := by
      apply Subtype.ext
      ext i
      fin_cases i <;>
        simp [traceZeroAction_val, rootA, rootC, rootAEquiv, rootCEquiv,
          rootALinear, rootCLinear, rootAApply, rootCApply, fifthVector,
          sixthVector, seventhVector, CharTwo.neg_eq, h5, h6, h7,
          trace_coordinates x, add_assoc, CharTwo.add_self_eq_zero]
    rw [← he]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ h0 h1) h2) hs

private theorem fixed_conjugate (A : Subgroup (Model 𝔽)) (g : Model 𝔽) :
    fixedSpace σ (A.map (MulAut.conj g).toMonoidHom) =
      (fixedSpace σ A).map (σ g) := by
  let e := LinearEquiv.ofBijective (σ g) ((σ).apply_bijective g)
  symm
  apply fixedSpace_map_equivariant σ σ (MulAut.conj g).toMonoidHom e
  intro a v
  change σ g (σ a v) = σ (g*a*g⁻¹) (σ g v)
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

private theorem commutator_conjugate (A : Subgroup (Model 𝔽)) (g : Model 𝔽) :
    subspaceCommutator σ ⊤ (A.map (MulAut.conj g).toMonoidHom) =
      (subspaceCommutator σ ⊤ A).map (σ g) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨a, ha, rfl⟩, x, _, rfl⟩
    refine ⟨σ a (σ g⁻¹ x) - σ g⁻¹ x,
      Submodule.subset_span ⟨a, ha, σ g⁻¹ x, Submodule.mem_top, rfl⟩, ?_⟩
    simp only [map_sub, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      map_mul, Module.End.mul_apply, (σ).self_inv_apply]
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, x, _, rfl⟩
    change σ g (σ a x - x) ∈ subspaceCommutator σ ⊤ (A.map (MulAut.conj g).toMonoidHom)
    have he : σ g (σ a x - x) = σ (g*a*g⁻¹) (σ g x) - σ g x := by
      simp only [map_sub, map_mul, Module.End.mul_apply, (σ).inv_self_apply]
    rw [he]
    exact Submodule.subset_span ⟨g*a*g⁻¹,
      mem_map_of_mem (MulAut.conj g).toMonoidHom ha,
      σ g x, Submodule.mem_top, rfl⟩

/-- B.4.6 commutator geometry on the full seven-dimensional Weyl module. -/
theorem offender_commutator_eq_fixed (A : Subgroup (Model 𝔽)) (hA : IsOffender σ A) :
    subspaceCommutator σ ⊤ A = fixedSpace σ A := by
  obtain ⟨g, rfl⟩ := offender_conjugate A hA
  rw [commutator_conjugate, fixed_conjugate, elementary_commutator_eq_fixed]

/-- The original fixed line lies in every offender commutator. -/
theorem scalarLine_le_offender_commutator (A : Subgroup (Model 𝔽))
    (hA : IsOffender σ A) : scalarLine 𝔽 ≤ subspaceCommutator σ ⊤ A := by
  rw [offender_commutator_eq_fixed A hA]
  exact scalarLine_le_fixedSpace A

/-- The fixed spaces form one orbit already under the actual derived group. -/
theorem offender_fixed_space_derived_orbit (A : Subgroup (Model 𝔽))
    (hA : IsOffender σ A) :
    ∃ d : commutator (Model 𝔽),
      fixedSpace σ A = (fixedSpace σ E).map (σ d.val) := by
  obtain ⟨g, rfl⟩ := offender_conjugate A hA
  rw [fixed_conjugate]
  by_cases hd : g ∈ commutator (Model 𝔽)
  · exact ⟨⟨g, hd⟩, rfl⟩
  · have hi : (commutator (Model 𝔽)).index = 2 := by
      rw [BinaryParabolicPair.commutator_eq_longRootClosure, BinaryException.index_H]
    have hc : rootC (1 : 𝔽) ∉ commutator (Model 𝔽) :=
      BinaryNormalizer.rootC_not_mem_derived
    have hgd : g * rootC (1 : 𝔽) ∈ commutator (Model 𝔽) :=
      ((commutator (Model 𝔽)).mul_mem_iff_of_index_two hi).mpr (iff_of_false hd hc)
    refine ⟨⟨g * rootC 1, hgd⟩, ?_⟩
    have hmap : (fixedSpace σ E).map (σ (g * rootC 1)) =
        (fixedSpace σ E).map (σ g) := by
      ext x
      constructor <;> rintro ⟨v, hv, rfl⟩ <;> refine ⟨v, hv, ?_⟩
      all_goals
        have hcv : σ (rootC 1) v = v := hv ⟨rootC 1, rootC_mem_elementary 1⟩
        simp only [map_mul, Module.End.mul_apply, hcv]
    exact hmap.symm

/-- Any two offender fixed spaces are conjugate by an actual derived element. -/
theorem offender_fixed_spaces_derived_conjugate (A B : Subgroup (Model 𝔽))
    (hA : IsOffender σ A) (hB : IsOffender σ B) :
    ∃ d : commutator (Model 𝔽),
      fixedSpace σ B = (fixedSpace σ A).map (σ d.val) := by
  obtain ⟨a, ha⟩ := offender_fixed_space_derived_orbit A hA
  obtain ⟨b, hb⟩ := offender_fixed_space_derived_orbit B hB
  refine ⟨b * a⁻¹, ?_⟩
  rw [ha, hb, ← Submodule.map_comp]
  congr 1
  change σ b.val = σ (b.val * a.val⁻¹) * σ a.val
  rw [← map_mul, inv_mul_cancel_right]

/-- The commutator is nontrivial even when retaining the full scalar cover. -/
theorem offender_commutator_ne_bot (A : Subgroup (Model 𝔽)) (hA : IsOffender σ A) :
    subspaceCommutator σ ⊤ A ≠ ⊥ := by
  intro hb
  have hf := offender_fixed_finrank A hA
  rw [← offender_commutator_eq_fixed A hA, hb, finrank_bot] at hf
  omega

/-- The literal model premises for the fixed-line and nontrivial-commutator
inputs in the original 12.4.9 consumer. The ambient transport and symmetry
of the two original subgroups use these same commutator and fixed spaces. -/
theorem offender_commutator_geometry (A : Subgroup (Model 𝔽)) (hA : IsOffender σ A) :
    OneCohomology.fixed (OrthogonalCover.action 𝔽) ≤ subspaceCommutator σ ⊤ A ∧
      subspaceCommutator σ ⊤ A = fixedSpace σ A ∧
      subspaceCommutator σ ⊤ A ≠ ⊥ ∧
      Module.finrank 𝔽 (fixedSpace σ A) = 4 ∧ rank A = 3 := by
  rw [fixed_eq_scalarLine]
  exact ⟨scalarLine_le_offender_commutator A hA, offender_commutator_eq_fixed A hA,
    offender_commutator_ne_bot A hA, offender_fixed_finrank A hA, offender_rank A hA⟩

end Atlas.G2.Natural.OrthogonalCover.BinaryOffenders
