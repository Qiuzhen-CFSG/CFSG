module

public import Theory.SpecificGroups.PSL3.RootPlaneGeometry
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.Representation.BinaryOffender.TwoWeightMaximizer

/-!
# Saturation of binary SL₃ offenders in root planes

Sylow conjugacy and the exponent-two criterion put every elementary subgroup
in one of the two literal SL₃ root planes. Explicit matrices in its parabolic
conjugate every nonidentity element to the highest-root element. Consequently
a nontrivial subgroup invariant under that normalizer is the full root plane.
Applying exponent-two offender maximization there gives a full root plane of
fixed codimension at most four times the field degree.

This proves the geometric step of Guralnick–Malle, Classification of 2F-modules
II, author manuscript Proposition 4.7, pp.25–26, using Lemma 2.1, pp.5–6.
The conjugators refine the existing matrices in
`PSL3/EvenInnerCentralizers/InvolutionConjugacy.lean` by retaining parabolic
membership. No claim about the size of a root-plane fixed space is made here.
-/

@[expose] public section
noncomputable section

open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3Even.UnipotentGeometry
open Representation Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Inner.Coarse

variable (F : Type*) [Field F] [Finite F]

private theorem root_conjugator_central (c : F) (hc : c ≠ 0) (point : Bool) :
    ∃ g ∈ parabolicSL F point, g * specialLinear F ⟨0,0,1⟩ =
      specialLinear F ⟨0,0,c⟩ * g := by
  let g : SL(3,F) := ⟨!![c,0,0; 0,c⁻¹,0; 0,0,1], by
    simp [Matrix.det_fin_three, hc]⟩
  refine ⟨g, ?_, Subtype.ext ?_⟩
  · cases point
    · exact (mem_lineParabolicSL_iff F g).mpr ⟨rfl,rfl⟩
    · exact (mem_pointParabolicSL_iff F g).mpr ⟨rfl,rfl⟩
  · change g.val * matrix F ⟨0,0,1⟩ = matrix F ⟨0,0,c⟩ * g.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [g, matrix, Matrix.mul_apply, Fin.sum_univ_three]

private theorem root_conjugator_point (a c : F) (ha : a ≠ 0) :
    ∃ g ∈ parabolicSL F true, g * specialLinear F ⟨0,0,1⟩ =
      specialLinear F ⟨a,0,c⟩ * g := by
  let g : SL(3,F) := ⟨!![1,0,0; 0,c,a⁻¹; 0,-a,0], by
    simp [Matrix.det_fin_three, ha]⟩
  refine ⟨g, (mem_pointParabolicSL_iff F g).mpr ⟨rfl,rfl⟩, Subtype.ext ?_⟩
  change g.val * matrix F ⟨0,0,1⟩ = matrix F ⟨a,0,c⟩ * g.val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g, matrix, Matrix.mul_apply, Fin.sum_univ_three, ha]
  ring

private theorem root_conjugator_line (b c : F) (hb : b ≠ 0) :
    ∃ g ∈ parabolicSL F false, g * specialLinear F ⟨0,0,1⟩ =
      specialLinear F ⟨0,b,c⟩ * g := by
  let g : SL(3,F) := ⟨!![c,-b⁻¹,0; b,0,0; 0,0,1], by
    simp [Matrix.det_fin_three, hb]⟩
  refine ⟨g, (mem_lineParabolicSL_iff F g).mpr ⟨rfl,rfl⟩, Subtype.ext ?_⟩
  change g.val * matrix F ⟨0,0,1⟩ = matrix F ⟨0,b,c⟩ * g.val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g, matrix, Matrix.mul_apply, Fin.sum_univ_three]

/-- The actual normalizer is transitive on the nonidentity elements of either
root plane. The conjugators remain in the specified point or line parabolic. -/
theorem rootPlane_conjugator (point : Bool) (u : SL(3,F))
    (hu : u ∈ rootPlaneSL F point) (hne : u ≠ 1) :
    ∃ g ∈ Subgroup.normalizer (rootPlaneSL F point : Set SL(3,F)),
      g * specialLinear F ⟨0,0,1⟩ * g⁻¹ = u := by
  rw [normalizer_rootPlaneSL]
  suffices h : ∃ g ∈ parabolicSL F point,
      g * specialLinear F ⟨0,0,1⟩ = u * g by
    obtain ⟨g,hg,he⟩ := h
    exact ⟨g,hg,mul_inv_eq_iff_eq_mul.mpr he⟩
  cases point
  · obtain ⟨b,c,rfl⟩ := (mem_rootPlaneSL_line F u).mp hu
    by_cases hb : b = 0
    · subst b
      have hc : c ≠ 0 := by
        intro hc
        subst c
        exact hne (map_one (specialLinear F))
      exact root_conjugator_central F c hc false
    · exact root_conjugator_line F b c hb
  · obtain ⟨a,c,rfl⟩ := (mem_rootPlaneSL_point F u).mp hu
    by_cases ha : a = 0
    · subst a
      have hc : c ≠ 0 := by
        intro hc
        subst c
        exact hne (map_one (specialLinear F))
      exact root_conjugator_central F c hc true
    · exact root_conjugator_point F a c ha

/-- A nontrivial subgroup of a root plane invariant under its full normalizer
is the whole plane, including over the field of two elements. -/
theorem eq_rootPlane_of_normalized (point : Bool) (D : Subgroup SL(3,F))
    (hD : D ≤ rootPlaneSL F point) (hne : D ≠ ⊥)
    (hnorm : Subgroup.normalizer (rootPlaneSL F point : Set SL(3,F)) ≤
      Subgroup.normalizer (D : Set SL(3,F))) : D = rootPlaneSL F point := by
  obtain ⟨u,hu,hu1⟩ := D.bot_or_exists_ne_one.resolve_left hne
  obtain ⟨g,hg,he⟩ := rootPlane_conjugator F point u (hD hu) hu1
  have hroot : specialLinear F ⟨0,0,1⟩ ∈ D :=
    (Subgroup.mem_normalizer_iff.mp (hnorm hg) _).mpr (he.symm ▸ hu)
  apply le_antisymm hD
  intro v hv
  by_cases hv1 : v = 1
  · exact hv1 ▸ D.one_mem
  obtain ⟨k,hk,hke⟩ := rootPlane_conjugator F point v hv hv1
  rw [← hke]
  exact (Subgroup.mem_normalizer_iff.mp (hnorm hk) _).mp hroot

omit [Finite F] in
theorem card_rootPlane (point : Bool) :
    Nat.card (rootPlaneSL F point) = Nat.card F ^ 2 := by
  rw [rootPlaneSL, Subgroup.card_map_of_injective (specialLinear_injective F)]
  cases point
  · exact card_V₂ F
  · exact card_V₁ F

variable [CharP F 2]

/-- Simultaneous elementary-subgroup placement in one of the two literal
SL₃ root planes, using the concrete unitriangular Sylow. -/
theorem exists_conjugate_le_rootPlane {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (A : Subgroup SL(3,F)) (hA : IsElementaryTwo A) :
    ∃ g : SL(3,F), ∃ point : Bool,
      A.map (MulAut.conj g).toMonoidHom ≤ rootPlaneSL F point := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  let S₀ := Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow F hn hF
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(3,F) S S₀
  have hSyl : (S : Subgroup SL(3,F)).map (MulAut.conj g).toMonoidHom =
      unipotentSL F := congrArg Sylow.toSubgroup hg
  let C := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
  have hC : C ≤ unipotentSL F := hSyl ▸ Subgroup.map_mono hAS
  have hplanes := marked_elementary_le_plane F (unipotentSL F)
    (unipotentSLEquiv F) C hC
  have hf : markedHom F (unipotentSL F) (unipotentSLEquiv F) = specialLinear F := rfl
  rw [hf] at hplanes
  rcases hplanes with hp | hl
  · exact ⟨g,true,hp⟩
  · exact ⟨g,false,hl⟩

/-- An inner elementary offender forces one full root plane to have common
fixed codimension at most 4n. No cubicity or faithfulness is used. -/
theorem exists_rootPlane_small_codim {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) SL(3,F) V)
    (A : Subgroup SL(3,F)) (hA : IsElementaryTwo A)
    (hd : fixedCodim ρ A ≤ 2 * rank A) :
    ∃ point : Bool, fixedCodim ρ (rootPlaneSL F point) ≤ 4 * n := by
  obtain ⟨g,point,hle⟩ := exists_conjugate_le_rootPlane F hn hF A hA
  have hconj : fixedCodim ρ (A.map (MulAut.conj g).toMonoidHom) ≤
      2 * rank (A.map (MulAut.conj g).toMonoidHom) := by
    simpa only [fixedCodim_map_conj, rank_map_conj] using hd
  obtain ⟨D,hD,hnD,hnorm,hmeasure⟩ := TwoWeight.exists_normalized_offender ρ
    (rootPlaneSL F point) hle (hA.map_conj g) hconj
  have he := eq_rootPlane_of_normalized F point D hD hnD hnorm
  rw [he] at hmeasure
  have hc : Nat.card (rootPlaneSL F point) ≤ 2 ^ (2 * n) := by
    rw [card_rootPlane, hF, ← pow_mul, Nat.mul_comm n 2]
  refine ⟨point, ?_⟩
  have hh := TwoWeight.fixedCodim_le_of_card_le_measure ρ hmeasure hc
  omega

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Inner.Coarse
