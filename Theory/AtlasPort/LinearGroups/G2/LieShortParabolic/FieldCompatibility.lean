module
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Geometry

/-!
# Field compatibility of the short-local quotient

Coefficientwise transport preserves the positive roots and the short Weyl
element, hence identifies the short local groups. Reading the first two
coordinates commutes with field transport. Therefore the explicit SL₂
quotient homomorphism intertwines this local equivalence with entrywise
transport of matrices, also for coefficient automorphisms.

Source: Aschbacher--Smith, F.1.12, printed pp. 263--264.
The coefficient transport is the licensed ATLAS construction. The positive
root transport is reused from the long-local geometry module; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section
open Atlas.SplitOctonion Atlas.G2 Atlas.G2.Explicit
open scoped MatrixGroups
namespace Atlas.G2.LieParabolicSetup
variable {F K : Type*} [Field F] [Field K]

private theorem short_field_weylS (e : F ≃+* K) : fieldEquiv e weylS = weylS := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;> simp [fieldEquiv,transportAutomorphism,transportLinear,
    mapCoefficients,weylS,weylSEquiv,weylSLinear,weylSApply]

private theorem short_field_mem (e : F ≃+* K) :
    local₁ (F := F) ≤ (local₁ (F := K)).comap (fieldEquiv e).toMonoidHom := by
  apply sup_le
  · intro g hg
    rw [unipotent_eq_range] at hg
    obtain ⟨t,rfl⟩ := hg
    change fieldEquiv e (unipotentProduct t) ∈ local₁
    rw [long_field_unipotentProduct]
    exact unipotent_le_local₁ (unipotentProduct_mem _)
  · apply (Subgroup.closure_le _).mpr
    rintro g (rfl : g = weylS)
    change fieldEquiv e weylS ∈ local₁
    rw [short_field_weylS]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

/-- Coefficientwise field transport preserves the short local subgroup. -/
theorem local₁_field_mem_iff (e : F ≃+* K) (g : Model F) :
    fieldEquiv e g ∈ local₁ ↔ g ∈ local₁ := by
  constructor
  · intro hg
    have hh := short_field_mem e.symm hg
    change (fieldEquiv e).symm (fieldEquiv e g) ∈ local₁ at hh
    simpa only [MulEquiv.symm_apply_apply] using hh
  · exact fun hg => short_field_mem e hg

theorem local₁_field_map (e : F ≃+* K) :
    (local₁ (F := F)).map (fieldEquiv e).toMonoidHom = local₁ (F := K) := by
  ext g
  constructor
  · rintro ⟨h,hh,rfl⟩
    exact (local₁_field_mem_iff e h).mpr hh
  · intro hg
    refine ⟨(fieldEquiv e).symm g,?_,(fieldEquiv e).apply_symm_apply g⟩
    apply (local₁_field_mem_iff e _).mp
    simpa only [MulEquiv.apply_symm_apply] using hg

/-- The actual coefficientwise equivalence between the two local groups. -/
def local₁FieldEquiv (e : F ≃+* K) : local₁ (F := F) ≃* local₁ (F := K) :=
  ((fieldEquiv e).subgroupMap _).trans (MulEquiv.subgroupCongr (local₁_field_map e))

/-- The explicit quotient map intertwines field transport and entrywise matrix transport. -/
theorem shortSLHom_field [CharP F 2] [CharP K 2] (e : F ≃+* K) (g : local₁ (F := F)) :
    shortSLHom (local₁FieldEquiv e g) =
      Matrix.SpecialLinearGroup.map e.toRingHom (shortSLHom g) := by
  have he (i : Fin 8) : mapCoefficients e (basisVector i) = basisVector i := by
    funext j
    simp [mapCoefficients,basisVector,Pi.single_apply,apply_ite e]
  have ha (i : Fin 8) : (fieldEquiv e g.val).val (basisVector i) =
      mapCoefficients e (g.val.val (basisVector i)) := by
    simpa only [he] using fieldEquiv_action e g.val (basisVector i)
  apply Subtype.ext
  ext i j
  change (fieldEquiv e g.val).val (basisVector (j.castLE (by decide : 2 ≤ 8)))
    (i.castLE (by decide : 2 ≤ 8)) = _
  rw [ha]
  rfl

end Atlas.G2.LieParabolicSetup
