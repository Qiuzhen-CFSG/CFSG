module
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.Points

/-!
# The base line in the original Ree coset geometry

Certified point labels 0,1,3 are exactly the three neighbors of the standard
second-parabolic coset. Their membership uses the marked r₈ and s₈ images;
the actual valence three excludes additional neighbors. Translation retains
the literal point and line coset actions.

Source: Aschbacher–Smith J.5.6–7, printed p.447.
-/

@[expose] public section
noncomputable section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteBridge
open Subgroup Tits
open Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
open Tits.ExceptionalParabolics
attribute [local instance] pointAction
local instance lineAction : MulAction (Model 0) LineCoset :=
  @MulAction.quotient (Model 0) (Model 0) (modelGroup 0) inferInstance
    (Monoid.toMulAction _) FullRee.second (MulAction.left_quotientAction _)

theorem pointOnLine_translate (g : Model 0) (p : PointCoset) (l : LineCoset) :
    pointOnLine (g • p) (g • l) ↔ pointOnLine p l := by
  change (false ≠ true ∧ CosetGeometry.Incident family
    (g • pointVertex p) (g • lineVertex l)) ↔ _
  rw [CosetGeometry.incident_smul_iff]
  rfl

def linePointsEquiv (l : LineCoset) :
    {p : PointCoset // pointOnLine p l} ≃ (graph family).neighborSet (lineVertex l) :=
  Equiv.ofBijective (fun p => ⟨pointVertex p.val, p.property.symm⟩) (by
    constructor
    · intro p q he
      exact Subtype.ext (pointVertex_injective (congrArg Subtype.val he))
    · rintro ⟨⟨b,q⟩,h⟩
      cases b
      · exact ⟨⟨q,h.symm⟩,rfl⟩
      · exact (h.1 rfl).elim)

theorem card_line_points (l : LineCoset) :
    Nat.card {p : PointCoset // pointOnLine p l} = 3 :=
  (Nat.card_congr (linePointsEquiv l)).trans (card_neighbors (lineVertex l))

private theorem generator_r8_mem_second : presentationMap (parrottGenerator .r8) ∈ FullRee.second := by
  change FullRee.atlasEmbedding (parrottFiniteImageEquiv (parrottGenerator .r8)) ∈ _
  rw [parrottFiniteImageEquiv_generator]
  exact FullRee.atlas_second_map_le ⟨_, reflection_mem_second, rfl⟩

private theorem generator_s8_mem_second : presentationMap (parrottGenerator .s8) ∈ FullRee.second := by
  change FullRee.atlasEmbedding (parrottFiniteImageEquiv (parrottGenerator .s8)) ∈ _
  rw [parrottFiniteImageEquiv_generator]
  apply FullRee.atlas_second_map_le
  refine ⟨_, sylow_le_second ?_, rfl⟩
  rw [S, atlas1600SylowTwoSubgroup_eq]
  exact subset_closure (by simp)

private theorem line_base_fixed (g : Model 0) (hg : g ∈ FullRee.second) :
    (g • (((1 : Model 0) : LineCoset))) = ((1 : Model 0) : LineCoset) := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  apply QuotientGroup.eq.mpr
  simpa using FullRee.second.inv_mem hg

theorem seed_zero : pointOnLine (pointEquiv 0) ((1 : Model 0) : LineCoset) := by
  rw [pointEquiv_zero]
  exact ⟨by decide, ⟨1,rfl,rfl⟩⟩

theorem seed_one : pointOnLine (pointEquiv 1) ((1 : Model 0) : LineCoset) := by
  have he : Tits.R1Certificate.table 0 (.r8,true) = 1 := by decide +kernel
  have hh := (pointOnLine_translate (presentationMap (parrottGenerator .r8))⁻¹
    (pointEquiv 0) ((1 : Model 0) : LineCoset)).mpr seed_zero
  rw [line_base_fixed _ (FullRee.second.inv_mem generator_r8_mem_second),
    ← pointEquiv_step, he] at hh
  exact hh

theorem seed_three : pointOnLine (pointEquiv 3) ((1 : Model 0) : LineCoset) := by
  have he : Tits.R1Certificate.table 1 (.s8,true) = 3 := by decide +kernel
  have hh := (pointOnLine_translate (presentationMap (parrottGenerator .s8))⁻¹
    (pointEquiv 1) ((1 : Model 0) : LineCoset)).mpr seed_one
  rw [line_base_fixed _ (FullRee.second.inv_mem generator_s8_mem_second),
    ← pointEquiv_step, he] at hh
  exact hh

theorem seed_incidence (p : Fin 1755) :
    pointOnLine (pointEquiv p) ((1 : Model 0) : LineCoset) ↔ p = 0 ∨ p = 1 ∨ p = 3 := by
  classical
  let f : Fin 3 → {q : PointCoset // pointOnLine q ((1 : Model 0) : LineCoset)} :=
    fun i => ⟨pointEquiv (![0,1,3] i), by
      fin_cases i
      · exact seed_zero
      · exact seed_one
      · exact seed_three⟩
  have hf : Function.Injective f := by
    intro i j he
    have hh := pointEquiv.injective (congrArg Subtype.val he)
    change ![0,1,3] i = ![0,1,3] j at hh
    fin_cases i <;> fin_cases j <;> simp_all
  have hfs := hf.bijective_of_nat_card_le (by rw [Nat.card_fin, card_line_points])
  constructor
  · intro hp
    obtain ⟨i,hi⟩ := hfs.2 ⟨pointEquiv p,hp⟩
    have hh := pointEquiv.injective (congrArg Subtype.val hi)
    change ![0,1,3] i = p at hh
    fin_cases i
    · exact Or.inl hh.symm
    · exact Or.inr (Or.inl hh.symm)
    · exact Or.inr (Or.inr hh.symm)
  · rintro (rfl | rfl | rfl)
    · exact seed_zero
    · exact seed_one
    · exact seed_three
end ReeF4.Octagon.Binary.Automorphisms.FiniteBridge
