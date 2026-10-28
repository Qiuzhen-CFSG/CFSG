module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal

/-!
# The ordinary vector stabilizer inside the extended point stabilizer

Entrywise conjugation preserves the subgroup fixing the first vector.
Its original normality in the point parabolic therefore persists in the
semidirect extension. The inclusion and its image retain the literal
semidirect coordinates; this is the normal subgroup used in the binary
endpoint calculation for Aschbacher–Smith F.4.36.
-/

@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter
open UnitaryFourFlag UnitaryFourPointLocal Subgroup
variable (F : Type*) [Field F] [Finite F]
  (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "J" => form F σ hσ
local notation "N" => localSU F J

omit [Finite F] in
/-- The marked field automorphism preserves the original vector stabilizer. -/
theorem matrixAut_mem_local (a : SU F J) :
    matrixAut F σ hσ a ∈ N ↔ a ∈ N := by
  simp [mem_localSU, matrixAut_apply]

/-- Embed the ordinary vector stabilizer in the actual extended point group. -/
def pointVectorEmbedding : N →* point F σ hσ where
  toFun a := ⟨SemidirectProduct.inl a.val, localSU_le_pointParabolicSU F J a.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a.val b.val)

theorem pointVectorEmbedding_injective : Function.Injective (pointVectorEmbedding F σ hσ) := by
  intro a b hab
  exact Subtype.ext (congrArg (fun x : point F σ hσ => x.val.left) hab)

/-- The same ordinary vector stabilizer as a subgroup of the extended point group. -/
def pointVector : Subgroup (point F σ hσ) := (pointVectorEmbedding F σ hσ).range

instance pointVector_normal : (pointVector F σ hσ).Normal := by
  constructor
  intro x hx g
  obtain ⟨a,rfl⟩ := hx
  have ha : action F σ hσ g.val.right a.val ∈ N := by
    rcases c2_cases g.val.right with hg | hg
    · simpa only [hg,map_one,MulAut.one_apply] using a.property
    · rw [hg, action_generator]
      exact (matrixAut_mem_local F σ hσ a.val).mpr a.property
  have hg : g.val.left ∈ pointParabolicSU F J := g.property
  have hnormal := localSU_normal F J
  have hconj := hnormal.conj_mem
    (⟨action F σ hσ g.val.right a.val, localSU_le_pointParabolicSU F J ha⟩ : pointParabolicSU F J)
    ha (⟨g.val.left,hg⟩ : pointParabolicSU F J)
  refine ⟨⟨g.val.left * action F σ hσ g.val.right a.val * g.val.left⁻¹,hconj⟩,?_⟩
  apply Subtype.ext
  change SemidirectProduct.inl (g.val.left * action F σ hσ g.val.right a.val * g.val.left⁻¹) =
    g.val * SemidirectProduct.inl a.val * g.val⁻¹
  rw [map_mul,map_mul,map_inv,SemidirectProduct.inl_aut]
  conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right g.val]
  simp only [map_inv]
  group

/-- The inclusion identifies the original matrix local with its actual image. -/
def pointVectorEquiv : N ≃* pointVector F σ hσ :=
  MonoidHom.ofInjective (pointVectorEmbedding_injective F σ hσ)

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter
