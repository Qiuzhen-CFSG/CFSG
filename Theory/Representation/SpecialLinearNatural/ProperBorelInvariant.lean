module
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Natural
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.BinaryOffender.Defs
/-!
# Proper Borel-invariant subgroups of the natural plane

A proper additive subgroup of the natural plane invariant under a Borel
lies in its Sylow fixed line. In standard coordinates the upper root and
diagonal torus would otherwise generate both coordinates. Sylow conjugacy
and equivariant coordinates transport this fact to the specified action.

The literal residual-section consumer is the natural alternative in DGS,
*Groups and Graphs* (1985), 8.5, printed p.139.
-/

@[expose] public noncomputable section
open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F]
/-- A proper upper-Borel invariant additive subgroup lies in the first line. -/
theorem proper_borel_invariant_second_eq_zero
    (W : AddSubgroup (Fin 2 → F)) (hne : W ≠ ⊤)
    (hinv : ∀ g ∈ rankOneBorel F, ∀ v ∈ W, g.val *ᵥ v ∈ W)
    (v : Fin 2 → F) (hv : v ∈ W) : v 1 = 0 := by
  by_contra hv1
  have hW : W ≠ ⊥ := by
    intro he
    have hz : v = 0 := by simpa only [he,AddSubgroup.mem_bot] using hv
    exact hv1 (congrFun hz 1)
  apply hne
  apply top_unique
  intro w hw
  by_cases hw1 : w 1 = 0
  · have he : w = ![w 0,0] := by ext i; fin_cases i <;> simp [hw1]
    rw [he]
    exact firstLine_mem_of_borel_invariant W hW hinv (w 0)
  · let a := v 1 / w 1
    have ha : a ≠ 0 := div_ne_zero hv1 hw1
    let z := (diag2 a ha).val *ᵥ v
    have hz : z ∈ W := hinv _ (diag_mem_rankOneBorel a ha) v hv
    have hz1 : z 1 = w 1 := by
      dsimp [z]
      simp [diag2_coe',mulVec,dotProduct,Fin.sum_univ_two,a,hv1]
    have he : w = z + ![w 0-z 0,0] := by
      ext i
      fin_cases i <;> simp [hz1]
    rw [he]
    exact W.add_mem hz (firstLine_mem_of_borel_invariant W hW hinv _)
end Matrix.SpecialLinearGroup

namespace Representation.SpecialLinearTwo
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every proper invariant subgroup is fixed by the specified Sylow subgroup. -/
theorem proper_sylow_normalizer_invariant_fixed
    (P : Sylow 2 SL(2,F)) (W : AddSubgroup (Fin 2 → F)) (hne : W ≠ ⊤)
    (hn : ∀ g ∈ normalizer (P : Set SL(2,F)), ∀ v ∈ W, Matrix.SpecialLinearGroup.toLin' g v ∈ W) :
    ∀ v ∈ W, ∀ g ∈ (P : Subgroup SL(2,F)), Matrix.SpecialLinearGroup.toLin' g v = v := by
  obtain ⟨a,rfl⟩ := MulAction.exists_smul_eq SL(2,F) (upperUnipotentSylow F 2) P
  let Y := W.comap (Matrix.SpecialLinearGroup.toLin' a).toAddMonoidHom
  have hP (g : SL(2,F)) :
      g ∈ (a • upperUnipotentSylow F 2 : Sylow 2 SL(2,F)) ↔
        ∃ b ∈ upperUnipotent F, a * b * a⁻¹ = g := by
    change g ∈ ((a • upperUnipotentSylow F 2 : Sylow 2 SL(2,F)) : Subgroup _) ↔ _
    rw [Sylow.coe_subgroup_smul]
    rfl
  have hyn : ∀ g ∈ rankOneBorel F, ∀ v ∈ Y, g.val *ᵥ v ∈ Y := by
    intro g hg v hv
    have hng : a * g * a⁻¹ ∈ normalizer
        ((a • upperUnipotentSylow F 2 : Sylow 2 SL(2,F)) : Set SL(2,F)) := by
      have hm := mem_map_of_mem (MulAut.conj a).toMonoidHom hg
      rw [map_equiv_normalizer_eq] at hm
      exact hm
    have he := hn _ hng (Matrix.SpecialLinearGroup.toLin' a v) hv
    change Matrix.SpecialLinearGroup.toLin' a (Matrix.SpecialLinearGroup.toLin' g v) ∈ W
    simpa using he
  have hyne : Y ≠ ⊤ := by
    intro hy
    apply hne
    apply top_unique
    intro v _
    have hv : Matrix.SpecialLinearGroup.toLin' a⁻¹ v ∈ Y := hy.ge (AddSubgroup.mem_top _)
    change Matrix.SpecialLinearGroup.toLin' a (Matrix.SpecialLinearGroup.toLin' a⁻¹ v) ∈ W at hv
    simpa using hv
  intro v hv g hg
  obtain ⟨b,hb,rfl⟩ := (hP g).mp hg
  have hvY : Matrix.SpecialLinearGroup.toLin' a⁻¹ v ∈ Y := by change Matrix.SpecialLinearGroup.toLin' a (Matrix.SpecialLinearGroup.toLin' a⁻¹ v) ∈ W; simpa using hv
  have hz := proper_borel_invariant_second_eq_zero Y hyne hyn _ hvY
  have hz' : (Matrix.SpecialLinearGroup.toLin' a).symm v 1 = 0 := by simpa using hz
  have he : Matrix.SpecialLinearGroup.toLin' b (Matrix.SpecialLinearGroup.toLin' a⁻¹ v) = Matrix.SpecialLinearGroup.toLin' a⁻¹ v := by
    obtain ⟨t,rfl⟩ := (mem_upperUnipotent F b).mp hb
    funext i
    fin_cases i <;>
      simp [Matrix.SpecialLinearGroup.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two,transvection_coe,hz']
  simpa using congrArg (Matrix.SpecialLinearGroup.toLin' a) he

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Algebra (ZMod 2) F]

/-- Equivariant natural coordinates retain the original invariant subspace. -/
theorem proper_natural_sylow_normalizer_invariant_fixed
    (ρ : Representation (ZMod 2) SL(2,F) V)
    (E : V ≃ₗ[ZMod 2] (Fin 2 → F))
    (hE : ∀ g v, E (ρ g v) = Matrix.mulVec g.val (E v))
    (P : Sylow 2 SL(2,F)) (W : Submodule (ZMod 2) V) (hne : W ≠ ⊤)
    (hn : ∀ g ∈ normalizer (P : Set SL(2,F)), ∀ v ∈ W, ρ g v ∈ W) :
    W ≤ BinaryOffender.fixedSpace ρ P := by
  let Y := W.toAddSubgroup.map E.toAddMonoidHom
  have hyne : Y ≠ ⊤ := by
    intro he
    apply hne
    apply top_unique
    intro v _
    obtain ⟨w,hw,hew⟩ := show E v ∈ Y from he.ge (AddSubgroup.mem_top _)
    exact E.injective hew ▸ hw
  have hyn : ∀ g ∈ normalizer (P : Set SL(2,F)), ∀ v ∈ Y, Matrix.SpecialLinearGroup.toLin' g v ∈ Y := by
    intro g hg v hv
    obtain ⟨w,hw,rfl⟩ := hv
    exact ⟨ρ g w,hn g hg w hw,hE g w⟩
  intro v hv g
  apply E.injective
  change E (ρ g.val v) = E v
  rw [hE]
  exact proper_sylow_normalizer_invariant_fixed P Y hyne hyn (E v) ⟨v,hv,rfl⟩ g g.property
end Representation.SpecialLinearTwo
