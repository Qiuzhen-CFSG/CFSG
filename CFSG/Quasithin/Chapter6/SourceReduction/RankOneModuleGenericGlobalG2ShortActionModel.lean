module
public import Theory.AtlasPort.LinearGroups.G2.ShortRootProducts.CentralizerCore.Containment
public import Theory.AtlasPort.LinearGroups.G2.LongRootPlaneLift
public import Theory.AtlasPort.LinearGroups.G2.LieSpecialRadical

/-!
# The intrinsic plane in the G₂ short-root centralizer

The long parabolic radical has derived group exactly the A–B root plane.
The six-root multiplication law proves containment, and the C–D and C–F
commutators generate the two coordinates. Thus the plane is characteristic
in the local two-core and is preserved by every ambient normalizer of L.
The perfect affine block in the short-root centralizer acts nontrivially:
the E-root shear moves the B-root by the nonzero A-root.

The companion source application transports both facts through the actual
left comparison map. They supply the nonsolvable automizer obstruction in
F.4.42, without assuming full short-root centralizer containment.
Source: Aschbacher–Smith F.4.42, printed p.295 (`refs/quasithin.pdf`).
Coordinate formulas reuse the licensed ATLAS port; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open Atlas.G2.ShortRootProducts.CentralizerCore
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2ShortAction
variable {F : Type*} [Field F] [CharP F 2]

/-- The plane is the embedded derived group of the actual long radical. -/
theorem radical_commutator :
    ⁅radical₂ (F := F),radical₂ (F := F)⁆ = longRootLocal (F := F) := by
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro x hx y hy
    obtain ⟨t,ht,rfl⟩ := hx
    obtain ⟨u,hu,rfl⟩ := hy
    let v := unipotentProductParameters
      (unipotentProductParameters (unipotentProductParameters t u)
        (unipotentInverseParameters t)) (unipotentInverseParameters u)
    have h (i : Fin 6) (hi : i=2 ∨ i=3 ∨ i=4 ∨ i=5) : v i=0 := by
      rcases hi with rfl|rfl|rfl|rfl <;>
        simp [v,unipotentProductParameters,unipotentInverseParameters,ht,hu,
          CharTwo.two_eq_zero]
    refine ⟨Multiplicative.ofAdd (v 0,v 1),?_⟩
    rw [commutatorElement_def,unipotentProduct_inv,unipotentProduct_inv,
      unipotentProduct_mul,unipotentProduct_mul,unipotentProduct_mul]
    change longRootHom _ = unipotentProduct v
    simp [longRootHom,unipotentProduct,h 2 (Or.inl rfl),h 3 (Or.inr (Or.inl rfl)),
      h 4 (Or.inr (Or.inr (Or.inl rfl))),h 5 (Or.inr (Or.inr (Or.inr rfl)))]
  · have hr (a b c d e : F) : unipotentProduct ![a,b,c,d,0,e] ∈ radical₂ :=
      ⟨_,rfl,rfl⟩
    have hc (a : F) :
        ⁅unipotentProduct ![0,0,a,0,0,0],unipotentProduct ![0,0,0,1,0,0]⁆ = rootA a := by
      have hh := fiveRoot_commutator (F := F) ![0,0,a,0,0,0] ![0,0,0,1,0,0] rfl rfl
      simpa [CharTwo.neg_eq,CharTwo.ofNat_eq_mod] using hh
    have hf (a : F) :
        ⁅unipotentProduct ![0,0,a,0,0,0],unipotentProduct ![0,0,0,0,0,1]⁆ = rootB a := by
      have hb : rootB a = unipotentProduct ![0,a,0,0,0,0] := by simp [unipotentProduct]
      rw [hb,commutatorElement_def,unipotentProduct_inv,unipotentProduct_inv,
        unipotentProduct_mul,unipotentProduct_mul,unipotentProduct_mul]
      congr 1
      ext i
      fin_cases i <;> simp [unipotentProductParameters,unipotentInverseParameters,
        CharTwo.neg_eq,CharTwo.sub_eq_add,CharTwo.ofNat_eq_mod,CharTwo.add_self_eq_zero]
    rintro x ⟨p,rfl⟩
    apply mul_mem
    · rw [←hc]
      exact commutator_mem_commutator (hr _ _ _ _ _) (hr _ _ _ _ _)
    · rw [←hf]
      exact commutator_mem_commutator (hr _ _ _ _ _) (hr _ _ _ _ _)

/-- The perfect affine block does not centralize its natural root plane. -/
theorem block_moves_plane :
    ¬ residualBlock (F := F) ≤ centralizer (longRootLocal (F := F) : Set (Model F)) := by
  intro h
  have hE : rootE (1:F) ∈ residualBlock := by
    rw [←block_upper]
    exact mem_sup_right ⟨_,rfl⟩
  have hh := h hE (rootB 1) (rootB_mem_longRootLocal 1)
  have he : MulAut.conj (rootE (1:F)) (rootB 1) = rootB 1 :=
    mul_inv_eq_iff_eq_mul.mpr hh.symm
  rw [ShortRootProducts.rootE_conjugate_rootB,one_mul] at he
  have ha : rootA (1:F)=1 := mul_right_cancel (he.trans (one_mul _).symm)
  exact one_ne_zero (rootA_injective (ha.trans rootA_zero.symm))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2ShortAction
