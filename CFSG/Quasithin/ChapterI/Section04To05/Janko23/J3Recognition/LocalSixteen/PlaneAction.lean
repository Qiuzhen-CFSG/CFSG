module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.NormalizerOrder
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.PlaneCentralizer
/-!
# The faithful automizer of the actual sixteen-group

A plane centralizer fixes z and normalizes the plane, so the characteristic
core intersection puts it inside the actual root normalizer. The marked
model calculation then identifies it with the plane itself. Consequently
the kernel of the literal normalizer action is exactly the relative plane;
the full normalizer order 2880 gives action-image order 180.

Source: Aschbacher, *Sporadic Groups* (1994), 46.14(5a), p.258.
This constructs the automizer and its kernel. Identifying that action as
GL₂(4) on its natural module, and splitting the full extension, remain
separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.HyperbolicRecognition
namespace CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen
open Matrix.PSL3Four
variable {G : Type*} [Group G] [Finite G] {D : Seed G}
namespace ReturningPair
variable (P : ReturningPair D)

/-- Each actual elementary root plane is self-centralizing in the whole source group. -/
theorem plane_centralizer (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 16) (hAR : A ≤ P.R) : centralizer (A : Set G) = A := by
  obtain ⟨d,f,hf⟩ := Geometry.Normalizer.exists_identification P
  have hEA : P.E ≤ A := by
    rcases (P.elementary_sixteen_iff d A hAR).mp ⟨inferInstance,hA⟩ with rfl | rfl
    · rw [←P.planes_inf d]; exact inf_le_left
    · rw [←P.planes_inf d]; exact inf_le_right
  apply le_antisymm _ (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  intro c hc
  have hcN : c ∈ normalizer (P.R : Set G) :=
    P.plane_point_stabilizer_le_root_normalizer A hAR hEA
      ⟨Subgroup.centralizer_le_normalizer _ hc,mem_centralizer_singleton_iff.mpr (hc D.z (hEA P.z_mem_E)).symm⟩
  let n : normalizer (P.R : Set G) := ⟨c,hcN⟩
  have step (V : Subgroup RootNormalizerModel.Root)
      (hV : A = (V.map d.symm.toMonoidHom).map P.R.subtype)
      (hfix : ∀ b : RootNormalizerModel.Model,
        (∀ q ∈ V, b * SemidirectProduct.inl q = SemidirectProduct.inl q * b) →
        b.right = 1 ∧ b.left ∈ V) : c ∈ A := by
    have hmem (q : RootNormalizerModel.Root) (hq : q ∈ V) : (d.symm q : G) ∈ A := by
      rw [hV]
      exact mem_map_of_mem P.R.subtype (mem_map_of_mem d.symm.toMonoidHom hq)
    obtain ⟨hr,hv⟩ := hfix (f n) (by
      intro q hq
      have hmark := hf (d.symm q)
      rw [d.apply_symm_apply] at hmark
      rw [←hmark,←map_mul,←map_mul]
      apply congrArg f
      exact Subtype.ext (hc (d.symm q) (hmem q hq)).symm)
    have he : n = inclusion le_normalizer (d.symm (f n).left) := by
      apply f.injective
      rw [hf,d.apply_symm_apply]
      exact SemidirectProduct.ext rfl hr
    have he' : c = (d.symm (f n).left : G) := congrArg Subtype.val he
    rw [he']
    exact hmem _ hv
  rcases (P.elementary_sixteen_iff d A hAR).mp ⟨inferInstance,hA⟩ with h | h
  · exact step rootPlane₁ h RootNormalizerModel.centralizes_first_plane
  · exact step rootPlane₂ h RootNormalizerModel.centralizes_second_plane

/-- The kernel is the literal relative plane, rather than a group-family label. -/
theorem plane_normalizer_action_kernel (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    A.normalizerMonoidHom.ker = A.subgroupOf (normalizer (A : Set G)) := by
  rw [normalizerMonoidHom_ker,P.plane_centralizer A hA hAR]

/-- The actual automizer of the plane has order 180. -/
theorem plane_normalizer_action_card (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    Nat.card A.normalizerMonoidHom.range = 180 := by
  have hk : Nat.card A.normalizerMonoidHom.ker = 16 := by
    rw [P.plane_normalizer_action_kernel A hA hAR,
      Nat.card_congr (subgroupOfEquivOfLe (le_normalizer : A ≤ normalizer (A : Set G))).toEquiv,hA]
  have hh := A.normalizerMonoidHom.ker.card_mul_index
  rw [hk,index_ker,P.plane_normalizer_card hclass A hA hAR] at hh
  omega
end ReturningPair
end CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen
