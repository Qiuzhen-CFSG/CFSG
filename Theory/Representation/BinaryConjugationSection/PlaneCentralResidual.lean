module
public import Theory.Representation.BinaryParabolicExteriorSquare.ComplementRecognition
public import Theory.Representation.BinaryConjugationSection.SubspacePreimages
public import Theory.LinearAlgebra.BinaryFlagCoordinates
import Mathlib.Tactic.FinCases

/-!
# The matrix image of a central plane residual

A two-perfect subgroup centralizing the marked plane maps into its
complementary-plane residual. If the original subgroup is not a two-group,
the image through a two-group kernel is nontrivial. The literal plane
normalizer then supplies normality in the model residual, forcing equality.
Both the coordinate map and the original relative normalizer are retained.

Source application: Aschbacher--Smith, The Classification of Quasithin
Groups, 13.8.31, printed p.965, with Notation 13.2.1 on p.877.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups
namespace Representation.BinaryConjugationSection
open BinaryParabolicExteriorSquare PlaneSpan
open BinaryLinear.FlagCoordinates
variable {G : Type*} [Group G]

/-- A normal two-perfect plane centralizer with nontrivial odd image is the
literal complementary-plane group, through the original matrix quotient. -/
theorem complement_image_of_plane_centralizer
    (H D UH V1 V3 QH : Subgroup G) (hDH : D ≤ H)
    (hp : IsPPerfect 2 D) (hnot : ¬ IsPGroup 2 D)
    (hcentral : D ≤ centralizer (V3 : Set G))
    (hn : H ⊓ normalizer (V3 : Set G) ≤ normalizer (D : Set G))
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hQH : IsPGroup 2 QH) (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (h13 : V1 ≤ V3) (h3U : V3 ≤ UH) (hplane : d.imageSpace V3 = plane) :
    (D.subgroupOf H).map π = PlaneRadical.complementLocal := by
  let M := (D.subgroupOf H).map π
  have hpD : IsPPerfect 2 (D.subgroupOf H) := hp.of_surjective
    (subgroupOfEquivOfLe hDH).symm.toMonoidHom (subgroupOfEquivOfLe hDH).symm.surjective
  have hpM : IsPPerfect 2 M := hpD.of_surjective (π.subgroupMap (D.subgroupOf H))
    (π.subgroupMap_surjective _)
  have hne : M ≠ ⊥ := by
    intro he
    have hl : D.subgroupOf H ≤ QH.subgroupOf H := by
      rw [←hker]
      exact (Subgroup.map_eq_bot_iff _).mp he
    exact hnot (hQH.to_le (fun x hx => hl (show (⟨x,hDH hx⟩:H) ∈ D.subgroupOf H from hx)))
  have hfixed (g : M) (w : Fin 4 → ZMod 2) (hw : w ∈ plane) :
      Matrix.mulVec g.val.val w = w := by
    obtain ⟨a,ha,he⟩ := g.property
    have hw' : w ∈ d.imageSpace V3 := hplane.symm ▸ hw
    obtain ⟨x,hx,hxw⟩ := (d.mem_imageSpace_iff V3 w).mp hw'
    have hconj : (⟨(a:G)*x*(a:G)⁻¹,
        (mem_normalizer_iff.mp (d.normalized a.property) x).mp x.property⟩ : UH) = x := by
      apply Subtype.ext
      change (a:G)*(x:G)*(a:G)⁻¹ = x
      have hh : (x:G)*(a:G) = (a:G)*(x:G) := hcentral ha x hx
      rw [←hh,mul_inv_cancel_right]
    have hh := d.equivariant a x
    rw [hconj,hxw,hnatural,he] at hh
    exact hh.symm
  have hM : M ≤ PlaneRadical.complementLocal :=
    PlaneRadical.twoPerfect_le_complementLocal_of_columns M hpM
      (fun g i => by
        have hh := congrFun (hfixed g (Pi.single 0 1) first_mem_plane) i
        simpa [Matrix.mulVec_single] using hh)
      (fun g i => by
        have hh := congrFun (hfixed g (Pi.single 1 1) (by constructor <;> simp)) i
        simpa [Matrix.mulVec_single] using hh)
  have hnormal (a : SL(4,ZMod 2))
      (ha : ∀ w ∈ plane, Matrix.mulVec a.val w = w) : a ∈ normalizer (M : Set _) := by
    obtain ⟨b,rfl⟩ := honto a
    have hb : (b:G) ∈ normalizer (V3 : Set G) := by
      have he := d.subspacePreimage_imageSpace V3 h3U h13
      rw [hplane] at he
      rw [←he,d.mem_normalizer_subspacePreimage_iff]
      apply le_antisymm
      · rintro _ ⟨w,hw,rfl⟩
        rwa [hnatural,ha w hw]
      · intro w hw
        exact ⟨w,hw,(hnatural b w).trans (ha w hw)⟩
    apply le_normalizer_map π
    apply mem_map_of_mem π
    exact mem_normalizer_iff.mpr (fun x =>
      mem_normalizer_iff.mp (hn ⟨b.property,hb⟩) (x:G))
  have hMn : PlaneRadical.complementLocal ≤ normalizer (M : Set _) := by
    apply sup_le
    · rintro _ ⟨v,rfl⟩
      apply hnormal
      intro w hw
      rcases hw with ⟨h2,h3⟩
      change Matrix.mulVec (PlaneRadical.matrix v.toAdd) w = w
      ext i
      fin_cases i <;>
        simp [PlaneRadical.matrix,
          Matrix.mulVec,dotProduct,Fin.sum_univ_succ,h2,h3]
    · apply zpowers_le.mpr
      apply hnormal
      intro w hw
      rcases hw with ⟨h2,h3⟩
      ext i
      fin_cases i <;>
        simp [complementElement,complementCubic,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,h2,h3]
  exact PlaneRadical.eq_complementLocal_of_normal_twoPerfect M hM hMn hpM hne

end Representation.BinaryConjugationSection
