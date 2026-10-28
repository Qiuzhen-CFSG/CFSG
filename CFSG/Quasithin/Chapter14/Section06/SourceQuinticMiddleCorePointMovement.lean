module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCoreCenter

/-!
# The original middle core moves the marked central point

The cubic endpoint normalizes its full two-core and has trivial center.
Consequently its induced automorphisms cannot all fix the original Sylow
central involution. This is the source obstruction used to test the marked
characteristic cores of the possible quintic complement extensions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- An actual automorphism of the original middle core moves each nonidentity
point of the original Sylow central line. -/
theorem source_quintic_middle_core_point_moved
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (z : G) (hz : z ∈ centralInvolutions T) (hz1 : z ≠ 1) :
    let QX := (sourceResidual M Mc ⊔ (T : Subgroup G)).pCoreIn 2
    ∃ hzQX : z ∈ QX, ∃ α : MulAut QX, (α ⟨z,hzQX⟩ : G) ≠ z := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  let QX := X.pCoreIn 2
  have hUQ : U ≤ H.pCoreIn 2 := (source_quintic_full_core_layers
    hG T hempty hM hu hmany hcard e H hH hi).1.ge.trans (commutator_le_self _)
  let : IsElementaryAbelian 2 U :=
    (Section02.SolvableAmalgam.source_index_five_closure_structure
      hG T hempty hM hu hmany hcard e H hH.1 hi).1
  have hZU : centralInvolutions T ≤ U :=
    (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  have hUC : U ≤ H ⊓ centralizer (U : Set G) :=
    le_inf (hUQ.trans (pCoreIn_le 2 H)) (le_centralizer U)
  have hzQX : z ∈ QX := (source_quintic_full_kernel_middle_placement
    hG T hempty hM hu hmany hcard e H hH hi).1 (hUC (hZU hz))
  refine ⟨hzQX,?_⟩
  by_contra hn
  push Not at hn
  have hXQX : X ≤ normalizer (QX : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hzcenter : (⟨z,(pCoreIn_le 2 X) hzQX⟩ : X) ∈ center X := by
    apply mem_center_iff.mpr
    intro x
    have hh := hn (QX.normalizerMonoidHom ⟨x,hXQX x.property⟩)
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp hh)
  have hbot : center X = ⊥ := (source_quintic_cubic_natural_center
    hG T hempty hM hu hmany hcard e H hH hi).1
  have he : (⟨z,(pCoreIn_le 2 X) hzQX⟩ : X) = 1 := mem_bot.mp (hbot ▸ hzcenter)
  exact hz1 (congrArg (fun x : X => (x : G)) he)

end CFSG.Quasithin.Chapter14.Section06
