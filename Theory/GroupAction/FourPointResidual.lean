module
public import Theory.GroupAction.FourPerfectOrbit
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.InvolutionCentralizerControl
/-!
# A fixed point removes the two-perfect action on a four-group

A nontrivial two-perfect image in the automorphism group of an elementary
four-group is transitive on its three nonidentity elements. It therefore
cannot fix a nonidentity point. Applied to the actual normalizer action,
this identifies the two-residuals of the plane normalizer and centralizer
when the ambient actor centralizes a point of that plane.

Source: Aschbacher–Smith, 13.7.6(iii), printed p.939.
-/
@[expose] public section
namespace MulAction
/-- A two-perfect action fixing a nonidentity point of a four-group is trivial. -/
theorem four_action_eq_one_of_twoPerfect_fixed
    {A W : Type*} [Group A] [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hA : IsPPerfect 2 A) (hW : Nat.card W = 4)
    (f : A →* MulAut W) (x : W) (hx : x ≠ 1)
    (hfix : ∀ a, f a x = x) : f = 1 := by
  apply MonoidHom.ext
  intro a
  apply MulEquiv.ext
  intro w
  change f a w = w
  by_contra hmove
  have hw : w ≠ 1 := by rintro rfl; exact hmove (map_one _)
  obtain ⟨b,hb⟩ := four_orbit_of_twoPerfect hA hW f w hw ⟨a,hmove⟩ x hx
  have he : w = x := (f b).injective (hb.trans (hfix b).symm)
  exact hmove (he ▸ hfix a)
end MulAction
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
/-- The two-residual of a four-group normalizer centralizing a point is its centralizer residual. -/
theorem four_point_normalizer_residual_eq
    (M W P : Subgroup G) [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (hP : Nat.card P = 2) (hPW : P ≤ W)
    (hMC : M ≤ centralizer (P : Set G)) :
    (pResidual 2 (M ⊓ normalizer (W : Set G) : Subgroup G)).map
        (M ⊓ normalizer (W : Set G)).subtype =
      (pResidual 2 (M ⊓ centralizer (W : Set G) : Subgroup G)).map
        (M ⊓ centralizer (W : Set G)).subtype := by
  let N := M ⊓ normalizer (W : Set G)
  let C := M ⊓ centralizer (W : Set G)
  let R := (pResidual 2 N).map N.subtype
  have hRN : R ≤ N := map_subtype_le _
  have hRW : R ≤ normalizer (W : Set G) := hRN.trans inf_le_right
  let f := W.normalizerMonoidHom.comp (inclusion hRW)
  obtain ⟨x,hx,_⟩ := (Nat.card_eq_two_iff' (1 : P)).mp hP
  let w : W := ⟨x,hPW x.property⟩
  have hw : w ≠ 1 := by
    intro he
    have heG : (x : G) = 1 := congrArg (fun y : W => (y : G)) he
    exact hx (Subtype.ext heG)
  have hfix : ∀ a : R, f a w = w := by
    intro a
    apply Subtype.ext
    change (a : G) * (x : G) * (a : G)⁻¹ = x
    rw [← mem_centralizer_iff.mp (hMC (hRN a.property).1) x x.property,
      mul_inv_cancel_right]
  have hf := MulAction.four_action_eq_one_of_twoPerfect_fixed
    (isPPerfect_embedded_pResidual 2 N) hW f w hw hfix
  have hRC : R ≤ C := by
    intro r hr
    refine ⟨(hRN hr).1,?_⟩
    intro y hy
    have he := congrArg (fun k : R →* MulAut W => (k ⟨r,hr⟩ ⟨y,hy⟩ : G)) hf
    change r * y * r⁻¹ = y at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  apply le_antisymm
  · have hh := embedded_pResidual_mono 2 hRC
    rw [(pResidual_eq_top_iff 2 R).mpr (isPPerfect_embedded_pResidual 2 N),
      ← MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  · exact embedded_pResidual_mono 2
      (inf_le_inf_left M (centralizer_le_normalizer (W : Set G)))
end Subgroup
