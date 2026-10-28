module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InvolutionClasses
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverInvolutions

/-!
# The two ambient involution-fusion inputs from the four-cover geometry

The central plane V₁=Z(L) and the marked highest-root plane V₂ put every
involution of L into V under an actual L-conjugator. Ambient fusion of the
representatives already in V then gives the v-or-z premise of the transfer
reduction. Distinct elements of V₁ need not be L-conjugate.

The other premise uses the source three-subgroup X, inverted by f, and
C_R(X)=1 with Z(L)≤R. These geometric facts prove the nontrivial center
action; the projective calculation and Klein four lifting then prove the
single class in the field coset. All conjugation and quotient maps are the
ones belonging to the supplied inclusion of L in I.

Source: Aschbacher--Smith, proof of 15.3.38, printed pp.1136--1137,
combined manuscript of 1 March 2004. These are the model inputs for the
source theorem's separate final assembly.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter
open Subgroup Matrix.PSL3Four
variable {G : Type*} [Group G]

/-- The root-plane geometry covers every involution using an actual L-conjugator. -/
theorem cover_involution_conjugate_into_planes
    (L V V₁ V₂ : Subgroup G) (c : FourCover L)
    (hV : V₁ ⊔ V₂ ≤ V) (hZ : (center L).map L.subtype = V₁)
    (g : PSL)
    (hroot : (Matrix.PSL3Even.UnipotentGeometry.projectiveCenter F).map
      (MulAut.conj g).toMonoidHom ≤ (V₂.subgroupOf L).map c.toMonoidHom)
    (x : G) (hxL : x ∈ L) (hx : orderOf x = 2) :
    ∃ b : L, (MulAut.conj (b : G)) x ∈ V := by
  have hZV : center L ≤ V.subgroupOf L := by
    intro z hz
    exact (le_sup_left.trans hV : V₁ ≤ V) (hZ ▸ mem_map_of_mem L.subtype hz)
  have hV₂V : V₂.subgroupOf L ≤ V.subgroupOf L := by
    intro z hz
    exact (le_sup_right.trans hV : V₂ ≤ V) hz
  obtain ⟨b, hb⟩ := InvolutionClasses.cover_conjugate_into c (V.subgroupOf L) hZV g
    (hroot.trans (map_mono hV₂V)) (⟨x,hxL⟩ : L) (by
      apply Subtype.ext
      change x ^ 2 = 1
      rw [← hx]
      exact pow_orderOf_eq_one x)
  exact ⟨b, hb⟩

/-- Only fusion of representatives already in the source V remains geometric. -/
theorem cover_involution_fusion
    (L V V₁ V₂ : Subgroup G) (c : FourCover L)
    (hV : V₁ ⊔ V₂ ≤ V) (hZ : (center L).map L.subtype = V₁)
    (g : PSL)
    (hroot : (Matrix.PSL3Even.UnipotentGeometry.projectiveCenter F).map
      (MulAut.conj g).toMonoidHom ≤ (V₂.subgroupOf L).map c.toMonoidHom)
    (v z : G)
    (hreps : ∀ y : G, y ∈ V → orderOf y = 2 → IsConj y v ∨ IsConj y z)
    (x : G) (hxL : x ∈ L) (hx : orderOf x = 2) :
    IsConj x v ∨ IsConj x z := by
  obtain ⟨b, hb⟩ := cover_involution_conjugate_into_planes L V V₁ V₂ c hV hZ g hroot x hxL hx
  have ho : orderOf ((MulAut.conj (b : G)) x) = 2 :=
    (orderOf_injective (MulAut.conj (b : G)).toMonoidHom (MulAut.conj (b : G)).injective x).trans hx
  have hc : IsConj x ((MulAut.conj (b : G)) x) := isConj_iff.mpr ⟨(b : G), rfl⟩
  exact (hreps _ hb ho).imp hc.trans hc.trans

/-- The source three-subgroup centralizer calculation supplies field-coset fusion
in G, through the original subgroup L and its projective-action quotient. -/
theorem cover_field_coset_fusion
    (I L : Subgroup G) (hLI : L ≤ I) [(L.subgroupOf I).Normal]
    (d : ExtendedCentralizer.Overgroup (L.subgroupOf I))
    (R X : Subgroup I) (hX : IsPGroup 3 X)
    (hZR : (center (L.subgroupOf I)).map (L.subgroupOf I).subtype ≤ R)
    (hfixed : R ⊓ centralizer (X : Set I) = ⊥)
    (f : I) (hf : f ^ 2 = 1)
    (hfield : IsConj pslFrobenius
      (ExtendedCentralizer.projectiveAction (L.subgroupOf I) d.cover f))
    (hinv : ∀ x : X, f * (x : I) * f⁻¹ = (x : I)⁻¹)
    (x : G) (hx : orderOf x = 2) (hxL : x * (f : G)⁻¹ ∈ L) :
    IsConj x (f : G) := by
  let q := ExtendedCentralizer.projectiveAction (L.subgroupOf I) d.cover
  let : IsKleinFour q.ker := InvolutionClasses.projectiveAction_kernel_isKleinFour d
  have hker : q.ker ≤ L.subgroupOf I := by
    rw [show q.ker = _ from d.projectiveAction_ker]
    exact map_subtype_le _
  have hfree : ((center (L.subgroupOf I)).map (L.subgroupOf I).subtype) ⊓
      centralizer (X : Set I) = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    exact hfixed.le ⟨hZR hz.1, hz.2⟩
  have hcenter := InvolutionClasses.field_moves_center_of_three_geometry
    d.cover X hX f hinv hfree
  exact field_coset_fusion_of_quotient I L hLI q hker f hf
    (InvolutionClasses.projectiveAction_moves_kernel d f hcenter)
    (InvolutionClasses.projectiveAction_field_fusion d.cover f hf hfield) x hx hxL

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter
