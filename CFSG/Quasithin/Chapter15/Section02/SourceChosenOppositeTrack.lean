module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenOppositeTrack.Geometry
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenOppositeTrack.Action
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenOppositeTrack.Setup

/-!
# The noncommuting opposite-span witness in Section 15.2

For the original chosen V and H, put U = ⟨Vᴴ⟩. We construct g in the ambient
group with U ≤ Hᵍ, Uᵍ ≤ H and [V,Vᵍ] nontrivial. The only retained earlier
source conclusion is the literal equality M ∩ H = T from 15.2.8.

Use the genuine pair N_M(C_T(V)), H in its generated subgroup. The first
vertex satisfies F.7.6 by 15.1.9(6), and its faithful centralizer-quotient action
embeds equivariantly in the original M-action on V. Thus the track is odd.
The source core containment makes its length at least three, giving opposite
span containment. Since N_G(V) = M and M ∩ H = T, the second-vertex
centralizer of U lies in its first-ball kernel. Criticality supplies a
noncommuting conjugate seed. Transport through the generated subgroup's
inclusion preserves V, H, U, and the nonzero commutator.

This discharges `htrack` in `source_chosen_pair_of_opposite_spans`; its chief
action and corank arguments remain with the separate critical-track assembly.
No later weak-closure, core-escape or displacement conclusion is used here.

Source: Aschbacher--Smith, Section 15.2, printed pp.1119--1120;
Notation 15.2.9, p.1110; 15.1.9, pp.1088--1089; F.7.1--11, pp.311--314.
-/

public section

open scoped IsMulCommutative
open Subgroup Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 ChapterD ChapterD.UniqueFactor ChosenOppositeTrack
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem map_conj_ambient {K : Type*} [Group K]
    (f : K →* G) (A : Subgroup K) (g : K) :
    (A.map (MulAut.conj g).toMonoidHom).map f =
      (A.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp

/-- The actual opposite-span witness for the chosen source module. The
intersection premise is precisely the preceding conclusion 15.2.8. -/
theorem source_chosen_opposite_spans
    (T : Sylow 2 G) {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMH : M ⊓ H = (T : Subgroup G)) :
    ∃ g : G,
      conjugateSpan H V ≤ H.map (MulAut.conj g).toMonoidHom ∧
      (conjugateSpan H V).map (MulAut.conj g).toMonoidHom ≤ H ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
  let := h.prepared.elementary
  let N := chosenNormalizer T M V
  let L := N ⊔ H
  let F : Bool → Subgroup L := fun i => if i then H.subgroupOf L else N.subgroupOf L
  obtain ⟨D, hne, hseed, hfirst, hcore⟩ := normalizer_source_setup T h hg
  have hH : (F true).map L.subtype = H :=
    map_subgroupOf_eq_of_le le_sup_right
  have hspan : (conjugateSpan (F true) D.seed).map L.subtype = conjugateSpan H V := by
    rw [conjugateSpan_eq, map_conjugateSpanBy, hseed, hH, conjugateSpan_eq]
  have hnot := not_ff_of_ambient_image D L.subtype L.subtype_injective
    M V h.prepared.normalized hfirst hseed h.not_ff
  have hnorm : normalizer (V : Set G) ≤ M :=
    h.maximal.1.1.2
      ⟨V, h.prepared.nontrivial, IsElementaryAbelian.isPGroup 2 V, rfl⟩
      h.prepared.normalized
  have hc : F true ⊓ centralizer (D.seed : Set L) ≤ F false := by
    intro x hx
    have hxC : (x : G) ∈ centralizer (V : Set G) := by
      rw [← hseed]
      rintro y ⟨z, hz, rfl⟩
      exact congrArg L.subtype (hx.2 z hz)
    have hxM := hnorm (_root_.centralizer_le_normalizer _ hxC)
    have hxT : (x : G) ∈ (T : Subgroup G) := hMH ▸ ⟨hxM, hx.1⟩
    exact sylow_le_chosenNormalizer T h.maximal.1.2 h.prepared.normalized hxT
  obtain ⟨g, hforward, hbackward, hmove⟩ := opposite_spans_of_not_ff D hne hcore hnot hc
  refine ⟨(g : G), ?_, ?_, ?_⟩
  · have hm := map_mono (f := L.subtype) hforward
    rwa [hspan, map_conj_ambient, hH] at hm
  · have hm := map_mono (f := L.subtype) hbackward
    rwa [map_conj_ambient, hspan, hH] at hm
  · intro he
    apply hmove
    apply (map_eq_bot_iff_of_injective _ L.subtype_injective).mp
    rw [map_commutator, map_conj_ambient, hseed]
    exact he

end CFSG.Quasithin.Chapter15.Section02
