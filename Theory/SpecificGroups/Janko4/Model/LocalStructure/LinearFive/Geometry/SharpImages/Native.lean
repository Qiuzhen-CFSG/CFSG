module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.SharpImages.Certificate
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.SharpImages.Octad
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.SharpImages.Proper
public import Theory.Mathieu.M24.ChapterHStabilizers.OctadAction
public import Theory.Representation.MathieuCodeRestriction.CodeLocal

/-!
# The sharp product bound in the actual Mathieu action

A nontrivial elementary subgroup whose order times its fixed-kernel order is
at least 1024 fixes the specified native octad pointwise. The same vertex and
mask injections used for the elementary bound carry the strict certificate
to the literal star Sylow subgroup and its marked Mathieu image.

Source application: Kleidman--Wilson (1988), Lemma 1.1.2(ii), p.485.
-/
@[expose] public section
namespace Janko4.LocalStructure.LinearFive.Geometry.SharpImages
open ElementaryNormalizerCover.ElementaryBound
open SylowCore SylowCore.FiniteBoundCertificate
open Simplicity.Max1Fusion.QuotientInvolutions
open Cardinality.QuotientCount.Image
open Sporadic.Mathieu M24LocalGeometry MathieuCode
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] vertexIndex point ElementaryNormalizerCover.ElementaryBound.row masks neighbors certificate check

/-- The actual Mathieu marking restricted to the fixed native Sylow candidate. -/
noncomputable def markedSylow : sylowCandidate →* M24 :=
  starGroupEquivM24.toMonoidHom.comp sylowCandidate.subtype

theorem elementary_fixed_bound_or_large_octad
    (B : Subgroup sylowCandidate) [IsElementaryAbelian 2 B] (hne : B ≠ ⊥) :
    Nat.card B * Nat.card (FixedMasks B) < 1024 ∨
      16 ≤ Nat.card B ∧ B.map markedSylow ≤ octadPointwiseKernel exceptionalOctad := by
  classical
  let s := Finset.univ.filter (fun v => native v ∈ B)
  have hs (v : Fin 192) : v ∈ s ↔ native v ∈ B := by simp [s]
  let f : s → B := fun v => ⟨native v.val, (hs v.val).mp v.property⟩
  have hfi : Function.Injective f := by
    intro v w hvw
    exact Subtype.ext (native_injective (congrArg Subtype.val hvw))
  have hfs : Function.Surjective f := by
    intro b
    obtain ⟨v, hv⟩ := vertex_of_mem B b.val b.property
    exact ⟨⟨v, (hs v).mpr (hv.symm ▸ b.property)⟩, Subtype.ext hv⟩
  have hsc : s.card = Nat.card B := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
      (Nat.card_congr (Equiv.ofBijective f ⟨hfi,hfs⟩))
  let a := Finset.univ.filter (fun m : Fin 2048 =>
    ∀ b : B, starMask b.val.val m.val = m.val)
  have ha (m : Fin 2048) : m ∈ a ↔ ∀ b : B, starMask b.val.val m.val = m.val := by simp [a]
  let e : a ≃ FixedMasks B :=
    { toFun := fun m => ⟨m.val, (ha m.val).mp m.property⟩
      invFun := fun m => ⟨m.val, (ha m.val).mpr m.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hac : a.card = Nat.card (FixedMasks B) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using Nat.card_congr e
  have hnon : 2 ≤ s.card := by
    rw [hsc]
    have hp := Nat.card_pos (α := B)
    have hn : Nat.card B ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
    omega
  have hp : ∃ d, s.card = 2 ^ d := by
    rw [hsc]
    exact (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
  have hd := check_sound keep neighbors masks certificate _ _ certificate_checked s a
    (fun v _ => List.mem_finRange v) (fun m _ => by
      simpa only [Nat.testBit_two_pow_sub_one, decide_eq_true_eq] using m.isLt) hnon hp
    (fun v hv w hw => native_compatible B v w ((hs v).mp hv) ((hs w).mp hw))
    (fun v hv m hm => native_fixes v m ((ha m).mp hm ⟨native v, (hs v).mp hv⟩))
  rcases hd with hd | hd
  · exact Or.inl (by simpa only [hsc, hac] using hd)
  · by_cases hlarge : 16 ≤ s.card
    · right
      refine ⟨by simpa only [hsc] using hlarge, ?_⟩
      rintro y ⟨g, hg, rfl⟩
      obtain ⟨v, rfl⟩ := vertex_of_mem B g hg
      exact native_mem_octad_kernel v (hd v ((hs v).mpr hg))
    · have hsize : s.card ≤ 8 := by
        obtain ⟨d,hdpow⟩ := hp
        have hdlt : d < 4 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
          (show 2 ^ d < 2 ^ 4 by omega)
        rw [hdpow]
        change 2 ^ d ≤ 2 ^ 3
        exact Nat.pow_le_pow_right (by decide) (by omega)
      have hh := Proper.check_sound neighbors masks Proper.certificate _ _
        Proper.certificate_checked s a
        (fun v hv => of_decide_eq_true (hd v hv))
        (fun m _ => by simpa only [Nat.testBit_two_pow_sub_one, decide_eq_true_eq] using m.isLt)
        hsize hnon hp
        (fun v hv w hw => native_compatible B v w ((hs v).mp hv) ((hs w).mp hw))
        (fun v hv m hm => native_fixes v m ((ha m).mp hm ⟨native v, (hs v).mp hv⟩))
      exact Or.inl (by simpa only [hsc, hac] using hh)

/-- The strict bound or the pointwise octad containment, without a size premise. -/
theorem elementary_fixed_bound_or_octad
    (B : Subgroup sylowCandidate) [IsElementaryAbelian 2 B] (hne : B ≠ ⊥) :
    Nat.card B * Nat.card (FixedMasks B) < 1024 ∨
      B.map markedSylow ≤ octadPointwiseKernel exceptionalOctad :=
  (elementary_fixed_bound_or_large_octad B hne).imp id And.right



/-- A sharp elementary product forces the actual quotient image into the octad kernel. -/
theorem elementary_large_image_octad
    (B : Subgroup sylowCandidate) [IsElementaryAbelian 2 B] (hne : B ≠ ⊥)
    (hlarge : 1024 ≤ Nat.card B * Nat.card (FixedMasks B)) :
    B.map markedSylow ≤ octadPointwiseKernel exceptionalOctad :=
  (elementary_fixed_bound_or_octad B hne).resolve_left (Nat.not_lt_of_ge hlarge)

/-- Sharpness forces the full actual pointwise kernel as image. -/
theorem elementary_large_image_eq_octad
    (B : Subgroup sylowCandidate) [IsElementaryAbelian 2 B] (hne : B ≠ ⊥)
    (hlarge : 1024 ≤ Nat.card B * Nat.card (FixedMasks B)) :
    B.map markedSylow = octadPointwiseKernel exceptionalOctad := by
  obtain ⟨hcard,hle⟩ := (elementary_fixed_bound_or_large_octad B hne).resolve_left
    (Nat.not_lt_of_ge hlarge)
  apply Subgroup.eq_of_le_of_card_ge hle
  have hi : Function.Injective markedSylow :=
    starGroupEquivM24.injective.comp sylowCandidate.subtype_injective
  rw [Subgroup.card_map_of_injective hi, ← octad_core_map_eq_pointwise,
    Subgroup.card_map_of_injective (octadStabilizer exceptionalOctad).subtype_injective,
    M24ChapterHStabilizers.OctadAction.core_card]
  exact hcard

end Janko4.LocalStructure.LinearFive.Geometry.SharpImages
