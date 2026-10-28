module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Checks
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Certificate

/-!
# The elementary product bound in the native Mathieu action

The certified vertex enumeration embeds an arbitrary elementary subgroup as a
commuting clique of exactly the same order. Its actual fixed masks satisfy
every checked actor equation. The exhaustive tree therefore bounds the product
by 1024, with no normality or maximality assumption on the subgroup.

This is the native finite input for Kleidman--Wilson (1988), Lemma 1.1.2(i).
-/
@[expose] public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
open Janko4.LocalStructure.SylowCore.FiniteBoundCertificate
open Janko4.LocalStructure.SylowCore.FiniteBoundCertificate.NormalWeights
open Janko4.LocalStructure.SylowCore
open Janko4.Simplicity.Max1Fusion.QuotientInvolutions
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] vertexIndex point row masks neighbors certificate check

def native (v : Fin 192) : sylowCandidate := element (vertexIndex v)

theorem native_injective : Function.Injective native :=
  element_injective.comp vertexIndex_injective

theorem vertex_of_mem (B : Subgroup sylowCandidate) [IsElementaryAbelian 2 B]
    (g : sylowCandidate) (hg : g ∈ B) : ∃ v, native v = g := by
  obtain ⟨i,hi⟩ := element_bijective.surjective g
  have hm : element i ∈ B := hi.symm ▸ hg
  have hs : SquareTest i := fun p => square_point B i hm (p.castLE (by decide))
  exact ⟨vertexCode i, (congrArg element (vertex_coverage i hs)).trans hi⟩

theorem native_compatible (B : Subgroup sylowCandidate) [IsElementaryAbelian 2 B]
    (v w : Fin 192) (hv : native v ∈ B) (hw : native w ∈ B) :
    compatible v w = true := by
  apply compatible_spec v w
  intro p
  simp only [point_spec]
  exact commute_point B (vertexIndex v) (vertexIndex w) hv hw (p.castLE (by decide))

theorem native_fixes (v : Fin 192) (m : Fin 2048)
    (hm : starMask (native v).val m.val = m.val) : fixedBit v m = true := by
  apply fixedBit_spec
  apply beq_iff_eq.mpr
  rw [row_spec]
  exact hm

theorem elementary_fixed_bound
    (B : Subgroup sylowCandidate) [IsElementaryAbelian 2 B] (hne : B ≠ ⊥) :
    Nat.card B * Nat.card (FixedMasks B) ≤ 1024 := by
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
  rw [← hsc, ← hac]
  apply check_sound neighbors masks certificate _ _ certificate_checked s a
    (fun v _ => List.mem_finRange v) (fun m _ => by
      simpa only [Nat.testBit_two_pow_sub_one, decide_eq_true_eq] using m.isLt) hnon hp
  · intro v hv w hw
    exact native_compatible B v w ((hs v).mp hv) ((hs w).mp hw)
  · intro v hv m hm
    exact native_fixes v m ((ha m).mp hm ⟨native v, (hs v).mp hv⟩)

end Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
