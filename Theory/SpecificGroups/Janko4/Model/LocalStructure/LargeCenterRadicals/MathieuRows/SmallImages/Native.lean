module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.SmallImages.Certificate
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.SmallImages.Octads

/-!
# Common-octad placement from a large native fixed space

The checked branching tree places every elementary image of order at least
four with at least 64 fixed binary masks in a literal pointwise octad kernel.
The actor and mask bijections preserve their exact cardinalities. This is
the missing local placement input for radical saturation, rather than an
assumed radical table or a statement about a contained normalizer.
Source: An--O'Brien--Wilson (2003), §4 and Table 1, pp.122,124.
-/
public noncomputable section
namespace Janko4.LocalStructure.LargeCenterRadicals.MathieuRows.SmallImages
open ElementaryNormalizerCover.ElementaryBound
open SylowCore SylowCore.FiniteBoundCertificate
open Simplicity.Max1Fusion.QuotientInvolutions
open Cardinality.QuotientCount.Image
open Sporadic.Mathieu M24LocalGeometry MathieuCode
attribute [local irreducible] vertexIndex point ElementaryNormalizerCover.ElementaryBound.row masks neighbors certificate check

/-- A noncyclic elementary native image with large fixed space fixes an octad pointwise. -/
theorem elementary_large_fixed_octad (B : Subgroup sylowCandidate)
    [IsElementaryAbelian 2 B] (hcard : 4 ≤ Nat.card B)
    (hfixed : 64 ≤ Nat.card (FixedMasks B)) :
    ∃ O : Octad, B.map LinearFive.Geometry.SharpImages.markedSylow ≤ octadPointwiseKernel O := by
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
  have hd := check_sound keep neighbors masks certificate _ _ certificate_checked s a
    (fun v _ => List.mem_finRange v) (fun m _ => by
      simpa only [Nat.testBit_two_pow_sub_one, decide_eq_true_eq] using m.isLt)
    (fun v hv w hw => native_compatible B v w ((hs v).mp hv) ((hs w).mp hw))
    (fun v hv m hm => native_fixes v m ((ha m).mp hm ⟨native v, (hs v).mp hv⟩))
  have hn : ¬ s.card < 4 := by rw [hsc]; omega
  have hf : ¬ a.card < 64 := by rw [hac]; omega
  obtain ⟨i,hi⟩ := (hd.resolve_left hn).resolve_left hf
  refine ⟨octad i, ?_⟩
  rintro y ⟨g,hg,rfl⟩
  obtain ⟨v,rfl⟩ := vertex_of_mem B g hg
  exact native_mem_octad_kernel i v (hi v ((hs v).mpr hg))

end Janko4.LocalStructure.LargeCenterRadicals.MathieuRows.SmallImages
