module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallMoverRefinement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CentralOmegaDualCover
public import Theory.Representation.SymplecticFourOrthogonalCover.DualFixed

/-!
# The original small-mover fixed-layer bound

An element of X centralizing the small-mover join projects to a fixed vector
in the full residual-fixed quotient. The join has no invariant refinement,
so dual-cover fixedness puts that vector in the literal image of U. Lifting
through the exact coordinate kernel gives C_X(J) <= U D, with the full
central attachment retained and at the original nonbinary degree.

This proves MS93 (5.3), printed p.915, on the minimum characteristic
replacement. The selected paths and terminal exclusions remain subsequent
steps toward its distance-two witness.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- MS93 (5.3) for the whole X-layer of an actual replacement edge. -/
theorem Input.replacement_small_mover_X_centralizer
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    X d.radical a ⊓ centralizer
      (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F ^ 2) : Set (FreeAmalgam d.radical)) ≤
      U d.radical a ⊔ fixedCore d.radical a := by
  obtain ⟨E,hE,s,i,hi,hdual,hrange,hindex⟩ :=
    h.exists_replacement_centralOmegaDualCover d geometry hb ha
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F ^ 2)
  let A := (J.subgroupOf S).map s.quotient
  let f := (commutator (Sp E.Carrier)).subtype.comp s.quotient
  have hlarge : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hL : commutator (Sp E.Carrier) = ⊤ :=
    Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hlarge
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨x,hx⟩ := s.quotient_surjective ⟨g,hL ▸ mem_top g⟩
    exact ⟨x,congrArg Subtype.val hx⟩
  have hfker : f.ker = s.quotient.ker := by
    ext x
    change (s.quotient x).val = 1 ↔ s.quotient x = 1
    exact ⟨fun he => Subtype.ext he,fun he => congrArg Subtype.val he⟩
  have hidx (B : Subgroup S) :
      (centralizer (B : Set S)).relIndex ((U d.radical a).subgroupOf S) =
      2 ^ fixedCodim (restrictScalars (k := ZMod 2)
        (symplecticNatural (k := E.Carrier) 2)) (B.map f) := by
    rw [hindex B]
    congr 1
    let τ := restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)
    have ht : binaryNatural (K := E.Carrier) = τ.comp (commutator (Sp E.Carrier)).subtype := rfl
    rw [ht,fixedCodim,fixedSpace_comp_map,Subgroup.map_map]
    rfl
  have hn := h.replacement_small_mover_no_refinement d geometry hb ha hat E hE f hf
    (by rw [hfker]; exact s.quotient_kernel) hidx
  have hno : ¬ ∃ c : Natural (K := E.Carrier), ∀ x : A, ∀ v,
      refinement c (binaryNatural x.val v) = refinement c v := by
    rintro ⟨c,hc⟩
    apply hn
    refine ⟨c,?_⟩
    rintro ⟨_,⟨x,hx,rfl⟩⟩ v
    exact hc ⟨s.quotient x,mem_map_of_mem s.quotient hx⟩ v
  intro x hx
  let xX : X d.radical a := ⟨x,hx.1⟩
  have hfix : (s.sectionData.coordinates xX).toAdd ∈ OneCohomology.fixed (s.action.comp A.subtype) := by
    rintro ⟨_,⟨g,hg,rfl⟩⟩
    change (s.action.comp s.quotient) g (s.sectionData.coordinates xX).toAdd = _
    rw [←s.sectionData.equivariant g xX]
    congr 2
    apply Subtype.ext
    have hc := hx.2 g.val hg
    exact (congrArg (fun y => y*g.val⁻¹) hc).trans (mul_inv_cancel_right x g.val)
  have hmem := dualCover_fixed_le_natural_of_no_refinement i hi hdual A hno hfix
  obtain ⟨u,hu,he⟩ := (hrange _).mp hmem
  have hdiff : (u⁻¹*xX : X d.radical a) ∈ s.sectionData.coordinates.ker := by
    change s.sectionData.coordinates (u⁻¹*xX) = 1
    rw [map_mul,map_inv,show s.sectionData.coordinates u = s.sectionData.coordinates xX
      from Multiplicative.toAdd.injective he,inv_mul_cancel]
  rw [s.sectionData.kernel_eq] at hdiff
  have hd : ((u⁻¹*xX : X d.radical a) : FreeAmalgam d.radical) ∈ fixedCore d.radical a := hdiff.2
  have hmul := mul_mem (mem_sup_left hu) (mem_sup_right hd)
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_cancel_left] using hmul

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
