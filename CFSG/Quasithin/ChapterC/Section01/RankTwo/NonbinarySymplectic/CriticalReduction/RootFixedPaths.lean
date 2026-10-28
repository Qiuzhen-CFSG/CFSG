module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootFixedKernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.IndividualPaths

/-!
# The full fixed kernel at the actual selected root neighbor

The existing individual-generation selector and the full-cover root fixer
identify the trapped neighbor's kernel on the whole X-intersection. The
original endpoint normalizes this kernel joined with the starting seed.
The same conjugator retains residual generation, both whole-edge-Z fixed
equalities, the exact B-relative U-index, strict quotient-image growth,
and every backward-path overlap or the complete trapped-root data.

This discharges the endpoint-normalization premise of source MS93 (5.7),
printed p.919, at its actual unequal-mover selector. The individual mover's
normalization and the field-sized kernel index remain to exclude trapping.
The original distance and all central attachments are retained.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The same selected neighbor retains the full root-fixed kernel and
its endpoint normalization, with all individual-generation and path data. -/
theorem Input.replacement_unequal_root_fixed_kernel_at_neighbor
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2)) :
    ∃ g ∈ Ltilde d.radical a,
      let w := act d.radical g⁻¹ t
      let v := act d.radical g⁻¹ c
      let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2) ⊔
        Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
          (Q d.radical t) (Nat.card F^2)
      let Ja := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical w) (Nat.card F^2)
      let Ec := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical w) (Nat.card F^2)
      Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
      (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) =
        (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ∧
      J.map (MulAut.conj g).toMonoidHom =
        Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical w) (Nat.card F^2) ⊔
        Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical w) (Nat.card F^2) ∧
      J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z = stabilizer d.radical a ∧
      Ltilde d.radical a ≤ Ec ⊔ Z d.radical z ∧
      Z d.radical t ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      Z d.radical t ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      ⁅⁅U d.radical a,Ja⁆,Ja⁆ = ⊥ ∧ ⁅⁅U d.radical v,Ec⁆,Ec⁆ = ⊥ ∧
      (centralizer (Ec : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = Nat.card F^3 ∧
      ¬ Q d.radical a ≤ Ec ∧ Nat.card F^2 < (Q d.radical a).relIndex Ec ∧
      ¬ Z d.radical z ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ((∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = w ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∨
      (Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
        (Q d.radical z).relIndex (Z d.radical a) = Nat.card F ∧
        (Q d.radical a).relIndex (Z d.radical z) = Nat.card F ∧
        Nat.card F ≤ (centralizer (Z d.radical v : Set (FreeAmalgam d.radical))).relIndex
          (Z d.radical z ⊓ Q d.radical a) ∧
        X d.radical z ⊓ Q d.radical a ≤ normalizer (Z d.radical v : Set _) ∧
        ⁅⁅X d.radical z ⊓ Q d.radical a,Z d.radical v⁆,Z d.radical v⁆ = ⊥ ∧
        (Z d.radical v ⊔ Z d.radical a) ⊓ centralizer
          ((X d.radical z ⊓ Q d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) =
          Z d.radical a ⊔ ((Z d.radical v ⊔ Z d.radical a) ⊓ Q d.radical z) ∧
        Z d.radical z ≤ normalizer (((Z d.radical v ⊓ centralizer
          ((X d.radical z ⊓ Q d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) ⊔
          Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))) := by
  obtain ⟨g,hg,haw,hvw,hindex,htransport,hgen,hres,hfixed,hindividual,
    hquadA,hquadC,hcube,hnot,hlarge,hn,hback⟩ :=
      h.replacement_unequal_individual_generation_root_at_neighbor d path hb hat hfirst hct
        hnormal hsmall hne
  refine ⟨g,hg,haw,hvw,hindex,htransport,hgen,hres,hfixed,hindividual,
    hquadA,hquadC,hcube,hnot,hlarge,hn,?_⟩
  rcases hback with hback | ⟨htrap,hi,hi',hmove,hnorm,hquad⟩
  · exact Or.inl hback
  · obtain ⟨hcent,hendpoint⟩ := h.replacement_trapped_root_endpoint_normalizes_fixed_kernel
      d path hb haw hvw hn htrap
    exact Or.inr ⟨htrap,hi,hi',hmove,hnorm,hquad,hcent,hendpoint⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
