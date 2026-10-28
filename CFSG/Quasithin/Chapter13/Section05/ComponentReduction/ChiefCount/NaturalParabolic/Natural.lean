module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.NaturalParabolic.Actor
public import Theory.GroupTheory.NoncentralChiefRefinement.RepeatedBinaryFlag
/-!
# The 2s natural chief factors on the literal residual section

The aligned copy coordinates identify (S intersect L1)/(S2 intersect L1)
with the same s natural planes supplied by c. The Borel line and its quotient
are irreducible noncentral binary constituents. Pulling back their flags in
successive coordinate supports gives an actual chief series of length and
count 2s. Equivariant Jordan--Hölder transfers the count to every chief series
with these endpoints. The construction includes s = 0.

Source: Aschbacher--Smith, 13.5.22(2), p.924/PDF p.941, using G.2.4(6).
-/

@[expose] public section
open Subgroup NoncentralChiefRefinement Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.NaturalParabolic
open ChapterG.Section02 ChapterG.Section02.Setup
open ChapterG.Section02.AlternatingFive
open ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry
open Representation.SL2FourNatural.BorelFactors
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}
variable (d : Hypothesis D g) (hgen : D.I g = D.L)
  [((AlternatingFive.S₂ D g).subgroupOf (D.S g)).Normal]
  {s : ℕ} (c : NaturalLayer D g F4 s d.L_le_I)
  (a : SL(2,F4))
  (ha : ((D.star D.L₁).subgroupOf (D.star D.L)).map
    (c.model.trans (MulAut.conj a)).toMonoidHom = B0)

noncomputable def naturalCoordinates :
    SectionCoordinates (second d) (core d)
      (naturalRepresentation (c.model.trans (MulAut.conj a)) ha) s where
  equiv := (upperSectionEquiv d hgen c).trans (adjustedCoordinates d c a)
  equivariant k x j := congrFun (adjustedCoordinates_equivariant d hgen c a k x) j

include hgen c in
theorem exists_natural_refinement :
    ∃ t : ChiefSeries D.L₁, t.head = second d ∧ t.last = core d ∧
      t.length = 2 * s ∧ t.noncentralTwoCount = 2 * s := by
  obtain ⟨a, _, ha⟩ := exists_natural_alignment_conjugator d c
  let e := c.model.trans (MulAut.conj a)
  let P := naturalLine e ha
  let := naturalLine_irreducible e ha
  let := naturalQuotient_irreducible e ha
  obtain ⟨hP,hQ⟩ := natural_factors_noncentral e ha
  exact (naturalCoordinates d hgen c a ha).exists_repeatedFlag_refinement
    (second_le_core d) P hP hQ

include hgen c in
theorem natural_count (t : ChiefSeries D.L₁)
    (ht0 : t.head = second d) (ht1 : t.last = core d) :
    t.noncentralTwoCount = 2 * s := by
  obtain ⟨u, hu0, hu1, _, huc⟩ := exists_natural_refinement d hgen c
  exact (t.noncentralTwoCount_eq u (ht0.trans hu0.symm) (ht1.trans hu1.symm)).trans huc
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.NaturalParabolic
