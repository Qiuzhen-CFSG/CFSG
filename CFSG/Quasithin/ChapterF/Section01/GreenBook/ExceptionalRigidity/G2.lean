module

public import Theory.GroupTheory.Amalgam.ExtensionTransport
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.OverlapExtensions
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.G2
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.FullTwists.Data
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.FullTwists.Certificate
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.FullTwists.Actual

/-!
# Concrete overlap extensions for the binary G₂ exceptional amalgams

For G₂(2)′ every overlap automorphism extends across the first parabolic.
The finite word-coordinate construction is transported to the catalogue's
literal Sylow overlap; both squares of the comparison are proved. Thus every
right twist factors, and independent parabolic isomorphisms for an arbitrary
faithful Sylow amalgam upgrade to a compatible amalgam isomorphism.

For G₂(2), the complete finite twist certificate combines with the realization
of the 192/64/192 word tables in the actual parabolics. This constructs both
endpoint extensions and proves the same factorization and recognition results.
The genuine conjugation identification with Aut(G₂(2)′) transports recognition
to its marked automorphism-group amalgam as well. No certificate or realization
premise remains in these recognition results.

Source context: Aschbacher--Smith, F.1.11--12, printed pp.262--263, and
Goldschmidt, *Automorphisms of trivalent graphs*, Ann. Math. 111 (1980),
377--406, DOI 10.2307/1971203. The present proof is an independent calculation
in the actual octonion models. The separate comparison of the original DGS
and Goldschmidt input hypotheses belongs to the source assembly; it is not
asserted here. The two model calculations apply to F.1.12(I)(8) and (I)(3)
at q = 2, respectively.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.ExceptionalRigidity.G2
open Theory.GroupTheory RankTwoAmalgam
open Atlas.G2 Atlas.G2.BinaryParabolicPair Atlas.G2.LieParabolicSetup
open Atlas.G2.LieAutomorphismExtensions
open ExceptionalModels.G2

private theorem word_left_eq : BinaryLeft = derivedL₁ := by
  change parabolic₁.subgroupOf BinaryDerived = firstParabolic.subgroupOf BinaryDerived
  rw [parabolic₁_binary]

private theorem word_middle_eq : binaryOverlap = derivedB := by
  change BinaryLeft ⊓ BinaryRight = derivedB
  rw [word_left_eq]
  exact derived_overlap

/-- Identity on ambient elements aligns the word tables with both catalogue maps. -/
def derivedWordIso : Iso binaryAmalgam simpleAmalgam where
  left := MulEquiv.subgroupCongr word_left_eq
  middle := MulEquiv.subgroupCongr word_middle_eq
  right := MulEquiv.refl _
  left_commutes _ := by apply Subtype.ext; rfl
  right_commutes _ := by apply Subtype.ext; rfl

/-- Every automorphism of the literal derived Sylow overlap extends on the left. -/
theorem simple_extendsAcross_left (d : MulAut derivedB) :
    ExtendsAcross simpleAmalgam.left d :=
  extendsAcross_of_equivalences derivedWordIso.left derivedWordIso.middle
    derivedWordIso.left_commutes
    BinaryAmalgamBound.OverlapExtensions.binary_extendsAcross_left d

/-- All derived twists factor; the faithfulness premise is unnecessary here. -/
theorem simple_factorsThrough (d : MulAut derivedB) :
    FactorsThrough simpleAmalgam d := by
  refine ⟨d, MulEquiv.refl _, simple_extendsAcross_left d, ?_, ?_⟩
  · exact ⟨MulEquiv.refl _, fun _ => rfl⟩
  · ext b
    rfl

/-- The faithful-twist contract used by the generic Sylow recognition theorem. -/
theorem simple_faithful_twist_factorization (d : MulAut derivedB)
    (_hf : Faithful (twistRight simpleAmalgam d)) :
    FactorsThrough simpleAmalgam d := simple_factorsThrough d

/-- Genuine compatible recognition, retaining both overlap squares. -/
theorem simple_iso_of_parabolicEquiv
    {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R} (hs : SylowEmbedded 2 α) (hf : Faithful α)
    (e : ParabolicEquiv α simpleAmalgam) :
    Nonempty (Iso α simpleAmalgam) :=
  iso_of_faithful_twist_factorization hs
    (sylowEmbedded_ofSubgroups derivedS _ _ _ _ _ rfl)
    hf e simple_faithful_twist_factorization

/-- Assembly of an explicit full-model finite calculation and its coordinate comparison. -/
theorem full_factorsThrough_of_tables
    (E : BinaryAmalgamBound.FullTwists.table.Realization fullAmalgam)
    (hfinite : BinaryAmalgamBound.FullTwists.table.TwistsVerified)
    (d : MulAut fullB) : FactorsThrough fullAmalgam d :=
  E.factorsThrough full_embeddings.1 full_embeddings.2 hfinite d

/-- Every full overlap automorphism factors through actual endpoint extensions.
The coordinate realization and complete finite certificate are both discharged. -/
theorem full_factorsThrough (d : MulAut fullB) : FactorsThrough fullAmalgam d :=
  full_factorsThrough_of_tables BinaryAmalgamBound.FullTwists.fullConcreteRealization
    BinaryAmalgamBound.FullTwists.full_twistsVerified d

/-- The full model satisfies the faithful-twist recognition contract. -/
theorem full_faithful_twist_factorization (d : MulAut fullB)
    (_hf : Faithful (twistRight fullAmalgam d)) :
    FactorsThrough fullAmalgam d := full_factorsThrough d

/-- Actual full-model recognition once the independent finite obligations are supplied. -/
theorem full_iso_of_parabolicEquiv_of_tables
    {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R} (hs : SylowEmbedded 2 α) (hf : Faithful α)
    (e : ParabolicEquiv α fullAmalgam)
    (E : BinaryAmalgamBound.FullTwists.table.Realization fullAmalgam)
    (hfinite : BinaryAmalgamBound.FullTwists.table.TwistsVerified) :
    Nonempty (Iso α fullAmalgam) :=
  iso_of_faithful_twist_factorization hs
    (sylowEmbedded_ofSubgroups fullS _ _ _ _ _ rfl)
    hf e (fun d _ => full_factorsThrough_of_tables E hfinite d)

/-- Genuine full-model recognition with both overlap squares and no table premise. -/
theorem full_iso_of_parabolicEquiv
    {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R} (hs : SylowEmbedded 2 α) (hf : Faithful α)
    (e : ParabolicEquiv α fullAmalgam) :
    Nonempty (Iso α fullAmalgam) :=
  iso_of_faithful_twist_factorization hs
    (sylowEmbedded_ofSubgroups fullS _ _ _ _ _ rfl)
    hf e full_faithful_twist_factorization

/-- The same conditional recognition uses the genuine conjugation identification
of G₂(2) with Aut(G₂(2)′), including both marked endpoint images. -/
theorem automorphism_iso_of_parabolicEquiv_of_tables
    {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R} (hs : SylowEmbedded 2 α) (hf : Faithful α)
    (e : ParabolicEquiv α automorphismAmalgam)
    (E : BinaryAmalgamBound.FullTwists.table.Realization fullAmalgam)
    (hfinite : BinaryAmalgamBound.FullTwists.table.TwistsVerified) :
    Nonempty (Iso α automorphismAmalgam) := by
  obtain ⟨f⟩ := full_iso_of_parabolicEquiv_of_tables hs hf
    (e.trans automorphismAmalgamIso.symm.toParabolicEquiv) E hfinite
  exact ⟨f.trans automorphismAmalgamIso⟩

/-- Recognition in the literal automorphism group, through the marked conjugation
identification with the full binary G₂ model. -/
theorem automorphism_iso_of_parabolicEquiv
    {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R} (hs : SylowEmbedded 2 α) (hf : Faithful α)
    (e : ParabolicEquiv α automorphismAmalgam) :
    Nonempty (Iso α automorphismAmalgam) := by
  obtain ⟨f⟩ := full_iso_of_parabolicEquiv hs hf
    (e.trans automorphismAmalgamIso.symm.toParabolicEquiv)
  exact ⟨f.trans automorphismAmalgamIso⟩

end CFSG.Quasithin.ChapterF.GreenBook.ExceptionalRigidity.G2
