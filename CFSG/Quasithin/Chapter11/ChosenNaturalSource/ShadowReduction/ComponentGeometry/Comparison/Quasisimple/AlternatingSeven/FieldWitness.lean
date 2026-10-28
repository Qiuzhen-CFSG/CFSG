module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness.Transposition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness.Construction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness.Ratio

/-!
# The natural six-space and maximum elementary field witness

The chosen-flag application constructs natural coordinates on the actual
moved omega-core module and proves ratio one and m2(R1) = m2(T).
The same coordinates identify J(R1)* with a transposition. Conjugation and
Sylow localization then construct an actual maximum elementary subgroup of T
and an element normalizing the original L1, with the literal nontrivial
PSL2 field-automorphism equation in the original quotient.

Source: Aschbacher--Smith, 11.4.2, printed p.777. The earlier actual PSL2
quotient marking is supplied by the natural flag Cartan argument, with
final discharge retained by the upstream 11.4.2 assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The chosen-flag application constructs the marked natural moved six-space,
ratio one on the original action, and equality of the original two-ranks.
The earlier PSL2 marking is retained for upstream discharge. -/
theorem ofFlag_natural_six_and_rank
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hmodel : AlternatingSevenModel (ofFlag S f X z H))
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier) :
    let E := ofFlag S f X z H
    ∃ t : MovedSection (action E) (componentImage E),
      IsIrrPlus (action E) (componentImage E) t.space.toSubmodule ∧
      IsCompl t.space.toSubmodule (fixedSpace (action E) (componentImage E)) ∧
      Nonempty (MarkedActionEquiv t.space.toRepresentation (offenderGroup E) (componentImage E)
        (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) ∧
      Module.finrank (ZMod 2) (moved (action E) (componentImage E)) = 6 ∧
      quadraticRatio (action E) = 1 ∧
      ChapterB.twoRank E.R₁ = ChapterB.twoRank (T : Subgroup G) := by
  obtain ⟨_,_,_,_,_,hff,_⟩ := ofFlag_ff_reduction S f X z H h hne hstar
    hlinear h1132 hcent hline hXR
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  have hq := quadraticRatio_eq_one _ h hf hne hstar hcent hmodel hff e
  obtain ⟨t,hi,hc,ha,hd⟩ := natural_moved _ h hf hne hstar hcent hmodel hff e
  exact ⟨t,hi,hc,ha,hd,hq,twoRank_radical_eq_sylow_of_ratio _ h hf hne hstar hcent hq.ge⟩
/-- The chosen-flag application constructs the marked natural moved six-space,
the transposition image in these coordinates, ratio one on the original
action, and equality of the original two-ranks.
The earlier PSL2 marking is retained for upstream discharge. -/
theorem ofFlag_natural_transposition_and_rank
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hmodel : AlternatingSevenModel (ofFlag S f X z H))
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier) :
    let E := ofFlag S f X z H
    ∃ t : MovedSection (action E) (componentImage E),
      IsIrrPlus (action E) (componentImage E) t.space.toSubmodule ∧
      IsCompl t.space.toSubmodule (fixedSpace (action E) (componentImage E)) ∧
      ∃ a : MarkedActionEquiv t.space.toRepresentation (offenderGroup E) (componentImage E)
        (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7)),
      (∃ s : Equiv.Perm (Fin 7), s.IsSwap ∧
        ((thompsonImage E).subgroupOf (offenderGroup E)).map a.action.groupEquiv.toMonoidHom = zpowers s) ∧
      Module.finrank (ZMod 2) (moved (action E) (componentImage E)) = 6 ∧
      quadraticRatio (action E) = 1 ∧
      ChapterB.twoRank E.R₁ = ChapterB.twoRank (T : Subgroup G) := by
  obtain ⟨_,_,_,_,_,hff,_⟩ := ofFlag_ff_reduction S f X z H h hne hstar
    hlinear h1132 hcent hline hXR
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  have hq := quadraticRatio_eq_one _ h hf hne hstar hcent hmodel hff e
  obtain ⟨t,hi,hc,⟨a⟩,hd⟩ := natural_moved _ h hf hne hstar hcent hmodel hff e
  exact ⟨t,hi,hc,a,transposition_image _ h hf hne hstar hcent hline hXR hmodel e t a,
    hd,hq,twoRank_radical_eq_sylow_of_ratio _ h hf hne hstar hcent hq.ge⟩

/-- The original chosen flag supplies normalization of L1 by T; the FF
reduction and the constructed natural row discharge all other local inputs
of the maximum elementary field witness. The earlier PSL2 marking is
retained for qt-d-1222-natural-flag-cartan and final upstream assembly. -/
theorem ofFlag_hasMaximalFieldWitness
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hmodel : AlternatingSevenModel (ofFlag S f X z H))
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier) :
    HasMaximalFieldWitness (ofFlag S f X z H) := by
  obtain ⟨_,_,_,_,_,hff,_⟩ := ofFlag_ff_reduction S f X z H h hne hstar
    hlinear h1132 hcent hline hXR
  exact hasMaximalFieldWitness _ h (fixed_and_transitive D S _ hlinear h1132).1
    hne hstar hcent hline hXR hmodel hff e (f.sylow_normalizes_Li 0)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness
