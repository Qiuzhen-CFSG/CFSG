module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.MixedWords.Commutation

/-!
# The actual replacements in Campbell's Theorem A

The two replacements use the original Sylow subgroup, its automorphism
and the chosen ambient involution. The first replaces a maximum elementary
subgroup by F, then by F^α; the second replaces it by F^(α⁻¹g).
All groups below are defined by the literal subgroup maps. No membership,
normality or noncontainment conclusion is recorded as input data.
Source: Campbell, Pushing up in Finite Groups, II.7, printed pp.33–35.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles.CampbellTheoremA
variable {H : Type*} [Group H] (S : Subgroup H)
noncomputable def fixed : Subgroup H := Campbell.V H ⊓ centralizer (S : Set H)
noncomputable def imageF (a : MulAut S) : Subgroup H := automorphismImage S a (Campbell.F H)
noncomputable def firstReplacement (a : MulAut S) (A : Subgroup H) : Subgroup H :=
  imageF S a ⊔ (((A ⊓ pCore 2 H) ⊔ Campbell.F H) ⊓ centralizer (imageF S a : Set H))
noncomputable def inverseConjugate (a : MulAut S) (g : H) : Subgroup H :=
  (imageF S a.symm).map (MulAut.conj g).toMonoidHom
noncomputable def replacement (a : MulAut S) (A : Subgroup H) (g : H) : Subgroup H :=
  inverseConjugate S a g ⊔ (firstReplacement S a A ⊓ centralizer (inverseConjugate S a g : Set H))
noncomputable def mixedActor (a : MulAut S) (g : H) : Subgroup H :=
  (automorphismImage S a.symm ((imageF S a).map (MulAut.conj g).toMonoidHom)).map
    (MulAut.conj g).toMonoidHom
end CFSG.Quasithin.ChapterC.GlaubermanNiles.CampbellTheoremA
end
