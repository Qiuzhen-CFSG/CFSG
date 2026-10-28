module

public import CFSG.KnownSimple.SporadicCarriers
public import Theory.Mathieu.InvolutoryTwoComponents
public import Theory.SpecificGroups.Janko1.Model.InvolutoryTwoComponents
public import Theory.SpecificGroups.Janko4.Model.InvolutoryTwoComponents
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne

/-!
# Mathieu and Janko contributions to the known-simple B₂ property

The completed branches here are M₁₁, M₂₃, J₁ and J₄, with the exact catalogue
group instances. The Mathieu results use full automorphism coverage. The J₁
consumer discharges the innerness premise with the checked matrix-generator
rigidity proof, and J₄ uses its complete innerness and both centralizer classes.
Simplicity of the two Janko carriers may be inherited along the parent's actual
carrier equivalence; no additional order or simplicity certification is required.

The M₁₂, M₂₂, M₂₄, J₂ and J₃ branches remain assembly obligations. In particular,
conditional centralizer tables and absence of ordinary components alone do not
establish B₂. Sources: GLS II, Definition 2.4 and Lemma 5.28; GLS III, Tables
5.3a--i (`refs/KGroup/GLS3/Chapter5(sec3-).tex`).
-/

public section
open Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section03.KnownSimpleB2
open KnownSimple

/-- M₁₁ with precisely the sporadic catalogue group structure. -/
theorem m11_hasInvolutoryB2 : HasInvolutoryB2 SporadicName.m11.Carrier :=
  Sporadic.Mathieu.m11_hasInvolutoryB2

/-- M₂₃ with precisely the sporadic catalogue group structure. -/
theorem m23_hasInvolutoryB2 : HasInvolutoryB2 SporadicName.m23.Carrier :=
  Sporadic.Mathieu.m23_hasInvolutoryB2

/-- The J₁ innerness input is supplied by its actual matrix certificate. -/
theorem j1_hasInvolutoryB2 [IsSimpleGroup SporadicName.j1.Carrier] :
    HasInvolutoryB2 SporadicName.j1.Carrier := by
  let : IsSimpleGroup Janko1.Model := ‹IsSimpleGroup SporadicName.j1.Carrier›
  apply Janko1.hasInvolutoryB2_of_inner
  intro r
  obtain ⟨g, hg⟩ := Janko1.OuterCertificate.aut_inner r
  exact ⟨g, hg.symm⟩

/-- Both inner J₄ classes and all automorphisms are covered on the exact carrier. -/
theorem j4_hasInvolutoryB2 [IsSimpleGroup SporadicName.j4.Carrier] :
    HasInvolutoryB2 SporadicName.j4.Carrier := by
  let : IsSimpleGroup Janko4.Model := ‹IsSimpleGroup SporadicName.j4.Carrier›
  exact Janko4.hasInvolutoryB2

end CFSG.Quasithin.ChapterI.Section03.KnownSimpleB2
