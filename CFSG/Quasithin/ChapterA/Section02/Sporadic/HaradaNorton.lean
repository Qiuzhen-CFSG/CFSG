module

public import CFSG.Quasithin.ChapterA.Section02.Sporadic
public import Theory.SpecificGroups.HaradaNorton.ProperAlternatingTwelve

/-!
# The proper A₁₂ subgroup in the F₅ case of A.2.19

Here F₅ is Harada--Norton, not Lyons: see GLS3, Table 5.3w
(`refs/KGroup/GLS3/Chapter5(sec3-).tex`) and GLS1's index.
The existing checked Suzuki presentation identifies the concrete ATLAS word
subgroup with A₁₂. It fixes a certified column, while the ambient generator b
moves coordinate 1 of that column. Thus the subgroup is proper, independently
of any ambient order or simplicity theorem. Transport gives the same proper
embedding under any explicit identification with the actual HN carrier.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma A.2.19, printed p. 41; ATLAS HNG1-max1W1 and HNG1-f5r133B0,
as retained and certified by the imported construction modules.
-/

public section
namespace CFSG.Quasithin.ChapterA

open HaradaNorton HaradaNorton.OrderCertificate Matrix

/-- The source's actual F₅ subgroup, including injectivity and properness. -/
noncomputable def hn_properA12SubgroupData : ProperA12SubgroupData HN where
  embedding := alternatingTwelveEmbedding
  injective := alternatingTwelveEmbedding_injective
  proper := alternatingTwelveEmbedding_range_ne_top

/-- Any group explicitly identified with HN contains this proper A₁₂. -/
noncomputable def properA12SubgroupData_of_hn_equiv
    {G : Type*} [Group G] (e : G ≃* HN) : ProperA12SubgroupData G :=
  hn_properA12SubgroupData.transport e.symm

end CFSG.Quasithin.ChapterA
