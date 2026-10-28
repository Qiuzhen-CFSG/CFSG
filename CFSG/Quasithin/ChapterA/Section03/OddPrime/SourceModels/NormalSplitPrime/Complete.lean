module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverSingerUnitary
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverSingerLinear

/-!
# A.3.18 for normal split prime extensions

The earlier reductions exhaust the full Theorem C catalogue and all central
covers under the original SQTK hypotheses. The last unitary row now has
its exact Singer centralizer and fusion of every outside subgroup of order
three. Assembly keeps the literal prime-to-p core quotient, original actor,
marked outer action, full prime-to-three residual, and disjoint complement.
No classification callback or model premise remains.

This is the normal split-extension specialization needed by the Cartan
extension in 4.3.6; it does not assert the unrestricted proposition LemmaA318.
Source: Aschbacher–Smith A.3.18, printed pp.51–53, and 4.3.6, printed p.615.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime

/-- The complete normal split-prime specialization of A.3.18. -/
theorem normal_split_prime (H : Type*) [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (K : Subgroup H) (hKN : K.Normal) (hK : K.IsCComponent)
    (hquasi : IsQuasisimple (K ⧸ pCore 2 K))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (a : H) (ha : orderOf a=p) (haK : a∉K) (hgen : K ⊔ zpowers a=⊤) :
    Alternatives p K := by
  let := hKN
  let := hquasi
  rcases CoverSingerLinear.alternatives_or_unitary_star_cover hH hK hp ho hr a ha haK hgen with
    halt | ⟨rfl,hs⟩
  · exact halt
  obtain ⟨q,hq,hmod,hm,α,hact,houter,hdiag⟩ := hs.marking
  let : (starComponent 3 K).Normal :=
    (inferInstance : K.Normal).map _ (QuotientGroup.mk'_surjective _)
  have he : α=(MulAut.conjNormal (starMap 3 H a) : MulAut (starComponent 3 K)) := by
    apply MulEquiv.ext
    intro l
    exact Subtype.ext (hact l)
  have hdiag' : IsUnitaryDiagonal (starComponent 3 K) q
      (MulAut.conjNormal (starMap 3 H a)) := by rwa [he] at hdiag
  have hb : primeRank 3 (Star 3 H)≤2 :=
    (primeRank_quotient_le_of_coprime 3 (pPrimeCore 3 H) pPrimeCore_coprime_card).trans
      (hH.stronglyQuasithin 3 Nat.prime_three (by decide))
  have hjoin : starComponent 3 K ⊔ zpowers (starMap 3 H a)=⊤ := by
    have hh := congrArg (Subgroup.map (starMap 3 H)) hgen
    rw [Subgroup.map_sup,MonoidHom.map_zpowers,
      map_top_of_surjective (starMap 3 H) (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  obtain ⟨hcyc,hcard⟩ := CoverSingerUnitary.unitary_centralizer (starComponent 3 K) (starMap 3 H a)
    hs.order hs.outside hb q hq hmod hdiag'
  have hfus := CoverSingerUnitary.unitary_fusion (starComponent 3 K) (starMap 3 H a)
    hs.order hs.outside hb hjoin q hq hmod hdiag'
  exact Or.inr (Or.inr ⟨rfl,Or.inl ⟨true,q,hmod,hm⟩,
    Or.inr ⟨true,q,hmod,hm,starMap 3 H a,α,hs.order,hact,houter,hdiag,
      hs.residual,hs.disjoint,hcyc,hcard,hfus⟩⟩)

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
