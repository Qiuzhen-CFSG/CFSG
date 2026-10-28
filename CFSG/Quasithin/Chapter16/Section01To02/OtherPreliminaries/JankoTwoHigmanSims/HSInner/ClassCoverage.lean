module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.LocalKernel
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.Enumeration
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.Marking
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic

/-!
# Exhaustive inner HS classes and centralizer transport

The finite certificates prove, unconditionally, that every involution in the
fixed degree-100 carrier is conjugate to `e0` or the distinct short word `t`.
This eliminates the proposed order-7680 premise from the class coverage step.

The checked product embedding and independent upper bound of 2880 identify
the entire `C(t)` with `C₂ × Aut(A₆)`, by finite cardinality. Conjugation then
transports that equivalence to every involution outside the class of `e0`.
Thus `involution_alternative` has no centralizer-order, fusion, simplicity or
perfectness premise. The extension structure of `C(e0)` and the source's outer
automorphism alternatives are separate obligations of the source assembly.

Source: Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3, Table 5.3m.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage
open Subgroup
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates

/-- The exact product specified by the source has order 2880. -/
theorem product_card : Nat.card (C2 × MulAut A6) = 2880 := by
  rw [Nat.card_prod, AlternatingSix.ShadowLocal.card_aut]
  have h2 : Nat.card C2 = 2 := by simp [C2]
  rw [h2]

/-- An embedding fills the entire centralizer once its independent upper bound
is proved. -/
theorem product_centralizer_equiv_of_embedding_and_bound
    (f : C2 × MulAut A6 →* centralizer ({t} : Set Carrier))
    (hf : Function.Injective f)
    (hbound : Nat.card (centralizer ({t} : Set Carrier)) ≤ 2880) :
    Nonempty (centralizer ({t} : Set Carrier) ≃* C2 × MulAut A6) := by
  have hb : Function.Bijective f := hf.bijective_of_nat_card_le (by rwa [product_card])
  exact ⟨(MulEquiv.ofBijective f hb).symm⟩

/-- Carrier conjugacy identifies full centralizers in the direction used by assembly. -/
theorem centralizer_equiv_of_isConj {x y : Carrier} (h : IsConj x y) :
    Nonempty (centralizer ({y} : Set Carrier) ≃* centralizer ({x} : Set Carrier)) := by
  obtain ⟨e⟩ := fixed_equiv_centralizer_of_isConj h
  exact ⟨(MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj y)).symm.trans e⟩

/-- Exhaustive centralizer coverage once the marked second centralizer is identified. -/
theorem involution_alternative_of_product_centralizer
    (ht : Nonempty (centralizer ({t} : Set Carrier) ≃* C2 × MulAut A6))
    (x : Carrier) (hx : orderOf x = 2) :
    IsConj e0 x ∨ Nonempty (centralizer ({x} : Set Carrier) ≃* C2 × MulAut A6) := by
  rcases involution_classes x hx with h | h
  · exact Or.inl h
  · obtain ⟨e⟩ := centralizer_equiv_of_isConj h
    exact Or.inr (ht.map (fun f => e.trans f))

/-- The two independent finite model calculations imply the requested alternative
for every involution, with no further fusion or centralizer-order premise. -/
theorem involution_alternative_of_embedding_and_bound
    (f : C2 × MulAut A6 →* centralizer ({t} : Set Carrier))
    (hf : Function.Injective f)
    (hbound : Nat.card (centralizer ({t} : Set Carrier)) ≤ 2880)
    (x : Carrier) (hx : orderOf x = 2) :
    IsConj e0 x ∨ Nonempty (centralizer ({x} : Set Carrier) ≃* C2 × MulAut A6) :=
  involution_alternative_of_product_centralizer
    (product_centralizer_equiv_of_embedding_and_bound f hf hbound) x hx

/-- The entire centralizer of the marked second involution is the exact source
product. The independent embedding and upper-bound calculations discharge
both premises of the finite-cardinality assembly. -/
theorem product_centralizer_equiv :
    Nonempty (centralizer ({t} : Set Carrier) ≃* C2 × MulAut A6) := by
  obtain ⟨f, hf⟩ := ProductEmbedding.exists_embedding
  exact product_centralizer_equiv_of_embedding_and_bound f hf t_centralizer_card_le_2880

/-- Every involution of the fixed HS carrier is conjugate to `e0` or has full
centralizer isomorphic to `C₂ × Aut(A₆)`. No assumption on `|C(e0)|` is needed. -/
theorem involution_alternative (x : Carrier) (hx : orderOf x = 2) :
    IsConj e0 x ∨ Nonempty (centralizer ({x} : Set Carrier) ≃* C2 × MulAut A6) :=
  involution_alternative_of_product_centralizer product_centralizer_equiv x hx

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage
