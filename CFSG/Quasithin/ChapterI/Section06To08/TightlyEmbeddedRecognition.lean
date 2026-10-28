module

public import CFSG.Quasithin.ChapterI.Section06To08.ProductDisconnected
public import BenderSuzuki.ZD.ProductClosedRecognition

/-!
# Theorem I.8.2: recognition from tight embedding

The ambient conjugates of the involutions of the original tightly embedded
subgroup form the product-closed disconnected set already constructed in
`ProductDisconnected`. Full Theorem ZD, together with central-factor elimination
and the rank-one factorization, gives both alternatives on its actual generated
subgroup. The odd-core quotient map and normalizer image are unchanged.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Theorem I.8.2, printed pp. 429--430.
-/

namespace CFSG.Quasithin.ChapterI.Section06To08
open Theory.GroupTheory BenderSuzuki PFAppendixIII PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

/-- The original I.8.2 alternative, with its exact generated subgroup, odd
core and Borel image. The second branch also records perfectness of the
involution-generated subgroup, supplied by the same ZD argument. -/
public theorem lemma_I_8_2 (K : Subgroup G)
    (hK : IsTightlyEmbedded K) (hnormal : ¬ K.Normal)
    (hodd : HasOddConjugateNormalizers K) :
    let Z := involutionConjugates K
    let L := Subgroup.closure Z
    let O := pPrimeCore 2 L
    (primeRank 2 L = 1 ∧ ∀ z : L, (z : G) ∈ Z → O ⊔ Subgroup.zpowers z = ⊤) ∨
      (commutator L = ⊤ ∧ BenderSuzuki.IsSimpleBenderGroup (L ⧸ O) ∧
        O ≤ (Subgroup.normalizer (K : Set G)).comap L.subtype ∧
        IsBorelSubgroup (((Subgroup.normalizer (K : Set G)).comap L.subtype).map
          (QuotientGroup.mk' O))) := by
  obtain ⟨hdis, hprod⟩ := lemma_I_8_2_productDisconnected K hK hnormal hodd
  exact ZD.product_closed_recognition hdis hprod

end CFSG.Quasithin.ChapterI.Section06To08
