module

public import Theory.GroupTheory.TightlyEmbedded.ProductDisconnected

/-!
# The product-disconnected reduction in Theorem I.8.2

For a nonnormal tightly embedded subgroup whose normalizers inside distinct
conjugates have odd order, the conjugacy closure of its involutions satisfies
Definition ZD and is closed under products of distinct commuting elements.
These are the inputs to the recognition step of Theorem I.8.2.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Theorem I.8.2, printed pp. 429--430.
-/

namespace CFSG.Quasithin.ChapterI.Section06To08

open Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- The product-disconnected and commuting-product conclusions established
before applying Theorem ZD in the proof of I.8.2. -/
public theorem lemma_I_8_2_productDisconnected (K : Subgroup G)
    (hK : IsTightlyEmbedded K) (hnormal : ¬ K.Normal)
    (hodd : HasOddConjugateNormalizers K) :
    IsProductDisconnected (involutionConjugates K) (Subgroup.normalizer (K : Set G)) ∧
      ∀ x ∈ involutionConjugates K, ∀ y ∈ involutionConjugates K,
        Commute x y → x ≠ y → x * y ∈ involutionConjugates K :=
  ⟨hK.productDisconnected hnormal hodd,
    fun _ hx _ hy hc hne => hK.involutionConjugates_mul hodd hx hy hc hne⟩

end CFSG.Quasithin.ChapterI.Section06To08
