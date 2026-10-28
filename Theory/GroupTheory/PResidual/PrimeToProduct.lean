module
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# Prime-to-p residuals of normal products

For G=AB with both factors normal, join their embedded prime-to-p
residuals to form R. The two relative indices |A:A∩R| and |B:B∩R|
are prime to p. Factoring |G:R| through RA proves the same for G/R,
so the defining minimality of the residual gives equality.

The actual application is the pair of point-stabilizer preimages in
Aschbacher--Smith, paragraph preceding 12.3.13, printed p.811.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The prime-to-p residual of a normal product is the product of the
embedded prime-to-p residuals of the two factors. -/
theorem primeToResidual_eq_sup_of_normal_generators (p : ℕ) [Fact p.Prime]
    (A B : Subgroup G) [A.Normal] [B.Normal] (hgen : A ⊔ B = ⊤) :
    primeToResidual p G = (primeToResidual p A).map A.subtype ⊔
      (primeToResidual p B).map B.subtype := by
  let RA := (primeToResidual p A).map A.subtype
  let RB := (primeToResidual p B).map B.subtype
  let R := RA ⊔ RB
  have hn (X : Subgroup G) [X.Normal] : ((primeToResidual p X).map X.subtype).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←X.normalizer_eq_top]
    exact normalizer_le_normalizer_characteristic_image X (primeToResidual p X)
  let : RA.Normal := hn A
  let : RB.Normal := hn B
  let : R.Normal := inferInstance
  have hRA : primeToResidual p A ≤ R.subgroupOf A := by
    intro a ha
    exact mem_sup_left (mem_map_of_mem A.subtype ha)
  have hRB : primeToResidual p B ≤ R.subgroupOf B := by
    intro b hb
    exact mem_sup_right (mem_map_of_mem B.subtype hb)
  have hA : Nat.Coprime p (R.relIndex A) :=
    (primeToResidual_index_coprime p).coprime_dvd_right (index_dvd_of_le hRA)
  have hB : Nat.Coprime p (R.relIndex B) :=
    (primeToResidual_index_coprime p).coprime_dvd_right (index_dvd_of_le hRB)
  have hgen' : (R ⊔ A) ⊔ B = ⊤ := by rw [sup_assoc,hgen,sup_top_eq]
  have hindex : (R ⊔ A).index = (R ⊔ A).relIndex B := by
    rw [←relIndex_top_right,←hgen',relIndex_sup_left]
  apply le_antisymm ?_ (sup_le (map_primeToResidual_le_of_hom p A.subtype)
    (map_primeToResidual_le_of_hom p B.subtype))
  apply primeToResidual_le
  change Nat.Coprime p R.index
  rw [←relIndex_mul_index (show R ≤ R ⊔ A from le_sup_left),relIndex_sup_left,hindex]
  exact hA.mul_right (hB.coprime_dvd_right (relIndex_dvd_of_le_left B le_sup_left))

end Subgroup
