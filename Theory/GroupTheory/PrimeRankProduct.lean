module

public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.QuasithinBasic

/-!
# Prime rank of direct products

Elementary subgroups attaining rank in the two factors give the lower bound;
projection onto one factor gives the reverse inequality. Disjoint commuting
subgroups therefore have additive prime rank in their join. This is the
direct-product part of the swapped-component rank calculation in
Aschbacher–Smith, 16.3.9, printed p.1180.
-/

public section

open Subgroup

/-- Prime rank is additive on finite direct products. -/
theorem primeRank_prod_eq_add {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (p : ℕ) [Fact p.Prime] : primeRank p (A × B) = primeRank p A + primeRank p B := by
  obtain ⟨E, hE, hEc⟩ := exists_elementaryAbelian_card_primeRank (G := A) (p := p)
  obtain ⟨F, hF, hFc⟩ := exists_elementaryAbelian_card_primeRank (G := B) (p := p)
  let := hE
  let := hF
  let : CommGroup E := IsMulCommutative.instCommGroup
  let : CommGroup F := IsMulCommutative.instCommGroup
  let f : E × F →* A × B := E.subtype.prodMap F.subtype
  have hf : Function.Injective f := by
    intro a b h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have hp : ∀ a : E × F, a ^ p = 1 := by
    intro a
    exact Prod.ext
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p E) a.1)
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p F) a.2)
  have hc : Nat.card (E × F) = p ^ (primeRank p A + primeRank p B) := by
    rw [Nat.card_prod, hEc, hFc, pow_add]
  have hlower := primeRank_ge_of_elementary_embedding hp hc f hf
  let π : A × B →* A := MonoidHom.fst A B
  let e : π.ker ≃* B :=
    { toFun := fun x => x.1.2
      invFun := fun b => ⟨(1, b), rfl⟩
      left_inv := fun x => Subtype.ext (Prod.ext x.property.symm rfl)
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hupper := Theory.GroupTheory.primeRank_le_ker_add (p := p) π
  rw [Theory.GroupTheory.primeRank_equiv p e] at hupper
  omega

/-- Disjoint commuting subgroups contribute independent prime ranks. -/
theorem Subgroup.primeRank_sup_eq_add_of_disjoint_commuting
    {G : Type*} [Group G] [Finite G] (A B : Subgroup G)
    (hd : Disjoint A B) (hc : A ≤ centralizer (B : Set G))
    (p : ℕ) [Fact p.Prime] :
    primeRank p (A ⊔ B : Subgroup G) = primeRank p A + primeRank p B := by
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  rw [← Theory.GroupTheory.primeRank_equiv p e, primeRank_prod_eq_add]
