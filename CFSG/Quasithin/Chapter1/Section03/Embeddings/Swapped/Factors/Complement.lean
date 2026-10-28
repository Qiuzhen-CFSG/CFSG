module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Factors.Orbit
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankWitness

/-!
# Odd complements in the repeated component quotient

A noncyclic odd-prime subgroup of one factor would contain an elementary
abelian plane; two copies of this plane would violate the ambient rank-two
bound. Thus the projection images of every odd-prime subgroup are cyclic,
and the subgroup itself is abelian. Applying this to the actual complement
embedding makes its elementary/extraspecial alternative elementary.

A separate lifting lemma uses normality of a factor and coprimality: an odd
p-element which lies in that factor modulo a normal two-group already lies
in the factor. This identifies the factors upstairs without assuming a
splitting of the two-core extension.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.510 (PDF p.527),
the equality P = (P ∩ L) × (P ∩ L)^t.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.SwappedFactorsProof
universe u

/-- A noncyclic odd-prime subgroup in either repeated factor would give an
elementary abelian group of rank four in the product. -/
theorem cyclic_pSubgroup_of_product_rank {D : Type*} [Group D] [Finite D]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hr : primeRank p (D × D) ≤ 2)
    (A : Subgroup D) (hA : IsPGroup p A) : IsCyclic A := by
  by_contra hn
  obtain ⟨E, _, hcard, he⟩ :=
    hA.exists_normal_elementary_prime_sq_of_odd_not_isCyclic
      (by intro hh; rw [hh] at hp; exact (by decide : ¬ Odd 2) hp) hn
  let _ := he
  let _ : CommGroup E := IsMulCommutative.instCommGroup
  let f : E →* D := A.subtype.comp E.subtype
  have hf : Function.Injective f := A.subtype_injective.comp E.subtype_injective
  have hpow : ∀ x : E × E, x ^ p = 1 := by
    intro x
    apply Prod.ext
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p E) x.1
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p E) x.2
  have hc : Nat.card (E × E) = p ^ 4 := by
    rw [Nat.card_prod, hcard, ← pow_add]
  have hfour := primeRank_ge_of_elementary_embedding hpow hc (f.prodMap f)
    (fun a b hab => Prod.ext (hf (congrArg Prod.fst hab)) (hf (congrArg Prod.snd hab)))
  omega

/-- Every odd-prime group embedded in a repeated factor product of odd rank
at most two is abelian: its two projection images are cyclic. -/
theorem commutative_pGroup_of_product_rank {D R : Type*}
    [Group D] [Finite D] [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hr : primeRank p (D × D) ≤ 2)
    (hR : IsPGroup p R) (f : R →* D × D) (hf : Function.Injective f) :
    IsMulCommutative R := by
  let f₁ := (MonoidHom.fst D D).comp f
  let f₂ := (MonoidHom.snd D D).comp f
  let _ : IsCyclic f₁.range := cyclic_pSubgroup_of_product_rank hp hr _
    (hR.of_surjective f₁.rangeRestrict f₁.rangeRestrict_surjective)
  let _ : IsCyclic f₂.range := cyclic_pSubgroup_of_product_rank hp hr _
    (hR.of_surjective f₂.rangeRestrict f₂.rangeRestrict_surjective)
  refine ⟨⟨fun x y => hf (Prod.ext ?_ ?_)⟩⟩
  · exact congrArg Subtype.val (show f₁.rangeRestrict (x * y) = f₁.rangeRestrict (y * x) by
      rw [map_mul, map_mul, mul_comm'])
  · exact congrArg Subtype.val (show f₂.rangeRestrict (x * y) = f₂.rangeRestrict (y * x) by
      rw [map_mul, map_mul, mul_comm'])

variable {G : Type u} [Group G] [Finite G]
variable {𝒦 : GroupClass.{u}} {p : ℕ} {T X P H L : Subgroup G}

/-- The actual odd complement is abelian after embedding in the repeated
component quotient product. -/
theorem complement_commutative (h : SwappedInput 𝒦 p T X P H L)
    (e : XiQuotient (componentOrbit L T) ≃* XiQuotient L × XiQuotient L) :
    IsMulCommutative P := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  have hr : primeRank p (XiQuotient L × XiQuotient L) ≤ 2 := by
    rw [← primeRank_congr p e]
    exact (SwappedSylow.orbit_quotient_sqtk h).stronglyQuasithin p h.prime h.odd
  let f := e.toMonoidHom.comp ((SwappedSylow.imageInOrbit L T P).subtype.comp
    (SwappedSylow.quotientComplementEquiv h).toMonoidHom)
  exact commutative_pGroup_of_product_rank h.odd hr h.odd_complement.isPGroup f
    (e.injective.comp (Subtype.val_injective.comp
      (SwappedSylow.quotientComplementEquiv h).injective))

/-- For a normal factor, an odd p-element whose image modulo a normal
two-group lies in the factor already lies in the factor. -/
theorem mem_normal_factor_of_quotient_mem {D : Type*} [Group D]
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A N R : Subgroup D) [A.Normal] [N.Normal]
    (hN : IsPGroup 2 N) (hR : IsPGroup p R)
    {x : D} (hx : x ∈ R)
    (hi : QuotientGroup.mk' N x ∈ A.map (QuotientGroup.mk' N)) : x ∈ A := by
  let q := QuotientGroup.mk' A
  have hxAN : x ∈ A ⊔ N := by
    have hh : x ∈ (A.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := hi
    rwa [comap_map_eq, QuotientGroup.ker_mk'] at hh
  have hxN : q x ∈ N.map q := by
    have hh := mem_map_of_mem q hxAN
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at hh
    exact hh
  have hd := (hR.map q).disjoint_of_coprime (hN.map q) (Nat.coprime_two_right.mpr hp)
  exact (QuotientGroup.eq_one_iff x).mp (hd.le_bot ⟨mem_map_of_mem q hx, hxN⟩)

end CFSG.Quasithin.Chapter1.XiEmbedding.SwappedFactorsProof
