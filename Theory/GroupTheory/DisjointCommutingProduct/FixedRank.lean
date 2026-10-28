module
public import Theory.GroupTheory.DisjointCommutingProjection
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.InvariantLeviDecomposition

/-!
# Fixed rank in a product of two commuting factors

An involution exchanging two disjoint commuting subgroups has a fixed subgroup
that embeds into either factor by the actual product projection. If instead
it preserves the factors, their fixed subgroups form a direct product. When
square-one elements of each factor lie in two exchanged subgroups, the fixed
prime-two rank is bounded by the sum of the ranks of their intersections.

The proof uses uniqueness of product coordinates and the characterization of
prime rank by elementary abelian subgroups. The factors and centralizers are
subgroups of the original ambient group throughout.

Source application: Aschbacher–Smith, the double linear case of §2.4,
printed pp.540–541, outside-involution bound in the Thompson-subgroup argument.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G]

private theorem conj_eq_self_of_mem_centralizer {a x : G}
    (hx : x ∈ centralizer ({a} : Set G)) : (MulAut.conj a) x = x := by
  change a * x * a⁻¹ = x
  exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hx).symm

/-- The projection onto the first factor embeds the fixed group when the
second factor is carried to the first. -/
theorem exists_injective_fixed_projection_of_swap (R₁ R₂ : Subgroup G)
    (hd : Disjoint R₁ R₂) (hc : R₁ ≤ centralizer (R₂ : Set G))
    (a : G) (ha : a ^ 2 = 1) (hswap : R₁.conjBy a = R₂) :
    ∃ f : ((R₁ ⊔ R₂) ⊓ centralizer ({a} : Set G) : Subgroup G) →* R₁,
      Function.Injective f := by
  have hback : R₂.conjBy a = R₁ := by
    rw [← hswap, conjBy_conjBy, ← pow_two, ha, conjBy_one]
  obtain ⟨f, _, hk, _⟩ := exists_projection_of_disjoint_commuting_product
    (R₁ ⊔ R₂) R₁ R₂ rfl hd hc
  let j := inclusion (show (R₁ ⊔ R₂) ⊓ centralizer ({a} : Set G) ≤ R₁ ⊔ R₂
    from inf_le_left)
  refine ⟨f.comp j, (MonoidHom.ker_eq_bot_iff _).mp ?_⟩
  apply eq_bot_iff.mpr
  intro x hx
  have hx₂ : (x : G) ∈ R₂ := by
    have hker : j x ∈ f.ker := hx
    rwa [hk] at hker
  have hx₁ : (x : G) ∈ R₁ := by
    have hm : (MulAut.conj a) (x : G) ∈ R₂.conjBy a := mem_map_of_mem _ hx₂
    rwa [hback, conj_eq_self_of_mem_centralizer x.property.2] at hm
  exact Subtype.ext (disjoint_def.mp hd hx₁ hx₂)

/-- A swapped pair has fixed prime rank at most the rank of either factor. -/
theorem primeRank_inf_centralizer_le_of_swap [Finite G]
    (R₁ R₂ : Subgroup G) (hd : Disjoint R₁ R₂)
    (hc : R₁ ≤ centralizer (R₂ : Set G)) (a : G)
    (ha : a ^ 2 = 1) (hswap : R₁.conjBy a = R₂) (p : ℕ) :
    primeRank p ((R₁ ⊔ R₂) ⊓ centralizer ({a} : Set G) : Subgroup G) ≤
      primeRank p R₁ := by
  obtain ⟨f, hf⟩ := exists_injective_fixed_projection_of_swap R₁ R₂ hd hc a ha hswap
  exact primeRank_le_of_injective p f hf

/-- Invariant direct factors split the centralizer of the actor. -/
theorem inf_centralizer_sup_eq_of_preserves (R₁ R₂ : Subgroup G)
    (hd : Disjoint R₁ R₂) (hc : R₁ ≤ centralizer (R₂ : Set G))
    (a : G) (h₁ : R₁.conjBy a = R₁) (h₂ : R₂.conjBy a = R₂) :
    (R₁ ⊔ R₂) ⊓ centralizer ({a} : Set G) =
      (R₁ ⊓ centralizer ({a} : Set G)) ⊔ (R₂ ⊓ centralizer ({a} : Set G)) := by
  apply le_antisymm
  · obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting R₁ R₂ hd hc
    rintro x ⟨hx, hxa⟩
    obtain ⟨⟨u,v⟩, huv⟩ := e.surjective ⟨x,hx⟩
    have huv' : (u:G) * (v:G) = x := (he u v).symm.trans (congrArg Subtype.val huv)
    have hfix := fixed_factors_of_disjoint (MulAut.conj a).toMonoidHom R₁ R₂ hd
      (fun y hy => h₁ ▸ mem_map_of_mem (MulAut.conj a).toMonoidHom hy)
      (fun y hy => h₂ ▸ mem_map_of_mem (MulAut.conj a).toMonoidHom hy)
      u.property v.property (huv' ▸ conj_eq_self_of_mem_centralizer hxa)
    have hu : (u:G) ∈ centralizer ({a} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix.1).symm
    have hv : (v:G) ∈ centralizer ({a} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix.2).symm
    rw [← huv']
    exact mul_mem (mem_sup_left ⟨u.property,hu⟩) (mem_sup_right ⟨v.property,hv⟩)
  · exact sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right)

/-- Containment of the elements of order dividing p suffices for prime-rank
monotonicity, even when the ambient subgroups are not nested. -/
theorem primeRank_le_of_pow_mem [Finite G] (K L : Subgroup G)
    (p : ℕ) [Fact p.Prime] (h : ∀ x ∈ K, x ^ p = 1 → x ∈ L) :
    primeRank p K ≤ primeRank p L := by
  apply (primeRank_le_iff_elementary_card_le K).mpr
  intro E hE
  let : IsElementaryAbelian p E := hE
  let f : E →* L := (K.subtype.comp E.subtype).codRestrict L (fun x => by
    apply h x.val.val x.val.property
    have hp := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.exponent_dvd_p x
    exact congrArg (fun y : E => (y : G)) hp)
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun z : L => (z : G)) hxy))
  have ht : IsElementaryAbelian p (⊤ : Subgroup E) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.exponent_dvd_p x.val)) }
  have hb := (primeRank_le_iff_elementary_card_le E).mp
    (primeRank_le_of_injective p f hf) ⊤ ht
  simpa using hb

/-- Fixed elements of square one lie in both exchanged covering subgroups. -/
theorem square_one_mem_inf_of_fixed_of_cover (R U V : Subgroup G)
    (a : G) (ha : a ^ 2 = 1) (hs : U.conjBy a = V)
    (hcover : ∀ x ∈ R, x ^ 2 = 1 → x ∈ U ∨ x ∈ V)
    {x : G} (hx : x ∈ R ⊓ centralizer ({a} : Set G)) (hx₂ : x ^ 2 = 1) :
    x ∈ U ⊓ V := by
  have hs' : V.conjBy a = U := by
    rw [← hs, conjBy_conjBy, ← pow_two, ha, conjBy_one]
  have hf := conj_eq_self_of_mem_centralizer hx.2
  rcases hcover x hx.1 hx₂ with hu | hv
  · refine ⟨hu, ?_⟩
    have hm : (MulAut.conj a) x ∈ U.conjBy a := mem_map_of_mem _ hu
    rwa [hs,hf] at hm
  · refine ⟨?_,hv⟩
    have hm : (MulAut.conj a) x ∈ V.conjBy a := mem_map_of_mem _ hv
    rwa [hs',hf] at hm

/-- Preserved factors with exchanged involution covers give an additive fixed
rank bound on their intersections. -/
theorem primeRank_inf_centralizer_le_of_preserves [Finite G]
    (R₁ R₂ U₁ V₁ U₂ V₂ : Subgroup G)
    (hd : Disjoint R₁ R₂) (hc : R₁ ≤ centralizer (R₂ : Set G))
    (a : G) (ha : a ^ 2 = 1)
    (h₁ : R₁.conjBy a = R₁) (h₂ : R₂.conjBy a = R₂)
    (hs₁ : U₁.conjBy a = V₁) (hs₂ : U₂.conjBy a = V₂)
    (hcover₁ : ∀ x ∈ R₁, x ^ 2 = 1 → x ∈ U₁ ∨ x ∈ V₁)
    (hcover₂ : ∀ x ∈ R₂, x ^ 2 = 1 → x ∈ U₂ ∨ x ∈ V₂) :
    primeRank 2 ((R₁ ⊔ R₂) ⊓ centralizer ({a} : Set G) : Subgroup G) ≤
      primeRank 2 (U₁ ⊓ V₁ : Subgroup G) + primeRank 2 (U₂ ⊓ V₂ : Subgroup G) := by
  rw [inf_centralizer_sup_eq_of_preserves R₁ R₂ hd hc a h₁ h₂,
    primeRank_sup_eq_add_of_disjoint_commuting _ _
      (hd.mono inf_le_left inf_le_left)
      (fun x hx y hy => hc hx.1 y hy.1)]
  exact Nat.add_le_add
    (primeRank_le_of_pow_mem _ _ 2 (fun _ hx hp =>
      square_one_mem_inf_of_fixed_of_cover R₁ U₁ V₁ a ha hs₁ hcover₁ hx hp))
    (primeRank_le_of_pow_mem _ _ 2 (fun _ hx hp =>
      square_one_mem_inf_of_fixed_of_cover R₂ U₂ V₂ a ha hs₂ hcover₂ hx hp))

end Subgroup
