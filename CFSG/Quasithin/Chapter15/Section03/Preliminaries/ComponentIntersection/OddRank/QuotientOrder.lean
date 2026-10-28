module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.OddRank.Intersection
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.QuotientCoordinates
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The rank-one intersection quotient in 15.3.12

Suppose `Y₊/O₂(Y₊)` is a three-group of exponent dividing three, as in the
quotient alternatives of 15.3.11(5). The image of a subgroup `A ≤ Y₊` in this
quotient has kernel exactly `O₂(A)`. If `m₃(A) ≤ 1`, its Sylow three-subgroup
is cyclic, so the image has order dividing three. A nontrivial two-perfect
`A` cannot have trivial two-core quotient.

Apply this to `A = O²(Y₊ ∩ L)` and derive its nontriviality using the proved
rank argument. This gives `|A/O₂(A)| = 3` and `|A|₃ = 3`. The hypotheses
concern the genuine quotient, not the exponent of `Y₊` itself. The two
quotient properties remain explicit consequences to be supplied by the
15.3.11 assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of Lemma 15.3.12(2), printed p.1125 (PDF p.1142).
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.ComponentIntersection
variable {G : Type*} [Group G] [Finite G]
variable {A Q : Type*} [Group A] [Finite A] [Group Q]

private theorem ker_eq_twoCore (f : A →* Q) (hker : IsPGroup 2 f.ker) (hq : IsPGroup 3 Q) :
    f.ker = pCore 2 A := by
  let u : A →* f.range := f.rangeRestrict
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hcore : pCore 2 f.range = ⊥ := by
    have hd := IsPGroup.disjoint_of_ne 2 3 (by decide)
      (pCore 2 f.range) (⊤ : Subgroup f.range) pCore_isPGroup
      ((hq.to_subgroup f.range).to_subgroup ⊤)
    simpa only [disjoint_top] using hd
  have hu : IsPGroup 2 u.ker := by
    change IsPGroup 2 f.rangeRestrict.ker
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have he := u.comap_pCore_of_ker_isPGroup f.rangeRestrict_surjective hu
  simpa only [hcore, MonoidHom.comap_bot, u, MonoidHom.ker_rangeRestrict] using he

private theorem cyclic_three_image (f : A →* Q) (hq : IsPGroup 3 Q)
    (hr : primeRank 3 A ≤ 1) : IsCyclic f.range := by
  let P : Sylow 3 A := Sylow.nonempty.some
  let : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  let u : A →* f.range := f.rangeRestrict
  have htop : (P.mapSurjective f.rangeRestrict_surjective : Subgroup f.range) = ⊤ := by
    apply top_unique
    exact ((hq.to_subgroup f.range).to_subgroup ⊤).le_sylow_of_normal _
  have hs : Function.Surjective (u.comp (P : Subgroup A).subtype) := by
    apply MonoidHom.range_eq_top.mp
    simpa only [MonoidHom.range_comp, range_subtype, Sylow.coe_mapSurjective] using htop
  exact isCyclic_of_surjective (u.comp (P : Subgroup A).subtype) hs

private theorem quotient_card_dvd_three {Y A : Subgroup G} (hAY : A ≤ Y)
    (hq : IsPGroup 3 (TwoCoreQuotient Y))
    (he : Monoid.exponent (TwoCoreQuotient Y) ∣ 3)
    (hr : primeRank 3 A ≤ 1) : Nat.card (TwoCoreQuotient A) ∣ 3 := by
  let f : A →* TwoCoreQuotient Y :=
    (QuotientGroup.mk' (pCore 2 Y)).comp (inclusion hAY)
  have hk : IsPGroup 2 f.ker := by
    have heq : f.ker = (pCore 2 Y).comap (inclusion hAY) := by
      ext x
      exact QuotientGroup.eq_one_iff _
    rw [heq]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hAY)
  have hker := ker_eq_twoCore f hk hq
  let e : TwoCoreQuotient A ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  let : IsCyclic f.range := cyclic_three_image f hq hr
  rw [Nat.card_congr e.toEquiv, ← IsCyclic.exponent_eq_card]
  exact (Monoid.exponent_dvd_of_monoidHom f.range.subtype
    f.range.subtype_injective).trans he

omit [Finite G] in
private theorem twoPerfect_quotient_card_ne_one {A : Subgroup G} (hne : A ≠ ⊥) (hA : IsPPerfect 2 A) :
    Nat.card (TwoCoreQuotient A) ≠ 1 := by
  intro hc
  have he : pCore 2 A = ⊤ := index_eq_one.mp hc
  have hpTop : IsPGroup 2 (⊤ : Subgroup A) := he ▸ pCore_isPGroup
  have hp : IsPGroup 2 A := hpTop.of_equiv Subgroup.topEquiv
  have hid := hA.hom_eq_one_of_isPGroup hp (MonoidHom.id A)
  apply hne ((eq_bot_iff_forall A).mpr ?_)
  intro x hx
  exact congrArg Subtype.val (DFunLike.congr_fun hid (⟨x, hx⟩ : A))


/-- The quotient order in the rank-one case, with nontriviality proved from ranks. -/
theorem intersectionResidual_quotient_card_eq_three_of_local_facts
    {Y S M I L : Subgroup G}
    (hI : I ∈ outsideFamily Y S M) (htheta : theta (M ⊓ I) = Y)
    (hLI : L ≤ I) (hindex : (normalizer (L : Set G)).relIndex I ≤ 2)
    (hY : primeRank 3 Y = 2) (hL : primeRank 3 L = 1)
    (hr : primeRank 3 I ≤ 2)
    (hq : IsPGroup 3 (TwoCoreQuotient Y))
    (he : Monoid.exponent (TwoCoreQuotient Y) ∣ 3) :
    Nat.card (TwoCoreQuotient (intersectionResidual Y L)) = 3 := by
  have hne := intersectionResidual_ne_bot_of_local_facts hI htheta hLI hindex hY
    hL.ge hr
  have hAr : primeRank 3 (intersectionResidual Y L) ≤ 1 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3
      (inclusion ((intersectionResidual_le Y L).trans inf_le_right))
      (inclusion_injective _)).trans hL.le
  have hd := quotient_card_dvd_three
    ((intersectionResidual_le Y L).trans inf_le_left) hq he hAr
  exact ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left
    (twoPerfect_quotient_card_ne_one hne (intersectionResidual_isPPerfect Y L))

/-- The three-part conclusion, retaining the actual two-core of the intersection residual. -/
theorem intersectionResidual_three_part_eq_three_of_local_facts
    {Y S M I L : Subgroup G}
    (hI : I ∈ outsideFamily Y S M) (htheta : theta (M ⊓ I) = Y)
    (hLI : L ≤ I) (hindex : (normalizer (L : Set G)).relIndex I ≤ 2)
    (hY : primeRank 3 Y = 2) (hL : primeRank 3 L = 1)
    (hr : primeRank 3 I ≤ 2)
    (hq : IsPGroup 3 (TwoCoreQuotient Y))
    (he : Monoid.exponent (TwoCoreQuotient Y) ∣ 3) :
    3 ^ (Nat.card (intersectionResidual Y L)).factorization 3 = 3 :=
  three_part_eq_three_of_quotient_card
    (intersectionResidual_quotient_card_eq_three_of_local_facts
      hI htheta hLI hindex hY hL hr hq he)

end CFSG.Quasithin.Chapter15.Section03.ComponentIntersection

end
