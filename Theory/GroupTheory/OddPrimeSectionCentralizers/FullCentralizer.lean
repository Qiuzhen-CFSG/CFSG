module

public import Theory.GroupTheory.OddPrimeSectionCentralizers
public import Theory.GroupTheory.FaithfulSupplementCentralizer
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Full involution-centralizer rank in rank-two sections

Let a finite group be a surjective image of a group of odd prime rank at
most two. If an involution acts nontrivially on a normal p-subgroup P,
then every p-subgroup R of its centralizer is cyclic. Indeed Q = PR is
normalized by the involution and the local group H = Q⟨t⟩ has a
self-centralizing p-core. Restrict the original surjection to the actual
preimage of H and apply the section-centralizer theorem there. Its cyclic
core centralizer contains the actual R.

Thus the full involution centralizer has p-rank at most one. The rank
bound is always on the original prequotient, with no assertion that
prime rank is monotone under arbitrary quotients.

Source: Aschbacher--Smith, D.2.21 and its A.1.31(1) input, printed
pp.188 and 27--28. This argument does not require a representation.
-/

public section
open Subgroup
namespace Theory.GroupTheory

universe u v
variable {K : Type u} [Group K] [Finite K] {G : Type v} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

private theorem faithful_involution_on_overgroup
    (P Q : Subgroup G) (hPQ : P ≤ Q) (t : G) (ht : orderOf t = 2)
    (htP : t ∉ centralizer (P : Set G))
    (hn : zpowers t ≤ normalizer (Q : Set G)) :
    Function.Injective (Q.normalizerMonoidHom.comp (inclusion hn)) := by
  classical
  rw [← MonoidHom.ker_eq_bot_iff]
  apply bot_unique
  intro a ha
  have hc : a.val ∈ centralizer (Q : Set G) := by
    change inclusion hn a ∈ Q.normalizerMonoidHom.ker at ha
    rwa [normalizerMonoidHom_ker] at ha
  have hcases : a.val = 1 ∨ a.val = t := by
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp
      ((mem_zpowers_iff_mem_range_orderOf).mp a.property)
    have hi' := Finset.mem_range.mp hi
    rw [ht] at hi'
    interval_cases i
    · exact Or.inl (by simpa only [pow_zero] using he.symm)
    · exact Or.inr (by simpa only [pow_one] using he.symm)
  rcases hcases with h | h
  · exact Subtype.ext h
  · exact (htP (h ▸ centralizer_le hPQ hc)).elim

private theorem local_characteristic_prime
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (R : Subgroup G) (hR : IsPGroup p R) (t : G) (ht : orderOf t = 2)
    (htP : t ∉ centralizer (P : Set G))
    (hRt : R ≤ centralizer ({t} : Set G)) (hp : Odd p) :
    generalizedFitting ((P ⊔ R) ⊔ zpowers t : Subgroup G) = pCore p ((P ⊔ R) ⊔ zpowers t : Subgroup G) ∧
      R.subgroupOf ((P ⊔ R) ⊔ zpowers t) ≤ pCore p ((P ⊔ R) ⊔ zpowers t : Subgroup G) := by
  let Q := P ⊔ R
  let H := Q ⊔ zpowers t
  have hQ : IsPGroup p Q := hP.to_sup_of_normal_left hR
  have htR : t ∈ normalizer (R : Set G) := by
    apply centralizer_le_normalizer
    intro r hr
    exact (hRt hr t (Set.mem_singleton t)).symm
  have hn : zpowers t ≤ normalizer (Q : Set G) := by
    apply zpowers_le.mpr
    exact normalizer_inf_normalizer_le_normalizer_sup P R
      ⟨le_normalizer_of_normal (mem_top t), htR⟩
  have hHn : H ≤ normalizer (Q : Set G) := sup_le Q.le_normalizer hn
  have hQH : Q ≤ H := le_sup_left
  let : (Q.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hQH).mpr hHn
  have hQcore : Q.subgroupOf H ≤ pCore p H := le_sSup ⟨inferInstance, hQ.comap_subtype⟩
  have htwo : IsPGroup 2 (zpowers t) := by
    apply IsPGroup.of_card (n := 1)
    simp only [Nat.card_zpowers, ht, pow_one]
  have hc : pCore p (zpowers t) = ⊥ := by
    exact disjoint_self.mp (IsPGroup.disjoint_of_ne p 2
      (fun he => by rw [he] at hp; norm_num at hp) _ _ pCore_isPGroup (htwo.to_subgroup _))
  have hself : H ⊓ centralizer (Q : Set G) ≤ Q :=
    sup_inf_centralizer_le_of_faithful_supplement Q (zpowers t) hn hQ hc
      (faithful_involution_on_overgroup P Q le_sup_left t ht htP hn)
  have hF : generalizedFitting H = pCore p H := by
    apply generalizedFitting_eq_pCore_of_selfCentralizing
    intro x hx
    apply hQcore
    apply hself
    refine ⟨x.property, ?_⟩
    intro q hq
    exact congrArg Subtype.val (hx ⟨q, hQH hq⟩ (hQcore hq))
  exact ⟨hF, (subgroupOf_mono H le_sup_right).trans hQcore⟩

/-- Restrict the literal surjection to the literal preimage of a subgroup. -/
private def preimageSurjection (f : K →* G) (H : Subgroup G) : H.comap f →* H where
  toFun x := ⟨f x, x.property⟩
  map_one' := Subtype.ext (f.map_one)
  map_mul' x y := Subtype.ext (f.map_mul x y)

omit [Finite K] [Finite G] in
private theorem preimageSurjection_surjective (f : K →* G) (hf : Function.Surjective f)
    (H : Subgroup G) : Function.Surjective (preimageSurjection f H) := by
  intro x
  obtain ⟨y, hy⟩ := hf x
  exact ⟨⟨y, show f y ∈ H from hy ▸ x.property⟩, Subtype.ext hy⟩

/-- Every p-subgroup of the full involution centralizer is cyclic. -/
theorem cyclic_pSubgroup_in_involution_centralizer_of_surjective_rank_two
    (hp : Odd p) (f : K →* G) (hf : Function.Surjective f) (hrank : primeRank p K ≤ 2)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (t : G) (ht : orderOf t = 2) (htP : t ∉ centralizer (P : Set G))
    (R : Subgroup G) (hR : IsPGroup p R) (hRt : R ≤ centralizer ({t} : Set G)) :
    IsCyclic R := by
  let H : Subgroup G := (P ⊔ R) ⊔ zpowers t
  have hRH : R ≤ H := le_sup_right.trans le_sup_left
  have htH : t ∈ H := (le_sup_right : zpowers t ≤ H) (mem_zpowers t)
  let a : H := ⟨t, htH⟩
  have ha : orderOf a = 2 := (orderOf_injective H.subtype H.subtype_injective a).symm.trans ht
  have hS : IsPGroup 2 (zpowers a) := by
    apply IsPGroup.of_card (n := 1)
    simp only [Nat.card_zpowers, ha, pow_one]
  have hSbot : zpowers a ≠ ⊥ := by
    intro hb
    have he : a = 1 := mem_bot.mp (hb ▸ mem_zpowers a)
    simp [he] at ha
  have hlocal := local_characteristic_prime P hP R hR t ht htP hRt hp
  have hcyc := cyclic_primeCore_centralizer_of_surjective_rank_le_two hp
    ((primeRank_subgroup_le p (H.comap f)).trans hrank)
    (preimageSurjection f H) (preimageSurjection_surjective f hf H)
    hlocal.1 (zpowers a) hS hSbot
  let C := (centralizer (zpowers a : Set H)).subgroupOf (pCore p H)
  let : IsCyclic C := hcyc
  let j : R →* C :=
    { toFun := fun x =>
        ⟨⟨⟨x.val, hRH x.property⟩, hlocal.2 x.property⟩, by
          change (⟨x.val, hRH x.property⟩ : H) ∈ centralizer (zpowers a : Set H)
          rw [mem_centralizer_iff]
          intro z hz
          obtain ⟨n, rfl⟩ := hz
          have hcomm : Commute a (⟨x.val, hRH x.property⟩ : H) := by
            apply Subtype.ext
            exact hRt x.property t (Set.mem_singleton t)
          exact (hcomm.zpow_left n).eq⟩
      map_one' := by rfl
      map_mul' := by intros; rfl }
  exact isCyclic_of_injective j
    (fun x y h => Subtype.ext (congrArg (fun z : C => z.val.val.val) h))

/-- The full centralizer rank bound, retaining rank on the source of the surjection. -/
theorem primeRank_involutionCentralizer_le_one_of_surjective_rank_le_two
    (hp : Odd p) (f : K →* G) (hf : Function.Surjective f) (hrank : primeRank p K ≤ 2)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (t : G) (ht : orderOf t = 2) (htP : t ∉ centralizer (P : Set G)) :
    primeRank p (centralizer ({t} : Set G)) ≤ 1 := by
  classical
  apply (primeRank_le_iff p 1).mpr
  intro B hB _
  let C := centralizer ({t} : Set G)
  have hcyc : IsCyclic (B.map C.subtype) :=
    cyclic_pSubgroup_in_involution_centralizer_of_surjective_rank_two hp f hf hrank
      P hP t ht htP (B.map C.subtype) (hB.map C.subtype) (map_subtype_le B)
  have hcycB : IsCyclic B := (equivMapOfInjective B C.subtype C.subtype_injective).isCyclic.mpr hcyc
  obtain ⟨b, hb⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := B)).mp hcycB
  have hgen : closure (({b} : Finset B) : Set B) = ⊤ := by
    simpa only [Finset.coe_singleton, ← zpowers_eq_closure] using hb
  simpa only [Finset.card_singleton] using Group.rank_le hgen

end Theory.GroupTheory
