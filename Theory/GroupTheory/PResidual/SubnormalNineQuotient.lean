module
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PPerfectHom

/-!
# Subnormal two-perfect subgroups over a residual quotient of order nine

If the two-residual of a finite group has two-core quotient of order nine,
then every subnormal two-perfect subgroup has two-core quotient of order
one, three or nine. Containment in the residual and the subnormal core
intersection theorem identify its quotient with an actual subgroup of that
order-nine quotient. Two-perfection makes the first case trivial.

For the cubic case, a normal two-subgroup Q normalizes every subnormal
two-perfect subgroup E. A cubic element of E therefore has [Q, x] inside E.
A lower bound on these concrete commutators gives the strict lower bound
on E, separately from the quotient-order calculation.

Source application: Aschbacher--Smith 2.3.9(7), printed p.526, for the Held
seed normalizer; the relative subnormal step is A.4.2(2), printed p.57.
No local order, quotient identification or finite certificate is asserted here.
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The intrinsic quotient embeds into the two-residual's intrinsic core quotient. -/
theorem core_quotient_card_dvd_residual_core_quotient (E : Subgroup G)
    (hE : E.IsSubnormal) (hp : IsPPerfect 2 E) :
    Nat.card (E ⧸ pCore 2 E) ∣
      Nat.card (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) := by
  let D := pResidual 2 G
  let F := E.subgroupOf D
  let e : F ≃* E := subgroupOfEquivOfLe (le_pResidual_of_isPPerfect E hp)
  have hF : F.IsSubnormal := hE.subgroupOf
  let eq := QuotientGroup.congr (pCore 2 F) (pCore 2 E) e (pCore_map_iso 2 e)
  rw [← Nat.card_congr eq.toEquiv, Nat.card_congr (hF.quotientCoreImageEquiv 2).toEquiv]
  exact card_subgroup_dvd_card _

/-- A two-perfect two-group is trivial, expressed through its core quotient. -/
theorem card_eq_one_of_isPPerfect_of_core_quotient_card_one
    (hp : IsPPerfect 2 G) (hq : Nat.card (G ⧸ pCore 2 G) = 1) :
    Nat.card G = 1 := by
  have hc : Nat.card G = Nat.card (pCore 2 G) := by
    simpa only [hq, one_mul] using card_eq_card_quotient_mul_card_subgroup (pCore 2 G)
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
  have hg : IsPGroup 2 G := IsPGroup.of_card (hc.trans hn)
  have hi := hp.hom_eq_one_of_isPGroup hg (MonoidHom.id G)
  have : Subsingleton G := ⟨fun x y => by
    have hx : x = 1 := DFunLike.congr_fun hi x
    have hy : y = 1 := DFunLike.congr_fun hi y
    exact hx.trans hy.symm⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

/-- Cauchy and relative subnormality turn cubic commutator bounds into a subgroup bound. -/
theorem twelve_lt_card_of_subnormal_cubic_commutators
    (Q E : Subgroup G) [Q.Normal] (hQ : IsPGroup 2 Q)
    (hcubic : ∀ x : G, orderOf x = 3 → 12 < Nat.card (⁅Q, zpowers x⁆ : Subgroup G))
    (hE : E.IsSubnormal) (hp : IsPPerfect 2 E) (hthree : 3 ∣ Nat.card E) :
    12 < Nat.card E := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := E) 3 hthree
  have hxG : orderOf (x : G) = 3 :=
    (orderOf_injective E.subtype E.subtype_injective x).trans hx
  have hn : Q ≤ normalizer E := le_normalizer_of_isSubnormal_isPPerfect E Q hE hp hQ
    (by rw [normalizer_eq_top]; exact le_top)
  have hcomm : ⁅Q, zpowers (x : G)⁆ ≤ E :=
    (commutator_mono le_rfl (zpowers_le.mpr x.property)).trans
      (le_normalizer_iff_commutator_le_right.mp hn)
  exact (hcubic x hxG).trans_le
    (Nat.card_le_card_of_injective (inclusion hcomm) (inclusion_injective hcomm))

/-- The two independent local calculations suffice for the full order trichotomy. -/
theorem subnormal_orders_of_residual_nine_of_cubic_commutators
    (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup 2 Q)
    (hnine : Nat.card (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) = 9)
    (hcubic : ∀ x : G, orderOf x = 3 → 12 < Nat.card (⁅Q, zpowers x⁆ : Subgroup G))
    (E : Subgroup G) (hE : E.IsSubnormal) (hp : IsPPerfect 2 E) :
    Nat.card E = 1 ∨
      (Nat.card (E ⧸ pCore 2 E) = 3 ∧ 12 < Nat.card E) ∨
        Nat.card (E ⧸ pCore 2 E) = 9 := by
  have hd := core_quotient_card_dvd_residual_core_quotient E hE hp
  rw [hnine] at hd
  obtain ⟨n, hn, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (show Nat.card (E ⧸ pCore 2 E) ∣ 3 ^ 2 from hd)
  interval_cases n
  · exact Or.inl (card_eq_one_of_isPPerfect_of_core_quotient_card_one hp he)
  · right; left
    have hthree : Nat.card (E ⧸ pCore 2 E) = 3 := he
    refine ⟨hthree, twelve_lt_card_of_subnormal_cubic_commutators Q E hQ hcubic hE hp ?_⟩
    rw [← hthree]
    exact (pCore 2 E).card_quotient_dvd_card
  · exact Or.inr (Or.inr he)

end Theory.GroupTheory
