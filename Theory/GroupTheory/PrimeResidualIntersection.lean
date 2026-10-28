module
public import Theory.GroupTheory.PResidual.Restriction
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.Quotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
/-!
# Residuals in proper subgroups above a Sylow subgroup

When the p-residual of a finite group has prime order, a proper subgroup
containing a Sylow p-subgroup meets that residual trivially. Otherwise the
prime-order subgroup lies in the overgroup, and the residual/Sylow supplement
generates the whole group. Consequently the proper overgroup is a p-group.

Apply this observation modulo a normal subgroup N contained in H. If H is
proper and contains an ambient Sylow p-subgroup, and Oᵖ(G/N) has prime order,
then the embedded residuals Oᵖ(H) and Oᵖ(N) are equal. The last theorem
retains all subgroup embeddings inside a larger ambient group.

Source application: Aschbacher–Smith 15.1.18(2), printed p.1092.
-/
public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A proper overgroup of a Sylow subgroup avoids the prime-order residual. -/
theorem prime_residual_inf_eq_bot {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (hH : H ≠ ⊤) (hprime : (Nat.card (pResidual p G)).Prime) :
    pResidual p G ⊓ H = ⊥ := by
  let R := pResidual p G
  let : Fact (Nat.card R).Prime := ⟨hprime⟩
  rcases (H.subgroupOf R).eq_bot_or_eq_top_of_prime_card with hb | ht
  · have hh := congrArg (map R.subtype) hb
    simpa only [subgroupOf_map_subtype,map_bot,inf_comm] using hh
  · apply (hH ?_).elim
    apply top_unique
    rw [←pResidual_sup_sylow_eq_top S]
    refine sup_le ?_ hSH
    intro r hr
    exact show (⟨r,hr⟩ : R) ∈ H.subgroupOf R from ht ▸ mem_top _

/-- Such a proper overgroup is itself a p-group. -/
theorem isPGroup_of_prime_residual_of_sylow_le {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (hH : H ≠ ⊤) (hprime : (Nat.card (pResidual p G)).Prime) : IsPGroup p H := by
  let f := (QuotientGroup.mk' (pResidual p G)).comp H.subtype
  apply (isPGroup_quotient_pResidual p).of_injective f
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro h hh
  apply mem_bot.mpr
  apply Subtype.ext
  have hr : (h:G) ∈ pResidual p G := (QuotientGroup.eq_one_iff (h:G)).mp hh
  have hh' : (h:G) ∈ pResidual p G ⊓ H := ⟨hr,h.property⟩
  rw [prime_residual_inf_eq_bot S H hSH hH hprime] at hh'
  exact hh'

/-- Modulo a normal subgroup, a prime-order residual forces equality of the
original embedded residuals. -/
theorem embedded_pResidual_eq_of_prime_quotient_residual {p : ℕ} [Fact p.Prime]
    (N H : Subgroup G) [N.Normal] (hNH : N ≤ H)
    (S : Sylow p G) (hSH : (S : Subgroup G) ≤ H) (hH : H ≠ ⊤)
    (hprime : (Nat.card (pResidual p (G ⧸ N))).Prime) :
    (pResidual p H).map H.subtype = (pResidual p N).map N.subtype := by
  let q := QuotientGroup.mk' N
  have hHbar : H.map q ≠ ⊤ := by
    intro hh
    have h := congrArg (comap q) hh
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hNH,comap_top] at h
    exact hH h
  have hp : IsPGroup p (H.map q) := isPGroup_of_prime_residual_of_sylow_le
    (S.mapSurjective (QuotientGroup.mk'_surjective N)) (H.map q)
    (map_mono hSH) hHbar hprime
  apply (embedded_pResidual_eq_of_le_of_residual_le p hNH ?_).symm
  rintro _ ⟨h,hh,rfl⟩
  have hr := pResidual_le_ker_of_isPGroup p (q.subgroupMap H) hp hh
  exact (QuotientGroup.eq_one_iff (h:G)).mp (congrArg Subtype.val hr)

/-- The residual identity with all three subgroups embedded in one ambient group. -/
theorem embedded_pResidual_intersection_of_prime_quotient_residual
    {p : ℕ} [Fact p.Prime] (K N H : Subgroup G) (hNK : N ≤ K) (hNH : N ≤ H)
    (hHK : H ≤ K) [(N.subgroupOf K).Normal]
    (S : Sylow p K) (hSH : (S : Subgroup K).map K.subtype ≤ H) (hH : H ≠ K)
    (hprime : (Nat.card (pResidual p (K ⧸ N.subgroupOf K))).Prime) :
    (pResidual p H).map H.subtype = (pResidual p N).map N.subtype := by
  have h := embedded_pResidual_eq_of_prime_quotient_residual (N.subgroupOf K) (H.subgroupOf K)
    (fun x hx => hNH hx) S
    (fun x hx => hSH (mem_map_of_mem K.subtype hx))
    (by intro hh; apply hH; have hm := congrArg (map K.subtype) hh
        rw [map_subgroupOf_eq_of_le hHK,←MonoidHom.range_eq_map,range_subtype] at hm
        exact hm) hprime
  have hm := congrArg (map K.subtype) h
  rw [map_embedded_pResidual,map_embedded_pResidual,
    map_subgroupOf_eq_of_le hHK,map_subgroupOf_eq_of_le hNK] at hm
  exact hm
end Subgroup
