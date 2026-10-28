module

public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.PrimaryRadical
public import Theory.GroupTheory.PResidual.SubnormalNineQuotient

/-!
# The elementary and absent-prime cases of the original primary radical

If I_p/O₂(I_p) has exponent p, its whole image lies in Ω₁(O_p(L/O₂L)).
Two-perfectness therefore puts I_p inside the defining residual Ξ_p(L).
The reverse inclusion was already proved. If p does not divide the
Fitting subgroup of L/O₂(L), the primary radical has trivial quotient
and two-perfectness makes the radical itself trivial.
Source: Aschbacher--Smith 3.2.14, p.585.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3.RadicalCentralization
open Chapter1
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Exponent p in the actual primary quotient gives containment in the
original canonical radical, without a model replacement. -/
theorem primaryRadical_le_XiP_of_exponent
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hexp : ∀ x : primaryRadical p L ⧸ pCore 2 (primaryRadical p L), x ^ p = 1) :
    primaryRadical p L ≤ XiP p L := by
  let e := primaryRadicalQuotientEquiv hG T hL ho
  let P := (xiPPreimage p L).map L.subtype
  have hIP : primaryRadical p L ≤ P := by
    intro x hx
    let a : primaryRadical p L := ⟨x,hx⟩
    let z : pCore p (XiQuotient L) := e (QuotientGroup.mk' _ a)
    have hp : z ^ p = 1 := by
      change (e (QuotientGroup.mk' _ a)) ^ p = 1
      rw [← map_pow,hexp,map_one]
    have hz : (z : XiQuotient L) ∈ xiOmegaCore p L :=
      mem_map_of_mem (pCore p (XiQuotient L)).subtype
        (subset_closure (by simpa only [Set.mem_ofPred_eq,pow_one] using hp))
    have hz' : QuotientGroup.mk' (pCore 2 L) (inclusion (map_subtype_le _) a) ∈
        xiOmegaCore p L := by
      rwa [show (z : XiQuotient L) = _ from primaryRadicalQuotientEquiv_apply_mk hG T hL ho a] at hz
    exact ⟨inclusion (map_subtype_le _) a,hz',rfl⟩
  have hm := embedded_pResidual_mono 2 hIP
  rw [(pResidual_eq_top_iff 2 (primaryRadical p L)).mpr
    (primaryRadical_twoPerfect L ho),← MonoidHom.range_eq_map,range_subtype] at hm
  have he : (pResidual 2 P).map P.subtype = XiP p L := by
    rw [← map_embedded_pResidual 2 (xiPPreimage p L) L.subtype]
    rfl
  exact hm.trans_eq he

/-- An absent odd Fitting prime has trivial actual primary radical. -/
theorem primaryRadical_eq_bot_of_not_dvd
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : ¬ p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    primaryRadical p L = ⊥ := by
  have hc : Nat.card (pCore p (XiQuotient L)) = 1 :=
    (pCore_isPGroup (p := p) (G := XiQuotient L)).card_eq_or_dvd.resolve_right
      (fun hh => hd (hh.trans (card_dvd_of_le (pCore_le_fitting _ p))))
  have hq : Nat.card (primaryRadical p L ⧸ pCore 2 (primaryRadical p L)) = 1 :=
    (Nat.card_congr (primaryRadicalQuotientEquiv hG T hL ho).toEquiv).trans hc
  exact Subgroup.card_eq_one.mp
    (card_eq_one_of_isPPerfect_of_core_quotient_card_one (primaryRadical_twoPerfect L ho) hq)

end CFSG.Quasithin.Chapter3.RadicalCentralization
