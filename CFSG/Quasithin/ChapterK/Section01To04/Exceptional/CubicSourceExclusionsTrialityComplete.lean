module
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.CubicSourceExclusionsTrialityShort
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.CubicSourceExclusionsTrialityGeometry

/-!
# Complete triality exclusion on the original cubic source domain

Outer involutions move more than 10r binary dimensions, and inner short-root
involutions move at least 11r. Hence every actor of ratio at most two lies
inside the original component and avoids the short-root class. The concrete
radical count bounds such an actor by q². Its allowed displacement is then
at most 4r, contradicting the strict 5r bound for every inner involution.

All tensor, period, cover, and group-geometric premises are discharged. The
proof retains every positive exponent, the original representation, arbitrary
central covers and ambient actors. Source: Aschbacher--Smith K.3, printed
p.457/PDF468, citing GM04 Theorem 8.1/Table 17; GM04 Lemma 8.6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Triality.Standard
namespace CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions
universe u v
variable {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- Triality is excluded from the exact cubic source domain, including q=2. -/
theorem triality_cubic_source_false (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {n : ℕ} (hn : 1≤n)
    (hm : IsTrialityGroupAt (2^n) (L ⧸ center L)) : False := by
  obtain ⟨A,hA,_,hAL,_,hsmall⟩ := triality_source_inner_actor h hn hm
  obtain ⟨e,e₀,he⟩ := triality_source_model_equiv h hn hm
  let := hA.2
  let A0 := A.subgroupOf L
  let : IsElementaryAbelian 2 A0 := IsElementaryAbelian.subgroupOf hAL
  let B := A0.map e.toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map e.toMonoidHom
  have hno := triality_small_actor_no_short h hn hm e A hA hsmall
  have hB : Nat.card B ≤ 2^(2*n) := by
    apply TrialityGeometry.no_short_card_le n hn B
    rintro _ ⟨t,ht,rfl⟩
    exact hno t ht
  have he0 : Nat.card A0 = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
  have heB : Nat.card A0 = Nat.card B :=
    Nat.card_congr (A0.equivMapOfInjective e.toMonoidHom e.injective).toEquiv
  rw [←heB,he0] at hB
  have hr : rank A ≤ 2*n := by
    simpa only [rank,Nat.log_pow Nat.one_lt_two] using Nat.log_mono_right (b:=2) hB
  obtain ⟨t,ht,hne⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  let tL : L := ⟨t,hAL ht⟩
  have ht2 : tL^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian t ht)
  have ht1 : tL≠1 := fun hh => hne (congrArg Subtype.val hh)
  have ho : orderOf tL=2 := orderOf_eq_prime ht2 ht1
  have hd := (triality_source_inner_displacement h hn e tL ho).1
  have hmono := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr ht))
  have hdt := fixedCodim_add_finrank ρ (zpowers t)
  have hdA := fixedCodim_add_finrank ρ A
  change 5*n < fixedCodim ρ (zpowers t) at hd
  omega
end CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions
