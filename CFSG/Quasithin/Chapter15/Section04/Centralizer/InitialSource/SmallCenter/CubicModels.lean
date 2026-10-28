module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SmallCenter.CubicFaithfulness
public import Theory.SpecificGroups.Alternating.FourPairAutomorphisms
public import GorensteinWalter.AutAlternatingFour
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Recognition of the original small-center maximal local

A normal A₄ or A₄ × A₄ subgroup has trivial centralizer by the original
order-two omega center and characteristic two. Conjugation embeds M in
S₄ or S₄ wr C₂ using the proved full automorphism groups. The original
quotient order 6^s s! and inherited four- or sixteen-element two-core
force the full image. In the pair case its cubic quotient of order nine
rules out s=1. Thus both local models are constructed from the source data.

Source: Aschbacher--Smith 15.4.7, printed p.1158.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
open FamilySource FamilySource.ModuleStructure
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem faithful_equiv_of_card_bound {H A B : Type*} [Group H] [Finite H] [Group A] [Group B]
    [Finite A] [Finite B] (N : Subgroup H) [N.Normal]
    (hc : centralizer (N : Set H) = ⊥) (a : N ≃* A) (b : MulAut A ≃* B)
    (hcard : Nat.card B ≤ Nat.card H) : Nonempty (H ≃* B) := by
  let f := b.toMonoidHom.comp ((MulAut.congr a).toMonoidHom.comp
    (MulAut.conjNormal : H →* MulAut N))
  have hf : Function.Injective f := b.injective.comp
    ((MulAut.congr a).injective.comp (MulAut.conjNormal_injective_of_centralizer_eq_bot N hc))
  exact ⟨MulEquiv.ofBijective f (hf.bijective_of_nat_card_le hcard)⟩

/-- Faithfulness and the original core quotient force the literal S₄ or wreath model. -/
theorem member_models_of_normal_models {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input KnownSimple.IsKnownSimple T M X s)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (N : Subgroup M) (hn : N.Normal)
    (hmodel : Nonempty (N ≃* alternatingGroup (Fin 4)) ∨ Nonempty (N ≃* AlternatingFourPair.Model)) :
    Nonempty (M ≃* Equiv.Perm (Fin 4)) ∨
    Nonempty (M ≃* RegularWreathProduct (Equiv.Perm (Fin 4)) (Multiplicative (ZMod 2))) := by
  let : N.Normal := hn
  have hcQ := core_quotient_card h hZ
  have hcore (d : ℕ) (hd : Nat.card (pCore 2 N) = d) : d ≤ Nat.card (pCore 2 M) := by
    have hh := card_le_of_le (pCoreIn_le_of_subnormal 2 hn.isSubnormal)
    rw [pCoreIn,card_map_of_injective N.subtype_injective,hd] at hh
    exact hh
  have hMcard := card_eq_card_quotient_mul_card_subgroup (pCore 2 M)
  rcases hmodel with hmodel | hmodel
  · obtain ⟨a⟩ := hmodel
    have hcN : Nat.card (pCore 2 N) = 4 := by
      rw [←card_map_of_injective (K := pCore 2 N) (f := a.toMonoidHom) a.injective,pCore_map_iso,AlternatingFourPair.twoCore_eq_kleinFour]
      exact alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num)
    have hNcard : Nat.card N = 12 := by
      rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      rfl
    have hne : N ≠ ⊥ := by intro he; rw [he,card_bot] at hNcard; omega
    have hz : center N = ⊥ := by
      apply card_eq_one.mp
      rw [Nat.card_congr (centerCongr a).toEquiv,
        alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 4)),card_bot]
    have hc := member_normal_centerless_centralizer h hZ N hn hne hz
    let b : MulAut (alternatingGroup (Fin 4)) ≃* Equiv.Perm (Fin 4) :=
      (MulEquiv.ofBijective (MulAut.conjNormal : Equiv.Perm (Fin 4) →* MulAut (alternatingGroup (Fin 4)))
        GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj).symm
    apply Or.inl
    apply faithful_equiv_of_card_bound N hc a b
    have h4 := hcore 4 hcN
    have hq : 6 ≤ Nat.card (M ⧸ pCore 2 M) := by
      change 6 ≤ Nat.card (CoreQuotient M)
      rw [hcQ]
      rcases h.parameter with hs | hs <;> rw [hs] <;> norm_num
    have h24 : 24 ≤ Nat.card M := by nlinarith
    simpa [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] using h24
  · obtain ⟨a⟩ := hmodel
    have hcN : Nat.card (pCore 2 N) = 16 := by
      rw [←card_map_of_injective (K := pCore 2 N) (f := a.toMonoidHom) a.injective,pCore_map_iso]
      exact AlternatingFourPair.card_twoCore
    have hNcard : Nat.card N = 144 := by
      rw [Nat.card_congr a.toEquiv]
      change Nat.card (alternatingGroup (Fin 4) × alternatingGroup (Fin 4)) = 144
      rw [Nat.card_prod,nat_card_alternatingGroup,Nat.card_fin]
      rfl
    have hne : N ≠ ⊥ := by intro he; rw [he,card_bot] at hNcard; omega
    have hz : center N = ⊥ := by
      apply card_eq_one.mp
      rw [Nat.card_congr (centerCongr a).toEquiv,AlternatingFourPair.center_eq_bot,card_bot]
    have hc := member_normal_centerless_centralizer h hZ N hn hne hz
    have hqN : Nat.card (N ⧸ pCore 2 N) = 9 := by
      have hh := card_eq_card_quotient_mul_card_subgroup (pCore 2 N)
      rw [hcN,hNcard] at hh
      omega
    have hiN : Nat.card (N.map (quotientMap M)) = 9 := by
      exact (Nat.card_congr (ChapterC.BlockCommutation.coreQuotientEquiv N hn.isSubnormal).toEquiv).symm.trans hqN
    have hd9 : 9 ∣ Nat.card (CoreQuotient M) := by
      have hh := (N.map (quotientMap M)).card_subgroup_dvd_card
      rwa [hiN] at hh
    have hq : Nat.card (M ⧸ pCore 2 M) = 72 := by
      change Nat.card (CoreQuotient M) = 72
      rw [hcQ] at hd9 ⊢
      rcases h.parameter with hs | hs
      · rw [hs] at hd9
        norm_num at hd9
      · rw [hs]; norm_num
    apply Or.inr
    apply faithful_equiv_of_card_bound N hc a AlternatingFourPair.mulAut_equiv_regularWreath
    rw [AlternatingFourPair.symmetric_wreath_card]
    have h16 := hcore 16 hcN
    rw [hq] at hMcard
    nlinarith
end CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
