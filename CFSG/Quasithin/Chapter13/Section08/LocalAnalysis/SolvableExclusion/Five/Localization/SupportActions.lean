module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.FactorData
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Supports
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.FiveCentralizer
public import Theory.GroupAction.IndependentCoprimeSupports
public import Theory.GroupAction.NormalizingActor
public import Theory.ElementaryAbelian.Basic

/-!
# Restricting the five-factors to their actual supports

Coprime splitting makes a five-factor faithful on its own moved subgroup.
We construct the restriction from its normalizer, retaining its evaluation
formula. On a support of order sixteen a commuting involution is therefore
trivial, whereas a normalizing actor that does not centralize the factor
must move a point of that support.

For the actual H/O₂(H)-action these statements prove fixation of the
canonical second lift modulo V₁, invariance of the summand under a
normalizing starred subgroup, and a moved-point witness. The factors and
the actor are the supplied actual subgroup images, not auxiliary models.
Existence of the second actor and the geometric bounds is not asserted.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951, the last two paragraphs. The restriction-faithfulness step
uses the coprime fixed/support decomposition; the commuting-involution
step uses the proved order-fifteen centralizer bound.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization
variable {W : Type*} [Group W]

def supportAction (P : Subgroup (MulAut W)) :
    normalizer (P : Set (MulAut W)) →* MulAut (commutatorAction P W) := by
  letI : IsInvariant (normalizer (P : Set (MulAut W))) W (commutatorAction P W) :=
    commutatorAction_isInvariant_of_normalizing_actor _ _ le_rfl
  exact MulDistribMulAction.toMulAut _ _

theorem supportAction_apply (P : Subgroup (MulAut W))
    (b : normalizer (P : Set (MulAut W))) (w : commutatorAction P W) :
    (supportAction P b w : W) = (b : MulAut W) w := rfl

def ownSupportAction (P : Subgroup (MulAut W)) :
    P →* MulAut (commutatorAction P W) :=
  (supportAction P).comp (inclusion le_normalizer)

theorem ownSupportAction_injective [Finite W] [IsMulCommutative W]
    (P : Subgroup (MulAut W))
    (hcop : Nat.Coprime (Nat.card P) (Nat.card W)) :
    Function.Injective (ownSupportAction P) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro p hp
  apply Subtype.ext
  apply ActionSupport.eq_one_of_fixes_support P hcop p
  intro w hw
  exact congrArg Subtype.val
    (DFunLike.congr_fun (show ownSupportAction P p = 1 from hp) ⟨w, hw⟩)

theorem ownSupportAction_range_card [Finite W] [IsMulCommutative W]
    (P : Subgroup (MulAut W))
    (hcop : Nat.Coprime (Nat.card P) (Nat.card W)) :
    Nat.card (ownSupportAction P).range = Nat.card P :=
  Nat.card_congr (MonoidHom.ofInjective (ownSupportAction_injective P hcop)).toEquiv.symm

theorem fixes_support_of_centralizes_five [Finite W] [IsMulCommutative W]
    (P : Subgroup (MulAut W)) (hP : Nat.card P = 5)
    (hcop : Nat.Coprime (Nat.card P) (Nat.card W))
    (hS : Nat.card (commutatorAction P W) = 16)
    (b : MulAut W) (hb : b ^ 2 = 1)
    (hc : b ∈ centralizer (P : Set (MulAut W))) :
    ∀ w ∈ commutatorAction P W, b w = w := by
  let bN : normalizer (P : Set (MulAut W)) :=
    ⟨b, centralizer_le_normalizer _ hc⟩
  have hbN : bN ^ 2 = 1 := Subtype.ext hb
  have hcard : Nat.card (ownSupportAction P).range = 5 :=
    (ownSupportAction_range_card P hcop).trans hP
  have hcentral : supportAction P bN ∈
      centralizer ((ownSupportAction P).range : Set (MulAut (commutatorAction P W))) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨p, rfl⟩
    have he : (inclusion le_normalizer p) * bN = bN * (inclusion le_normalizer p) :=
      Subtype.ext (mem_centralizer_iff.mp hc p p.property)
    exact congrArg (supportAction P) he |>.trans (by rw [map_mul]; rfl)
  have he := involution_eq_one_of_centralizes_five (ownSupportAction P).range
    hcard hS (supportAction P bN) (by rw [← map_pow, hbN, map_one]) hcentral
  intro w hw
  exact congrArg Subtype.val (DFunLike.congr_fun he ⟨w, hw⟩)

theorem moves_support_of_not_centralizes [Finite W] [IsMulCommutative W]
    (P : Subgroup (MulAut W))
    (hcop : Nat.Coprime (Nat.card P) (Nat.card W))
    (b : MulAut W) (hn : b ∈ normalizer (P : Set (MulAut W)))
    (hc : b ∉ centralizer (P : Set (MulAut W))) :
    ∃ w ∈ commutatorAction P W, b w ≠ w := by
  classical
  by_contra h
  push Not at h
  let bN : normalizer (P : Set (MulAut W)) := ⟨b, hn⟩
  have he : supportAction P bN = 1 := by
    ext w
    exact h w w.property
  apply hc
  apply mem_centralizer_iff.mpr
  intro p hp
  let pP : P := ⟨p, hp⟩
  let bp : P := ⟨b * p * b⁻¹, (mem_normalizer_iff.mp hn p).mp hp⟩
  have heq : ownSupportAction P bp = ownSupportAction P pP := by
    change supportAction P ((inclusion le_normalizer) bp) =
      supportAction P ((inclusion le_normalizer) pP)
    have helem : (inclusion le_normalizer) bp =
        bN * ((inclusion le_normalizer) pP) * bN⁻¹ := rfl
    rw [helem, map_mul, map_mul, map_inv, he, one_mul, inv_one, mul_one]
  have hcj : b * p * b⁻¹ = p :=
    congrArg Subtype.val (ownSupportAction_injective P hcop heq)
  have hh := congrArg (fun x : MulAut W => x * b) hcj
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh.symm

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization

namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
open CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization
variable {G : Type*} [Group G]
variable {H UH V₁ : Subgroup G} [(V₁.subgroupOf UH).Normal]

theorem StarAction.lift_commutator_le_denominator
    (a : StarAction H UH V₁) (B : Subgroup G) (hB : B ≤ H)
    (S : Subgroup (UH ⧸ V₁.subgroupOf UH))
    (hfixed : ∀ b : a.actors B, ∀ w ∈ S, b • w = w) :
    ⁅liftTilde UH V₁ S, B⁆ ≤ V₁ := by
  have hzero : commutatorSubgroup (a.actors B) (UH ⧸ V₁.subgroupOf UH) S = ⊥ := by
    apply bot_unique
    rw [commutatorSubgroup, closure_le]
    rintro _ ⟨b, w, hw, rfl⟩
    rw [hfixed b w hw, inv_mul_cancel]
    exact one_mem _
  have himage : tildeImage UH V₁ ⁅liftTilde UH V₁ S, B⁆ = ⊥ := by
    rw [← a.commutatorSubgroup_eq_tildeImage _ B (liftTilde_le UH V₁ S) hB,
      tildeImage_liftTilde, hzero]
  have hker : (⁅liftTilde UH V₁ S, B⁆).subgroupOf UH ≤ V₁.subgroupOf UH := by
    simpa only [tildeImage, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using himage
  have hU : ⁅liftTilde UH V₁ S, B⁆ ≤ UH :=
    (commutator_mono (liftTilde_le UH V₁ S) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hB.trans a.normalizes))
  intro x hx
  exact hker (show (⟨x, hU hx⟩ : UH) ∈ (⁅liftTilde UH V₁ S, B⁆).subgroupOf UH from hx)

theorem RankOneFactors.remaining_support_fixed [Finite G]
    [IsElementaryAbelian 2 (UH ⧸ V₁.subgroupOf UH)]
    (a : StarAction H UH V₁) (hf : Function.Injective a.action)
    {P Uγ : Subgroup G} (f : RankOneFactors a P Uγ)
    (i : Fin f.factors.count) (hi : i.val ≠ 0) :
    ∀ b : a.actors Uγ, ∀ w ∈ f.factors.support i, b • w = w := by
  have hcard : Nat.card (a.actors (f.factors.factor i)) = 5 :=
    (card_map_of_injective hf).trans (f.factors.star_card i)
  have hcop : Nat.Coprime (Nat.card (a.actors (f.factors.factor i)))
      (Nat.card (UH ⧸ V₁.subgroupOf UH)) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 (UH ⧸ V₁.subgroupOf UH)).exists_card_eq
    rw [hcard, hn]
    exact (by decide : Nat.Coprime 5 2).pow_right n
  have hcomm : ⁅a.actors Uγ, a.actors (f.factors.factor i)⁆ = ⊥ := by
    rw [StarAction.actors, StarAction.actors, ← map_commutator, f.remaining_fixed i hi, Subgroup.map_bot]
  intro b w hw
  have hb2 : (b : MulAut (UH ⧸ V₁.subgroupOf UH)) ^ 2 = 1 := by
    obtain ⟨c, hc, he⟩ := b.property
    have hc2 : c ^ 2 = 1 := by
      have hh := pow_card_eq_one' (x := (⟨c, hc⟩ : Source.starImage H Uγ))
      rw [f.actor_card] at hh
      exact congrArg Subtype.val hh
    rw [← he, ← map_pow, hc2, map_one]
  exact fixes_support_of_centralizes_five (a.actors (f.factors.factor i)) hcard hcop
    (f.factors.support_card i) b hb2
    ((commutator_eq_bot_iff_le_centralizer.mp hcomm) b.property) w hw

theorem RankOneFactors.remaining_lift_fixed [Finite G]
    [IsElementaryAbelian 2 (UH ⧸ V₁.subgroupOf UH)]
    (a : StarAction H UH V₁) (hf : Function.Injective a.action)
    {P Uγ : Subgroup G} (f : RankOneFactors a P Uγ) (hUγ : Uγ ≤ H)
    (i : Fin f.factors.count) (hi : i.val ≠ 0) :
    ⁅liftTilde UH V₁ (f.factors.support i), Uγ⁆ ≤ V₁ :=
  a.lift_commutator_le_denominator Uγ hUγ _ (f.remaining_support_fixed a hf i hi)

theorem Factorization.support_invariant
    (a : StarAction H UH V₁) {P : Subgroup G} (f : Factorization a P)
    (i : Fin f.count) (B : Subgroup G)
    (hn : Source.starImage H B ≤ normalizer (Source.starImage H (f.factor i) : Set _)) :
    ∀ b : a.actors B, ∀ w ∈ f.support i, b • w ∈ f.support i := by
  have hn' : a.actors B ≤ normalizer (a.actors (f.factor i) : Set _) :=
    (map_mono hn).trans (le_normalizer_map a.action)
  let : IsInvariant (a.actors B) (UH ⧸ V₁.subgroupOf UH) (f.support i) :=
    commutatorAction_isInvariant_of_normalizing_actor _ _ hn'
  intro b w hw
  exact (IsInvariant.invariant b w).mp hw

theorem Factorization.exists_moved_on_support [Finite G]
    [IsElementaryAbelian 2 (UH ⧸ V₁.subgroupOf UH)]
    (a : StarAction H UH V₁) (hf : Function.Injective a.action)
    {P : Subgroup G} (f : Factorization a P) (i : Fin f.count) (B : Subgroup G)
    (hn : Source.starImage H B ≤ normalizer (Source.starImage H (f.factor i) : Set _))
    (hm : ⁅Source.starImage H B, Source.starImage H (f.factor i)⁆ ≠ ⊥) :
    ∃ b : a.actors B, ∃ w ∈ f.support i, b • w ≠ w := by
  have hn' : a.actors B ≤ normalizer (a.actors (f.factor i) : Set _) :=
    (map_mono hn).trans (le_normalizer_map a.action)
  have hm' : ⁅a.actors B, a.actors (f.factor i)⁆ ≠ ⊥ := by
    intro he
    apply hm
    apply (map_injective hf)
    simpa only [map_commutator, Subgroup.map_bot, StarAction.actors] using he
  have hc : ¬ a.actors B ≤ centralizer (a.actors (f.factor i) : Set _) :=
    fun h => hm' (commutator_eq_bot_iff_le_centralizer.mpr h)
  obtain ⟨b, hb, hbc⟩ := SetLike.not_le_iff_exists.mp hc
  have hcard : Nat.card (a.actors (f.factor i)) = 5 :=
    (card_map_of_injective hf).trans (f.star_card i)
  have hcop : Nat.Coprime (Nat.card (a.actors (f.factor i)))
      (Nat.card (UH ⧸ V₁.subgroupOf UH)) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 (UH ⧸ V₁.subgroupOf UH)).exists_card_eq
    rw [hcard, hn]
    exact (by decide : Nat.Coprime 5 2).pow_right n
  obtain ⟨w, hw, hmoves⟩ := moves_support_of_not_centralizes
    (a.actors (f.factor i)) hcop b (hn' hb) hbc
  exact ⟨⟨b, hb⟩, w, hw, hmoves⟩

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five

end
