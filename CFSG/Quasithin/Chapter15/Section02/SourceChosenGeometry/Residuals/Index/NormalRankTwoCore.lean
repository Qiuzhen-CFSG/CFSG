module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.Cubic
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore
public import CFSG.Quasithin.ChapterD.Defs
public import Theory.GroupTheory.NormalRankTwoCoreControl
public import Theory.ElementaryAbelian.PrimeRankCard

/-!
# Equality-row control of the chosen two-module

When the partner span is the original residual, the residual subgroup inside
the partner is normal and has elementary quotient of order nine.  The general
normal rank-two core lemma then puts the local two-core containing the chosen
module inside the partner's ambient two-core.  This is the concrete equality
consumer needed before any prime-complement residual identity is invoked.

Source: Aschbacher--Smith 15.2.12(4), combined manuscript p.1111.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Chapter1 Chapter1.XiEmbedding Section01 Section03 Section03.InitialSource
open Chapter13.Section08.Components.Swapped.LinearThree
open ChapterD

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}

/-- In the equality row `Kc = K`, the selected module lies in `O₂(Mc)`.

The proof works inside `Mc`: the residual subgroup is normal there, its
two-core quotient is the elementary cubic base from the wreath input, and the
three-prime core normalizes the restricted chosen module through the preceding
three-core containment theorem.
-/
theorem ResidualInput.partner_core_le_twoCore_of_eq
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (he : partnerSpan H Mc = residual H) : V ≤ twoCoreIn Mc := by
  let hg : ChosenPlaneGeometry h H ⁅V, B⁆ := d.geometry_of_full d.full
  have hcore : (pPrimeCore 3 Mc).map Mc.subtype ≤ M ⊓ Mc :=
    source_chosen_threePrimeCore_le h hg hquotient
  have hKM : residual H ≤ Mc := (map_subtype_le _).trans hg.in_partner
  let K : Subgroup Mc := (residual H).subgroupOf Mc
  let eK : K ≃* residual H := subgroupOfEquivOfLe hKM
  let eQ := QuotientGroup.congr (pCore 2 K) (pCore 2 (residual H)) eK
    (pCore_map_iso 2 eK)
  let e := eQ.trans (residualQuotientEquiv H d.quotient.some)
  let : IsElementaryAbelian 3 (K ⧸ pCore 2 K) :=
    IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  have hKrank : primeRank 3 (K ⧸ pCore 2 K) = 2 := by
    rw [← IsElementaryAbelian.log_card_eq_primeRank (p := 3)]
    rw [Nat.card_congr e.toEquiv, WreathModel.cubicBase_card]
    decide
  have hMcrank : primeRank 3 Mc ≤ 2 := by
    exact (h.ambient.twoLocal_sqtk (partner_mem_overgroups h).1.1).stronglyQuasithin
      3 Nat.prime_three (by decide)
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (partner_normalizes_of_eq H Mc he)
  have hKH : K ≤ H.subgroupOf Mc := by
    intro x hx
    exact (map_subtype_le (pResidual 2 H)) hx
  have hVcore : V.subgroupOf Mc ≤ (H.subgroupOf Mc).pCoreIn 2 := by
    rw [pCoreIn_subgroupOf 2 H Mc hg.in_partner]
    intro x hx
    exact h.prepared.inside_core H d.outside hx
  have hVMc : V ≤ Mc :=
    (h.prepared.inside_core H d.outside).trans (pCoreIn_le 2 H) |>.trans hg.in_partner
  have hnorm : pPrimeCore 3 Mc ≤ normalizer (V.subgroupOf Mc : Set Mc) := by
    rw [← subgroupOf_normalizer_eq hVMc]
    intro x hx
    have hx' : (x : G) ∈ (pPrimeCore 3 Mc).map Mc.subtype :=
      mem_map_of_mem Mc.subtype hx
    exact h.prepared.normalized (hcore hx').1
  have hres := le_twoCore_of_normal_rank_two_section K (H.subgroupOf Mc)
    (V.subgroupOf Mc) hKH hMcrank hKrank hVcore hnorm
  change V ≤ pCoreIn 2 Mc
  have hmap := map_mono (f := Mc.subtype) hres
  simpa only [pCoreIn, map_subgroupOf_eq_of_le hVMc] using hmap

/- The equality-row core result also gives the strict residual inequality in
   the complementary (noncore) branch.  This is kept next to the equality
   proof so callers can split the actual `ResidualInput` without reopening
   the order-nine calculation. -/
theorem ResidualInput.noncore_residual_lt
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hne : ¬ V ≤ twoCoreIn Mc) : residual H < partnerSpan H Mc := by
  apply lt_of_le_of_ne (le_conjugateSpanBy _ _)
  intro he
  apply hne
  exact d.partner_core_le_twoCore_of_eq hquotient he.symm

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
