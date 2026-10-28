module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.PairedComponent
public import Theory.SpecificGroups.SL2.OddAbelianSubgroups
/-!
# Full Hall intersections in the selected general-field component

Restrict the prescribed odd Hall to `K ∩ M`, using its proved normalization
of K. The actual Baumann normalizer supplies the divisor `q - 1` in that
intersection. Conversely, its odd Hall injects into `K/O₂(K) ≃ SL₂(q)`;
the full Hall order `(q - 1)^2` cancels the relatively prime factors
`q(q + 1)` in the SL₂ order. Thus the same `B ∩ K` is cyclic of order
`q - 1`. The final application retains the selected component, marked
quotient, block alternative and alpha fixed subgroup.

Natural marking and original Borel placement remain inputs discharged by
this task's final moving-Hall assembly. Source: Aschbacher–Smith 10.2.3(4),
printed pp.746–747.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {B : Subgroup H}

private theorem odd_dvd_hall {X : Type*} [Group X] (C : Subgroup X)
    (hC : IsHallSubgroup Subgroup.OddHall.oddPrimes C) {m : ℕ} (hm : Odd m)
    (hd : m ∣ Nat.card X) : m ∣ Nat.card C := by
  have hc : Nat.Coprime m C.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpm hpi
    exact hC.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hpi
      (show p ≠ 2 from fun he => hm.not_two_dvd_nat (he ▸ hpm))
  rw [←C.index_mul_card] at hd
  exact hc.dvd_of_dvd_mul_left hd

private theorem card_dvd_torus {X F : Type*} [Group X] [Finite X]
    [Field F] [Finite F] (hf : Even (Nat.card F))
    (r : X →* SL(2,F)) (hi : Function.Injective r)
    (hd : Nat.card X ∣ (Nat.card F - 1)^2) : Nat.card X ∣ Nat.card F - 1 := by
  have hq : 1 ≤ Nat.card F := (Finite.one_lt_card (α := F)).le
  have hc₁ : Nat.Coprime (Nat.card F - 1) (Nat.card F) :=
    (Nat.coprime_self_sub_left hq).mpr (Nat.coprime_one_left _)
  have ho : Odd (Nat.card F - 1) := Nat.Even.sub_odd hq hf odd_one
  have hc₂ : Nat.Coprime (Nat.card F - 1) (Nat.card F + 1) := by
    rw [show Nat.card F + 1 = 2 + (Nat.card F - 1) by omega,
      Nat.coprime_add_self_right]
    exact ho.coprime_two_right
  have hc := ((hc₁.mul_right hc₂).pow_left 2).of_dvd_left hd
  have hcard := card_dvd_of_injective r hi
  rw [BenderSuzuki.External.huppert614_card_specialLinearGroup] at hcard
  have he : Nat.card F * (Nat.card F ^ 2 - 1) =
      (Nat.card F * (Nat.card F + 1)) * (Nat.card F - 1) := by
    have hsub := Nat.sub_add_cancel hq
    have hsq := Nat.sub_add_cancel (show 1 ≤ Nat.card F ^ 2 by nlinarith)
    nlinarith
  rw [he] at hcard
  exact hc.dvd_of_dvd_mul_left hcard

/-- Restrict the prescribed Hall to the same comparison component. -/
theorem Context.component_hall_card_and_cyclic
    (ctx : Context D H B)
    {F E : Type} [Field F] [Finite F] [CharP F 2]
    [Field E] [Finite E] [CharP E 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L)
    (K : Subgroup H) (hE : Nat.card E = Nat.card F)
    (eK : (K ⧸ pCore 2 K) ≃* SL(2,E))
    (hBN : B ≤ normalizer (K : Set H))
    (hdiv : Nat.card F - 1 ∣ Nat.card (K ⊓
      normalizer (baumann (T.subtype ctx.hstar.1.1.2 : Subgroup H) : Set H) : Subgroup H)) :
    Nat.card (B ⊓ K : Subgroup H) = Nat.card F - 1 ∧ IsCyclic (B ⊓ K : Subgroup H) := by
  let S := T.subtype ctx.hstar.1.1.2
  let M := D.maximalLocal.subgroupOf H
  let N := K ⊓ M
  have hNm : normalizer (baumann (S : Subgroup H) : Set H) ≤ M := by
    intro x hx
    apply ctx.original_baumann_normalizer_le D n hn hF e
    have hmap : (baumann (S : Subgroup H)).map H.subtype = baumann (T : Subgroup G) := by
      have hh := baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
      change (baumann (S : Subgroup H)).map H.subtype = baumann ((S : Subgroup H).map H.subtype) at hh
      rw [show (S : Subgroup H).map H.subtype = (T : Subgroup G) from
        map_subgroupOf_eq_of_le ctx.hstar.1.1.2] at hh
      exact hh
    have hh := (baumann (S : Subgroup H)).le_normalizer_map H.subtype (mem_map_of_mem H.subtype hx)
    rwa [hmap] at hh
  have hBN' : B ≤ normalizer (N : Set H) :=
    (le_inf hBN (ctx.hall_le.trans M.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hhall := Subgroup.OddHall.hall_restrict_of_normalizes ctx.hall ctx.hall_le
    (show N ≤ M from inf_le_right) hBN'
  have ho : Odd (Nat.card F - 1) := Nat.Even.sub_odd
    (Finite.one_lt_card (α := F)).le
    (hF.symm ▸ even_two.pow_of_ne_zero (by omega : n ≠ 0)) odd_one
  have hlow := odd_dvd_hall _ hhall ho
    (hdiv.trans (card_dvd_of_le (inf_le_inf_left K hNm)))
  have hBNcard : Nat.card (B.subgroupOf N) = Nat.card (B ⊓ K : Subgroup H) := by
    rw [←inf_subgroupOf_right B N, Nat.card_congr (subgroupOfEquivOfLe
      (show B ⊓ N ≤ N from inf_le_right)).toEquiv]
    have he : B ⊓ N = B ⊓ K :=
      (inf_assoc B K M).symm.trans (inf_eq_left.mpr (inf_le_left.trans ctx.hall_le))
    rw [he]
  rw [hBNcard] at hlow
  let A := B ⊓ K
  have hodd : Odd (Nat.card A) := ctx.hall_odd.of_dvd_nat (card_dvd_of_le (show A ≤ B from inf_le_left))
  let r : A →* SL(2,E) := eK.toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 K)).comp (inclusion (show A ≤ K from inf_le_right)))
  have hi : Function.Injective r := by
    apply (MonoidHom.ker_eq_bot_iff r).mp
    apply eq_bot_of_card_eq
    have hp : IsPGroup 2 r.ker := by
      have he : r.ker = (pCore 2 K).comap (inclusion (show A ≤ K from inf_le_right)) := by
        ext x
        change eK (QuotientGroup.mk' _ _) = 1 ↔ _
        rw [eK.map_eq_one_iff]
        exact QuotientGroup.eq_one_iff _
      rw [he]
      exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
    exact hp.card_eq_or_dvd.resolve_right
      (hodd.of_dvd_nat (card_subgroup_dvd_card r.ker)).not_two_dvd_nat
  have hsquare : Nat.card A ∣ (Nat.card E - 1)^2 := by
    rw [hE,←ctx.hall_card_eq_torus_square D n hn hF e mark hBB]
    exact card_dvd_of_le inf_le_left
  have heven : Even (Nat.card E) := by
    rw [hE,hF]
    exact even_two.pow_of_ne_zero (by omega : n ≠ 0)
  have hupp := card_dvd_torus heven r hi hsquare
  rw [hE] at hupp
  let := ctx.abelian
  let : IsMulCommutative A := ⟨⟨fun x y =>
    (inclusion_injective (show A ≤ B from inf_le_left)) (by
      simp only [map_mul,mul_comm])⟩⟩
  exact ⟨Nat.dvd_antisymm hupp hlow, Matrix.SL2.odd_abelian_isCyclic_of_injective hodd r hi⟩
open Representation Representation.BinaryOffender
open ChapterE.ThompsonAction ChapterB.SourceInduction ChapterB.QuasisimpleSource
open ChapterC.RankOne.ChiProduct.SelectedRankOne ChapterC.GlaubermanNiles
set_option backward.isDefEq.respectTransparency false in
/-- The selected paired comparison now includes the full original Hall intersection. -/
theorem Context.paired_component_with_full_hall
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L) :
    let S := T.subtype ctx.hstar.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    letI := (source_hstar_omega_orbit_reduced D ctx.hstar).normal
    letI := (source_hstar_omega_orbit_reduced D ctx.hstar).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    let B₀ := baumann (S : Subgroup H)
    letI := offenderSubgroup_normal α
    ∃ (d : SourceTwoFactorCase (α.comp Y.subtype)) (E : BinaryField),
      Nat.card E.Carrier = Nat.card F ∧ Nonempty (d.MarkedProduct (linearNatural E 2)) ∧
      ∃ K : Subgroup H, K.IsCComponent ∧ K.map q = d.first.map Y.subtype ∧
        (solvableResidual (RankOneBaumann.PairedFactorOrbit.factorPreimage q Y d.first)).map
          (RankOneBaumann.PairedFactorOrbit.factorPreimage q Y d.first).subtype = K ∧
        U ≤ normalizer (K : Set H) ∧ B₀ ≤ normalizer (K : Set H) ∧
        InLocalClass (inclusion (show B₀ ≤ K ⊔ B₀ from le_sup_right)) ∧
        (localV (inclusion (show B₀ ≤ K ⊔ B₀ from le_sup_right))).map (K ⊔ B₀).subtype =
          (⁅U,K⁆ : Subgroup H) ⊔ (thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H)) ∧
        thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H) ≠ ⊥ ∧
        Nonempty ((K ⧸ pCore 2 K) ≃* SL(2,E.Carrier)) ∧ K ⊔ (S : Subgroup H) = ⊤ ∧
        (∃ t ∈ (S : Subgroup H), pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom) ∧
        Nat.card F - 1 ∣ Nat.card (K ⊓ normalizer (B₀ : Set H) : Subgroup H) ∧
        Nat.card (B ⊓ K : Subgroup H) = Nat.card F - 1 ∧
        IsCyclic (B ⊓ K : Subgroup H) ∧
        B ≤ normalizer (K : Set H) ∧
        (∀ t : H, B ≤ normalizer (K.map (MulAut.conj t).toMonoidHom : Set H)) ∧
        (ChapterC.IsBlock (L.subgroupOf (localJoin T L)) ∨
          (ChapterC.IsBlock K ∧ ∃ m, ChapterC.IsL2EvenBlock K m)) ∧
        ∃ E' : BinaryField,
          letI : Algebra (ZMod 2) E'.Carrier := ZMod.algebra _ 2
          ∃ (q₁ q₂ : localOrbit T L →* SL(2,E'.Carrier)),
            Nonempty (BinaryConjugationSection (localOrbit T L) D.moduleSubgroup
              (D.moduleSubgroup ⊓ centralizer (localOrbit T L : Set G))
              (Representation.prod (SL2.BinarySmall.natural.comp q₁)
                (SL2.BinarySmall.natural.comp q₂))) ∧
            ((B ⊓ K).map H.subtype ≤ q₁.ker.map (localOrbit T L).subtype ∨
              (B ⊓ K).map H.subtype ≤ q₂.ker.map (localOrbit T L).subtype) := by
  obtain ⟨d,E,hE,hmarked,K,hK,hi,hcan,hUK,hBK,hlocal,hv,hfixed,heq,hgen,hcover,
    hdiv,hBN,hBNt,hblock,haxis⟩ := ctx.paired_component_and_block D n hn hF e mark hBB
  obtain ⟨hcard,hcyclic⟩ := ctx.component_hall_card_and_cyclic D n hn hF e mark hBB
    K hE heq.some hBN hdiv
  exact ⟨d,E,hE,hmarked,K,hK,hi,hcan,hUK,hBK,hlocal,hv,hfixed,heq,hgen,hcover,
    hdiv,hcard,hcyclic,hBN,hBNt,hblock,haxis⟩

end CFSG.Quasithin.Chapter10.MovingHall
