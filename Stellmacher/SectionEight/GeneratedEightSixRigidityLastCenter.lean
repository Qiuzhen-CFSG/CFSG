module

public import Stellmacher.SectionEight.GeneratedEightSixRigidityReduction

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_rigidity_le_first_center_of_le_initial
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (U : Subgroup G) (hUZ : U ≤ ZAt ctx.Γ ctx.criticalPath.a)
    (hUV : U ≤ Subgroup.centralizer (VAt ctx.Γ ctx.criticalPath.firstStep : Set G)) :
    U ≤ ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  let center := ZAt graph path.a
  let first := VAt graph path.firstStep
  let fixed := center ⊓ Subgroup.centralizer (first : Set G)
  have hZaV : center ≤ first := (lemma_seven_four ctx.sectionSeven graph path).first_containment.1
  have hVS : first ≤ S :=
    (le_sup_left.trans data.sylow_intersection.symm.le).trans inf_le_right
  have hfirstEnd : graph.adjacent path.firstStep path.a' := by
    have hadj := path.path_adj ⟨1, by change 1 < ctx.criticalPath.length; omega⟩
    have hleft : path.path (⟨1, by change 1 < ctx.criticalPath.length; omega⟩ :
        Fin path.length).castSucc = path.firstStep := path.path_first
    have hright : path.path (⟨1, by change 1 < ctx.criticalPath.length; omega⟩ :
        Fin path.length).succ = path.a' := by
      convert path.path_end using 1
      congr 1
      apply Fin.ext
      change 1 + 1 = ctx.criticalPath.length
      omega
    rwa [hleft, hright] at hadj
  have hZendV : ZAt graph path.a' ≤ first := by
    change z graph path.a' ≤ v graph path.firstStep
    rw [v, graph.vAt_def]
    exact le_sSup ⟨path.a', (SevenSix.mem_neighborhood_iff_adjacent graph).mpr hfirstEnd, rfl⟩
  have hZendQ : ZAt graph path.a' ≤ QAt graph path.firstStep := by
    apply SevenSix.critical_minimality graph path
    rw [graph.distance_symm, (SevenSix.adjacent_iff_distance_eq_one graph).mp hfirstEnd]
    change 1 < ctx.criticalPath.length
    omega
  have hfirstNe : ZAt graph path.firstStep ≠ ⊥ := by
    intro hbot
    apply ctx.commutator_ne
    apply le_bot_iff.mp
    exact ((Subgroup.commutator_mono hZaV hZendQ).trans_eq data.first_commutator).trans_eq hbot
  have hZfixed : ZAt graph path.firstStep ≤ fixed :=
    le_inf (eight_six_first_center_le_initial ctx.sectionSeven graph path hcenter)
      ((hcenter.trans (SevenSix.centerAmbient_le_centralizer _)).trans
        (Subgroup.centralizer_le (hVS.trans
          (SevenSix.edge_sylow_data ctx.sectionSeven graph path).2.1)))
  have hfixedNe : fixed ≠ center := by
    intro heq
    apply ctx.commutator_ne
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    have hcentral : center ≤ Subgroup.centralizer (first : Set G) :=
      heq ▸ (inf_le_right : fixed ≤ Subgroup.centralizer (first : Set G))
    exact hcentral.trans (Subgroup.centralizer_le hZendV)
  have hfixedCard : Nat.card fixed < 4 := by
    have hle : Nat.card fixed ≤ Nat.card center :=
      Nat.card_le_card_of_injective (Subgroup.inclusion (show fixed ≤ center from inf_le_left))
        (Subgroup.inclusion_injective _)
    have hne : Nat.card fixed ≠ Nat.card center := fun heq =>
      hfixedNe (Subgroup.eq_of_le_of_card_ge inf_le_left heq.ge)
    exact (lt_of_le_of_ne hle hne).trans_eq hcard
  have hdvd : Nat.card fixed ∣ 4 := hcard ▸ Subgroup.card_dvd_of_le
    (show fixed ≤ center from inf_le_left)
  have hbound : Nat.card fixed ≤ 2 := by
    obtain ⟨exponent, hexponent, hpower⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card fixed ∣ 2 ^ 2 from hdvd)
    have hcases : exponent = 0 ∨ exponent = 1 ∨ exponent = 2 := by omega
    rcases hcases with heq | heq | heq
    · rw [heq] at hpower
      exact hpower.le.trans (by decide)
    · rw [heq] at hpower
      exact hpower.le
    · rw [heq] at hpower
      norm_num at hpower
      omega
  have hlower : 2 ≤ Nat.card (ZAt graph path.firstStep) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hfirstNe
  have heq : ZAt graph path.firstStep = fixed :=
    Subgroup.eq_of_le_of_card_ge hZfixed (hbound.trans hlower)
  exact (le_inf hUZ hUV).trans_eq heq.symm

end Stellmacher.SectionEight
