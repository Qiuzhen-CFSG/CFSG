module

public import Stellmacher.SectionNine.DistanceOneV1ActionClassification
public import Stellmacher.SectionNine.DistanceOneProductCoreAction

/-!
# The maximal V₁ has order eight after initial core equality

In the actual critical-length-one configuration, suppose the initial core
has become its center. An extracted product V of order32 lies in the terminal
core of order64 and meets the initial center in order8. For the actual
maximal-V₁ subgroup U, retain its full terminal residual commutator, central
terminal-core commutator, Sylow normality, initial action bounds, and source
containment U≤V joined with the initial center. The theorem proves U≤V and
|U|=8; it does not assume or conclude elementarity of U.

The initial-center intersection with the terminal core lies in V, so a
normalized-product decomposition gives U≤V. The exact quotient action packet
applies (1.3) to U/Z_terminal, with full action, giving quotient orders4,16,
or64. The last exceeds |V|32. Order16 would force U=V, contradicting the
proved noncentral terminal-core action on V modulo the initial center.
The remaining quotient order4 and |Z_terminal|2 give |U|8.

Source: Stellmacher(9.1), Journal of Algebra190 (1997), p.48, the small
maximal-subgroup deduction after (11). All geometry and intermediate orders
are explicit; no full local conclusion is used. Elementarity and the terminal
S3 quotient are separate subsequent transfers.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven SevenSix CosetGraphContext
universe u

public theorem distance_one_v1_card_eight_of_core_eq_center
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length=1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hcore : QAt ctx.Γ ctx.criticalPath.a=ZAt ctx.Γ ctx.criticalPath.a)
    (U V : Subgroup G)
    (hUQ : U≤q ctx.Γ ctx.criticalPath.a')
    (hZU : z ctx.Γ ctx.criticalPath.a'≤U)
    (hUQc : ⁅U,q ctx.Γ ctx.criticalPath.a'⁆=z ctx.Γ ctx.criticalPath.a')
    (hUE : ⁅U,twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.a')⁆=U)
    (hUT : U≤T) (hUn : (U.subgroupOf T).Normal)
    (hlow : Nat.card (U⊓Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a:Set G):Subgroup G)<Nat.card U)
    (hupper : Nat.card U≤4*Nat.card (U⊓Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a:Set G):Subgroup G))
    (hVQ : V≤q ctx.Γ ctx.criticalPath.a')
    (hVcard : Nat.card V=32) (hQcard : Nat.card (q ctx.Γ ctx.criticalPath.a')=64)
    (hIcard : Nat.card (V⊓z ctx.Γ ctx.criticalPath.a:Subgroup G)=8)
    (hseed : z ctx.Γ ctx.criticalPath.a⊓q ctx.Γ ctx.criticalPath.a'≤V)
    (hUsup : U≤V⊔z ctx.Γ ctx.criticalPath.a)
    (hZcard : Nat.card (z ctx.Γ ctx.criticalPath.a')=2)
    (hZZ : z ctx.Γ ctx.criticalPath.a'≤z ctx.Γ ctx.criticalPath.a) :
    U≤V ∧ Nat.card U=8 := by
  let Za := z ctx.Γ ctx.criticalPath.a
  let Q := q ctx.Γ ctx.criticalPath.a'
  let Z := z ctx.Γ ctx.criticalPath.a'
  have hend : ctx.criticalPath.a'=ctx.criticalPath.firstStep := by
    rw [← ctx.criticalPath.path_end,← ctx.criticalPath.path_first]
    congr 1
    exact Fin.ext hb
  have hQT : Q≤T := by
    change q ctx.Γ ctx.criticalPath.a'≤T
    rw [hend]
    exact (local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).2
  have hVfirst : V≤stabilizer ctx.Γ ctx.criticalPath.a :=
    hVQ.trans (hQT.trans (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1)
  have hn : V≤Subgroup.normalizer (Za:Set G) :=
    hVfirst.trans (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a)
  have hUV : U≤V := by
    intro x hx
    have hh : x∈(↑(V⊔Za):Set G) := hUsup hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right V Za hn] at hh
    obtain ⟨v,hv,a,ha,rfl⟩ := hh
    have haQ : a∈Q := by
      have hh := Q.mul_mem (Q.inv_mem (hVQ hv)) (hUQ hx)
      simpa only [inv_mul_cancel_left] using hh
    exact V.mul_mem hv (hseed ⟨ha,haQ⟩)
  have hUle : Nat.card U≤32 := by simpa only [hVcard] using Subgroup.card_le_of_le hUV
  obtain ⟨hN,hW,hnt,hPU,rho,hcompat,hQker,hfull,x,hx,hxi,hxQ,hrx,hFx,hclass⟩ :=
    distance_one_v1_action_classification ctx hb U hUQ hZU hUQc hUE hUT hUn hlow hupper
  let _ := hN
  let _ := hW
  have hZnative : Nat.card (Z.subgroupOf U)=2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv).trans hZcard
  have hmult := (Z.subgroupOf U).card_mul_index
  rw [hZnative,Subgroup.index_eq_card] at hmult
  have hcardW : Nat.card (U⧸Z.subgroupOf U)=4 := by
    cases hclass with
    | cyclicThree hcard _ =>
      simpa only [hfull,Subgroup.card_top, show (2:ℕ)^4=16 by decide, show (2:ℕ)^6=64 by decide] using hcard
    | small hcard _ _ =>
      have hc : Nat.card (U⧸Z.subgroupOf U)=16 := by
        simpa only [hfull,Subgroup.card_top, show (2:ℕ)^4=16 by decide, show (2:ℕ)^6=64 by decide] using hcard
      have hU32 : Nat.card U=32 := by omega
      have heq : U=V := Subgroup.eq_of_le_of_card_ge hUV (by rw [hU32,hVcard])
      have hbad := distance_one_product_core_commutator_not_le_initial_center
        ctx.toLocalContext hb hfaith hcore V hVQ hVcard hQcard hIcard
      apply (hbad ?_).elim
      change ⁅q ctx.Γ ctx.criticalPath.a',V⁆≤z ctx.Γ ctx.criticalPath.a
      rw [Subgroup.commutator_comm,← heq,hUQc]
      exact hZZ
    | extraspecial hcard _ _ _ _ =>
      have hc : Nat.card (U⧸Z.subgroupOf U)=64 := by
        simpa only [hfull,Subgroup.card_top, show (2:ℕ)^4=16 by decide, show (2:ℕ)^6=64 by decide] using hcard
      omega
  exact ⟨hUV,by omega⟩
end Stellmacher.SectionNine
