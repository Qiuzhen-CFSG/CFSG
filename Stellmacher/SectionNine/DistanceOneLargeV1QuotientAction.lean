module
public import Stellmacher.SectionNine.DistanceOneSmallV1CoreAction
/-!
# The large quotient action forced by noncentral initial core action

Under the actual maximal-V₁ input properties at critical length one,
if [Q_initial,U] is not contained in Z_initial, then U/Z_terminal has
order64 and the actual terminal-residual image on this quotient is
extraspecial of order27. The theorem retains the literal quotient,
normality and elementary instances, exact conjugation map, killed core,
full residual action, and selected involution. Its fixed index is four,
and it centralizes the center of the extraspecial residual image.

The small-case core-action theorem excludes |U|≤16|Z_terminal|.
The actual (1.3) packet then rules out its four- and sixteen-element
alternatives, leaving the extraspecial case. The subgroup quotient
cardinality identity converts quotient order64 to |U|=64|Z_terminal|.
No additional structure of the initial faithful quotient is needed here.

Source: Stellmacher, Journal of Algebra190 (1997), (9.1), p.47, the
large branch immediately before (10). The preserved image acts on U/Z;
this result does not identify it with the action on U or with the entire
terminal core quotient. Those are separate local transfers.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise commutatorElement
universe u
public theorem distance_one_large_v1_quotient_action
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (U : Subgroup G)
    (hUQ : U ≤ q ctx.Γ ctx.criticalPath.a')
    (hZU : z ctx.Γ ctx.criticalPath.a' ≤ U)
    (hUQc : ⁅U,q ctx.Γ ctx.criticalPath.a'⁆ = z ctx.Γ ctx.criticalPath.a')
    (hUE : ⁅U,twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.a')⁆ = U)
    (hUT : U ≤ T) (hUn : (U.subgroupOf T).Normal)
    (hlow : Nat.card (U ⊓ Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G) : Subgroup G)
      < Nat.card U)
    (hupper : Nat.card U ≤ 4 * Nat.card
      (U ⊓ Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G) : Subgroup G))
    (hnoncentral : ¬ ⁅q ctx.Γ ctx.criticalPath.a,U⁆ ≤ z ctx.Γ ctx.criticalPath.a) :
    ∃ hN : ((z ctx.Γ ctx.criticalPath.a').subgroupOf U).Normal,
      let _ := hN
      let P := stabilizer ctx.Γ ctx.criticalPath.a'
      let Z := z ctx.Γ ctx.criticalPath.a'
      ∃ hW : IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U),
      let _ := hW
      Nat.card U = 64 * Nat.card Z ∧
      Nat.card (U ⧸ Z.subgroupOf U) = 64 ∧
      Nontrivial (U ⧸ Z.subgroupOf U) ∧
      ∃ hPU : P ≤ Subgroup.normalizer (U : Set G),
      ∃ ρ : P →* MulAut (U ⧸ Z.subgroupOf U),
        (∀ p : P, ∀ u : U, ρ p (QuotientGroup.mk' (Z.subgroupOf U) u) =
          QuotientGroup.mk' (Z.subgroupOf U) ⟨(p:G)*(u:G)*(p:G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hPU p.property) u).mp u.property⟩) ∧
        (q ctx.Γ ctx.criticalPath.a').subgroupOf P ≤ ρ.ker ∧
        commutatorAction ((twoResidualIn P).subgroupOf P |>.map ρ)
          (U ⧸ Z.subgroupOf U) = ⊤ ∧
        ∃ x : P, (x:G) ∈ z ctx.Γ ctx.criticalPath.a ∧ _root_.IsInvolution (x:G) ∧
          (x:G) ∉ q ctx.Γ ctx.criticalPath.a' ∧ _root_.IsInvolution (ρ x) ∧
          ⁅(twoResidualIn P).subgroupOf P |>.map ρ, Subgroup.zpowers (ρ x)⁆ =
            ((twoResidualIn P).subgroupOf P |>.map ρ) ∧
          Nat.card (U ⧸ Z.subgroupOf U) = 4 * Nat.card
            (FixedPoints.subgroup (Subgroup.zpowers (ρ x)) (U ⧸ Z.subgroupOf U)) ∧
          ⁅(Subgroup.center ((twoResidualIn P).subgroupOf P |>.map ρ)).map
            ((twoResidualIn P).subgroupOf P |>.map ρ).subtype, Subgroup.zpowers (ρ x)⁆ = ⊥ ∧
          IsExtraspecial 3 ((twoResidualIn P).subgroupOf P |>.map ρ) ∧
          Nat.card ((twoResidualIn P).subgroupOf P |>.map ρ) = 27 := by
  obtain ⟨hN,hW,hWne,hPU,ρ,hρ,hker,hfull,x,hx,hxi,hxQ,hxi',hFx,hclass⟩ :=
    distance_one_v1_action_classification ctx hb U hUQ hZU hUQc hUE hUT hUn hlow hupper
  let _ := hN
  let _ := hW
  let _ := hWne
  let Z := z ctx.Γ ctx.criticalPath.a'
  let W := U ⧸ Z.subgroupOf U
  let P := stabilizer ctx.Γ ctx.criticalPath.a'
  let F := (twoResidualIn P).subgroupOf P |>.map ρ
  have hcount : Nat.card U = Nat.card W * Nat.card Z := by
    have hh := (Z.subgroupOf U).card_mul_index
    rw [Subgroup.index_eq_card] at hh
    have heq : Nat.card (Z.subgroupOf U) = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv
    rw [heq] at hh
    exact hh.symm.trans (Nat.mul_comm _ _)
  have hFWcard : Nat.card (commutatorAction F W) = Nat.card W := by
    rw [hfull, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup W) ≃* W).toEquiv]
  have hnot : ¬ Nat.card U ≤ 16 * Nat.card Z := by
    intro hh
    exact hnoncentral (distance_one_small_v1_core_action ctx hb U hUQ hZU hUQc hUE
      hUT hUn hlow hupper hh)
  cases hclass with
  | cyclicThree hcard _ =>
    exfalso
    apply hnot
    rw [hcount, ← hFWcard, hcard]
    exact Nat.mul_le_mul_right _ (by decide : 4≤16)
  | small hcard _ _ =>
    exfalso
    apply hnot
    rw [hcount, ← hFWcard, hcard]
    exact le_rfl
  | extraspecial hcard hfix hcent hExtra hFcard =>
    have hWcard : Nat.card W = 64 := hFWcard.symm.trans hcard
    refine ⟨hN,hW,?_,hWcard,hWne,hPU,ρ,hρ,hker,hfull,x,hx,hxi,hxQ,hxi',hFx,
      hfix,hcent,hExtra,hFcard⟩
    rw [hcount,hWcard]
end Stellmacher.SectionNine
