module
public import Stellmacher.SectionNine.DistanceOneV1ActionClassification
public import Theory.GroupAction.FourElementInvolutionLines

/-!
# The maximal V₁ intersections in the large quotient branch

In the actual critical-length-one configuration, suppose U has the
maximal-V₁ commutator and Sylow-normality properties, with nontrivial
initial-center action of index at most four. Assume its terminal-center
quotient has order64, the terminal center has order2, and the intersection
of the initial center with the terminal core has order8. Then U meets
the initial center in order8 and the initial core in order32. In
particular its image modulo the initial core has order4. Its double
commutator with the initial core lies even in the terminal center.

The actual (1.3) quotient-action packet forces the large alternative.
The selected initial-center involution has sixteen fixed points and four
action commutators on U/Z_terminal. Its commutator subgroup lies in the
image of U intersected with the initial center; the order8 upper bound
forces equality of their orders. The initial-core intersection maps into
the same involution's fixed subgroup, giving an order32 upper bound.
The original action-index inequality and (7.4)'s Sylow centralizer identity
give the reverse bound. Quotient-image cardinality formulas retain the
literal intersections. Finally U is normal in the edge Sylow, so the
double commutator is bounded by [U,U]≤[U,Q_terminal]=Z_terminal.

Source: Stellmacher, Journal of Algebra190 (1997), p.47, the intersection
ratio4 before (9.1)(10), and the barred V₁ order and double-commutator
assertions in (10). This argument does not identify the action on U with
its action on U/Z_terminal or assume initial core equality.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise commutatorElement
universe u

private theorem quotient_intersection_card
    {G : Type*} [Group G] [Finite G] (U Z A : Subgroup G)
    (hZU : Z ≤ U) (hZA : Z ≤ A) (hN : (Z.subgroupOf U).Normal) :
    let _ := hN
    Nat.card Z * Nat.card ((A.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))) =
      Nat.card (U ⊓ A : Subgroup G) := by
  let _ := hN
  dsimp only
  let N := Z.subgroupOf U
  let D := A.subgroupOf U
  have hND : N ≤ D := fun _ h => hZA h
  have hp := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup U) N D bot_le hND
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at hp
  have hn : Nat.card N = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv
  have hd : Nat.card D = Nat.card (U ⊓ A : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective (K := D) U.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [hn, hd] at hp
  have hi : N.relIndex D = Nat.card (D.map (QuotientGroup.mk' N)) := by
    simpa only [QuotientGroup.ker_mk'] using D.relIndex_ker (QuotientGroup.mk' N)
  rwa [hi] at hp

private theorem quotient_commutator_le_initial_image
    {G : Type*} [Group G] (P U Z A : Subgroup G)
    (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (hUA : U ≤ Subgroup.normalizer (A : Set G))
    (hN : (Z.subgroupOf U).Normal) :
    let _ := hN
    ∀ ρ : P →* MulAut (U ⧸ Z.subgroupOf U),
      (∀ p : P, ∀ u : U,
        ρ p (QuotientGroup.mk' (Z.subgroupOf U) u) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(p:G)*(u:G)*(p:G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp (hPU p.property) u).mp u.property⟩) →
      ∀ x : P, (x:G) ∈ A →
      commutatorAction (Subgroup.zpowers (ρ x)) (U ⧸ Z.subgroupOf U) ≤
        (A.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
  let _ := hN
  dsimp only
  intro ρ hρ x hx
  let π := QuotientGroup.mk' (Z.subgroupOf U)
  rw [commutatorAction_eq_closure]
  apply (Subgroup.closure_le (K := (A.subgroupOf U).map π)).mpr
  rintro _ ⟨a,w,rfl⟩
  have ha : (a : MulAut (U ⧸ Z.subgroupOf U)) ∈ (Subgroup.zpowers x).map ρ := by
    rw [MonoidHom.map_zpowers]
    exact a.property
  obtain ⟨y,hy,hya⟩ := ha
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w
  have hyA : (y:G) ∈ A :=
    (Subgroup.zpowers_le.mpr (show x ∈ A.subgroupOf P from hx)) hy
  change (π u)⁻¹ * (a : MulAut (U ⧸ Z.subgroupOf U)) (π u) ∈ _
  rw [← hya,hρ,← map_inv,← map_mul]
  apply Subgroup.mem_map_of_mem
  change (u:G)⁻¹ * ((y:G)*(u:G)*(y:G)⁻¹) ∈ A
  have hh := A.mul_mem
    ((Subgroup.mem_normalizer_iff.mp (hUA (U.inv_mem u.property)) y).mp hyA)
    (A.inv_mem hyA)
  simpa only [inv_inv,mul_assoc] using hh

/-- Exact initial intersections of maximal V₁ in the large quotient case. -/
public theorem distance_one_large_v1_intersections
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
    (hlarge : Nat.card U = 64 * Nat.card (z ctx.Γ ctx.criticalPath.a'))
    (hZaQ : Nat.card (z ctx.Γ ctx.criticalPath.a ⊓ q ctx.Γ ctx.criticalPath.a' : Subgroup G) = 8)
    (hZd : Nat.card (z ctx.Γ ctx.criticalPath.a') = 2) :
    Nat.card (U ⊓ z ctx.Γ ctx.criticalPath.a : Subgroup G) = 8 ∧
      Nat.card (U ⊓ q ctx.Γ ctx.criticalPath.a : Subgroup G) = 32 ∧
      Nat.card U = 4 * Nat.card (U ⊓ q ctx.Γ ctx.criticalPath.a : Subgroup G) ∧
      ⁅⁅q ctx.Γ ctx.criticalPath.a,U⁆,U⁆ ≤ z ctx.Γ ctx.criticalPath.a' := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a'
  let Za := z Γ cp.a
  let Z := z Γ cp.a'
  let Qa := q Γ cp.a
  obtain ⟨hN,hW,hWne,hPU,ρ,hρ,hker,hfull,x,hx,hxi,hxQ,hxi',hFx,hclass⟩ :=
    distance_one_v1_action_classification ctx hb U hUQ hZU hUQc hUE hUT hUn hlow hupper
  let _ := hN
  let _ := hW
  let _ := hWne
  let W := U ⧸ Z.subgroupOf U
  let π := QuotientGroup.mk' (Z.subgroupOf U)
  let D := (Za.subgroupOf U).map π
  let K := (Qa.subgroupOf U).map π
  let X := Subgroup.zpowers (ρ x)
  let Cx := FixedPoints.subgroup X W
  let M := commutatorAction X W
  have hUcard : Nat.card U = 128 := by rw [hZd] at hlarge; omega
  have hWcard : Nat.card W = 64 := by
    have hcount := (Z.subgroupOf U).card_mul_index
    rw [Subgroup.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv, hZd] at hcount
    change 2 * Nat.card W = Nat.card U at hcount
    omega
  have hCx : Nat.card Cx = 16 := by
    have hcardF : Nat.card (commutatorAction ((twoResidualIn P).subgroupOf P |>.map ρ) W) =
        Nat.card W := by rw [hfull, Subgroup.card_top]
    cases hclass with
    | cyclicThree hc _ =>
      have hh : Nat.card W = 4 := hcardF.symm.trans hc
      omega
    | small hc _ _ =>
      have hh : Nat.card W = 16 := hcardF.symm.trans hc
      omega
    | extraspecial _ hfixed _ _ _ =>
      change Nat.card W = 4 * Nat.card Cx at hfixed
      omega
  have hXcard : Nat.card X = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxi'.2 hxi'.1]
  let xX : X := ⟨ρ x,Subgroup.mem_zpowers _⟩
  have hxX : xX ≠ 1 ∧ xX^2=1 :=
    ⟨fun h => hxi'.1 (congrArg Subtype.val h), Subtype.ext hxi'.2⟩
  obtain ⟨hprod,_hle⟩ := card_two_action_fixed_commutator_card_data (U:=W) xX hxX hXcard
  have hMcard : Nat.card M = 4 := by
    change Nat.card W = Nat.card Cx * Nat.card M at hprod
    rw [hWcard,hCx] at hprod
    omega
  have hneighbor : cp.a' ∈ neighborhood Γ cp.a := by
    rw [neighborhood, Γ.neighbors_def]
    exact (Γ.distance_symm _ _).trans (cp.endpoint_distance.trans hb)
  have hstep : cp.firstStep = cp.a' := by
    rw [← cp.path_end, ← cp.path_first]
    congr 1
    exact Fin.ext hb.symm
  have hTQa : Qa ≤ T := (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1
  have hZa : Za ≤ omegaOneCenter Qa :=
    (lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.a' hneighbor
  have hQA : Qa ≤ Subgroup.centralizer (Za:Set G) :=
    Subgroup.le_centralizer_iff.mp
      (hZa.trans ((omegaOneCenter_le_centerAmbient Qa).trans (centerAmbient_le_centralizer Qa)))
  have hUA : U ≤ Subgroup.normalizer (Za:Set G) :=
    (hUT.trans (edge_sylow_data ctx.sectionSeven Γ cp).1.1).trans
      (stabilizer_le_normalizer_z Γ cp.a)
  have hZA : Z ≤ Za := by
    have h75 := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).next_center.1
    rw [hstep] at h75
    rw [show Z = omegaOneCenter T from h75]
    obtain ⟨_,R,hR⟩ := (edge_sylow_data ctx.sectionSeven Γ cp).1
    change omegaOneCenter T ≤ z Γ cp.a
    rw [z,Γ.zAt_def]
    exact le_sSup ⟨R,congrArg omegaOneCenter hR.symm⟩
  have hZQa : Z ≤ Qa := hZA.trans (hZa.trans (Subgroup.map_subtype_le _))
  have hDcount : 2 * Nat.card D = Nat.card (U ⊓ Za : Subgroup G) := by
    have hh := quotient_intersection_card U Z Za hZU hZA hN
    change Nat.card Z * Nat.card D = _ at hh
    rw [show Nat.card Z = 2 from hZd] at hh
    exact hh
  have hKcount : 2 * Nat.card K = Nat.card (U ⊓ Qa : Subgroup G) := by
    have hh := quotient_intersection_card U Z Qa hZU hZQa hN
    change Nat.card Z * Nat.card K = _ at hh
    rw [show Nat.card Z = 2 from hZd] at hh
    exact hh
  have hMD : M ≤ D := quotient_commutator_le_initial_image P U Z Za hPU hUA hN ρ hρ x hx
  have hDlower : 4 ≤ Nat.card D := by
    simpa only [hMcard] using Subgroup.card_le_of_le hMD
  have hDupper : Nat.card (U ⊓ Za : Subgroup G) ≤ 8 := by
    have hh := Subgroup.card_le_of_le (show U ⊓ Za ≤ Za ⊓ q Γ cp.a' from
      le_inf inf_le_right (inf_le_left.trans hUQ))
    exact hh.trans_eq hZaQ
  have hKC : K ≤ Cx := by
    rintro w ⟨v,hv,rfl⟩ a
    have hcomm : (x:G)*(v:G)=(v:G)*(x:G) :=
      Subgroup.mem_centralizer_iff.mp (hQA hv) x hx
    have hfixed : ρ x (π v) = π v := by
      rw [hρ]
      apply congrArg π
      apply Subtype.ext
      change (x:G)*(v:G)*(x:G)⁻¹=(v:G)
      rw [hcomm,mul_assoc,mul_inv_cancel,mul_one]
    exact smul_eq_self_of_mem_zpowers a.property hfixed
  have hKupper : Nat.card K ≤ 16 := (Subgroup.card_le_of_le hKC).trans_eq hCx
  have hCeq : U ⊓ Subgroup.centralizer (Za:Set G) = U ⊓ Qa := by
    change U ⊓ Subgroup.centralizer (z Γ cp.a:Set G) = U ⊓ q Γ cp.a
    rw [← (lemma_seven_four ctx.sectionSeven Γ cp).edge_centralizer,
      ← inf_assoc, inf_eq_left.mpr hUT]
  change Nat.card U ≤ 4 * Nat.card (U ⊓ Subgroup.centralizer (Za:Set G) : Subgroup G) at hupper
  rw [hCeq] at hupper
  have hQcard : Nat.card (U ⊓ Qa : Subgroup G) = 32 := by omega
  change Nat.card (U ⊓ Za : Subgroup G) = 8 ∧
    Nat.card (U ⊓ Qa : Subgroup G) = 32 ∧
    Nat.card U = 4 * Nat.card (U ⊓ Qa : Subgroup G) ∧ ⁅⁅Qa,U⁆,U⁆ ≤ Z
  refine ⟨by omega,hQcard,by omega,?_⟩
  have hQU : ⁅Qa,U⁆ ≤ U :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp (hTQa.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hUT).mp hUn))
  exact (Subgroup.commutator_mono hQU hUQ).trans hUQc.le

end Stellmacher.SectionNine
