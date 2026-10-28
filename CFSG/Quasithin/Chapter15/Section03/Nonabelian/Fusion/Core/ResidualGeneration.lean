module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Quotients
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Inputs
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Index

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Placement
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Action
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.TransferIndex

/-!
# The residual and Frattini calculation in 15.3.59

`Inputs` fixes actual natural/dual recognition on U/Z. `Quotients` proves
Sylow restriction, centrality of the actor kernel in K/U, Frattini lifting
of marked generators, and the order bound from the literal fibers.
`Placement` retains the source partner and its conjugate. `Action` proves
U ≤ K, K = [K,V], the residual actor order, and the centralizer containment.
`Partner` derives the marked commutator identity and lifts X through the
normalized subgroup XU. The Frattini kernel is the image of K ∩ Q_H in
K/U; no containment Q_C ≤ K or central-cover classification is required.

`residual_generation_of_earlier_source` assembles the residual containment,
commutator generation, marked Frattini generation, placement in YU, and
order bound, discharging all residual and marked-calculation premises of
the original conditional helper. The input consists of genuine earlier
local conclusions, including the two actual equivariant module markings.

After U = Q_H, `transfer_description_of_earlier_source` identifies T_K with
U C_T(V). `TransferIndex` derives its local index from the earlier orders
eight and four of the literal conjugation images on V. The parent `Core`
owns the earlier-source inputs, the intervening equality U = Q_H, and
assembly of all four clauses of 15.3.59.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.1149–1150.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core
variable {G : Type*} [Group G] [Finite G]

/-- Assemble the Frattini generation, containment in YU and order bound from
marked image calculations. The later `residual_generation_of_earlier_source`
discharges the residual-action and partner-lift hypotheses of this helper. -/
theorem generation_containment_and_bound_of_marked_inputs (T Z ZS V Y : Subgroup G) (y t : G)
    [(Z.subgroupOf (closureU Z ZS)).Normal] [IsExtraspecial 2 (closureU Z ZS)]
    (d : LocalCoreData T Z ZS V Y)
    (S : Sylow 2 (centralizerH Z))
    (hS : (S : Subgroup (centralizerH Z)).map (centralizerH Z).subtype = T)
    (hUK : closureU Z ZS ≤ residualK Z)
    (hcomm : ⁅residualK Z, V⁆ = residualK Z)
    (hXT : partnerX Z ZS y ≤ T) (hXK : partnerX Z ZS y ≤ residualK Z)
    (hy : y ∈ Y) (ht : t ∈ T)
    (himage : actorImage Z (residualSylow T Z) ≤ actorImage Z
      (partnerX Z ZS y ⊔ rightConjugate (partnerX Z ZS y) t))
    (hU : Nat.card (closureU Z ZS) = 2 ^ 7)
    (hactor : 2 ^ 3 ≤ Nat.card (actorImage Z (residualSylow T Z))) :
    residualSylow T Z = (partnerX Z ZS y ⊔ rightConjugate (partnerX Z ZS y) t) ⊔ closureU Z ZS ∧
      residualSylow T Z ≤ Y ⊔ closureU Z ZS ∧
      2 ^ 10 ≤ Nat.card (residualSylow T Z) := by
  have hUT := d.closure_le_core.trans d.core_le_sylow
  have hX : partnerX Z ZS y ≤ residualSylow T Z := le_inf hXT hXK
  have hQ := coreQ_split T Z ZS d.T_le_H d.closure_le_core d.core_le_sylow
    d.center_closure d.action_kernel
  have hc := residualK_centralizes_centralizerC T Z ZS V d.T_le_H d.core_le_sylow
    d.action_kernel d.module_le_sylow d.normalizes_module d.module_centralizer
    d.center_two_group hcomm
  have he := residualSylow_generation_of_actor_generation T Z ZS _ _ S hS hUK hUT
    d.closure_le_core hQ hc hX (conjugate_le_residualSylow T Z _ t ht d.T_le_H hX) himage
  refine ⟨he, ?_, residualSylow_card_lower T Z ZS hUT hUK d.closure_le_core hU hactor⟩
  rw [he]
  exact sup_le (sup_le (partnerX_le_pair Z ZS Y y hy)
    (conjugate_partnerX_le_pair T Z ZS Y y t hy ht d.T_le_H d.normalizes_Y)) le_sup_right

/-- The centralizer containment and the two actual index calculations identify
the subgroup used by transfer. The local index of U C_T(V) comes from its
image in the earlier orthogonal action on V; it is not the desired equality. -/
theorem transfer_description_of_centralizer_containment (T Z ZS V : Subgroup G)
    (S : Sylow 2 (centralizerH Z))
    (hS : (S : Subgroup (centralizerH Z)).map (centralizerH Z).subtype = T)
    (e : ActorQuotient Z ≃* MulAut Matrix.PSL3Two.SL)
    (hUQ : closureU Z ZS = coreQ Z) (hUK : closureU Z ZS ≤ residualK Z)
    (hCTK : T ⊓ centralizer (V : Set G) ≤ residualK Z)
    (hlocal : ((closureU Z ZS ⊔ (T ⊓ centralizer (V : Set G))).subgroupOf T).index = 2) :
    residualSylow T Z = closureU Z ZS ⊔ (T ⊓ centralizer (V : Set G)) := by
  let D := closureU Z ZS ⊔ (T ⊓ centralizer (V : Set G))
  have hUT : closureU Z ZS ≤ T :=
    hUQ.le.trans ((core_le_sylow_image _ S).trans hS.le)
  have hDT : D ≤ T := sup_le hUT inf_le_left
  have hDK : D ≤ residualSylow T Z := le_inf hDT (sup_le hUK hCTK)
  have hindex := residualSylow_index_two_of_actor_equiv T Z ZS S hS e hUQ hUK
  change (D.subgroupOf T).index = 2 at hlocal
  have he : D.subgroupOf T = (residualSylow T Z).subgroupOf T := by
    by_contra hne
    have hlt := index_strictAnti (lt_of_le_of_ne (subgroupOf_mono T hDK) hne)
    omega
  have hm := congrArg (map T.subtype) he
  rw [map_subgroupOf_eq_of_le hDT,
    map_subgroupOf_eq_of_le (show residualSylow T Z ≤ T from inf_le_left)] at hm
  exact hm.symm

variable {T Z ZS V Y Y₁ : Subgroup G} {y t : G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal] [IsExtraspecial 2 (closureU Z ZS)]

/-- The residual/Frattini calculation of 15.3.59 from earlier conclusions
through 15.3.58. The actual natural/dual recognition, the full paired
transvection marking, the source t, and the J-normalizer information are
retained in m. No residual containment, generation or order bound is an input.
The nontrivial V-action and displacement are 15.3.51(1) and 15.3.53(2);
the order of U is 15.3.58(2). -/
theorem residual_generation_of_earlier_source
    (d : LocalCoreData T Z ZS V Y)
    (m : Partner.EarlierGeometry T Z ZS V Y₁ y t)
    (hY₁ : Y₁ ≤ Y)
    (hVQ : ¬ V ≤ coreQ Z)
    (hdisplacement : ⁅closureU Z ZS, V⁆ ≤ V)
    (hcard : Nat.card (vectorDisplacement Z ZS V) = 4)
    (hU : Nat.card (closureU Z ZS) = 2 ^ 7) :
    closureU Z ZS ≤ residualK Z ∧
      ⁅residualK Z, V⁆ = residualK Z ∧
      partnerX Z ZS y ≤ residualK Z ∧
      residualSylow T Z =
        (partnerX Z ZS y ⊔ rightConjugate (partnerX Z ZS y) t) ⊔ closureU Z ZS ∧
      residualSylow T Z ≤ Y ⊔ closureU Z ZS ∧
      2 ^ 10 ≤ Nat.card (residualSylow T Z) := by
  obtain ⟨hUK, hcomm, hactor, _⟩ := residual_action_consequences m.recognized
    m.sylow m.sylow_map d.closure_le_core d.center_closure d.action_kernel
    d.module_le_sylow hVQ hdisplacement hcard
  obtain ⟨hXK, himage⟩ := m.partner_conclusions hUK hactor
  exact ⟨hUK, hcomm, hXK,
    generation_containment_and_bound_of_marked_inputs T Z ZS V Y y t d
      m.sylow m.sylow_map hUK hcomm m.X_le_T hXK (hY₁ m.y_mem)
      m.recognized.t_mem himage hU (by omega)⟩

/-- The transfer subgroup after the parent's intervening proof U = Q_H.
The two scalar action orders are earlier orthogonal-action conclusions
on the literal V, not a supplied index or a residual-generation hypothesis.
Both the required centralizer containment and the local index are proved
before applying the original index-comparison helper. -/
theorem transfer_description_of_earlier_source
    (a : RecognizedAction T Z ZS V t)
    (S : Sylow 2 (centralizerH Z))
    (hS : (S : Subgroup (centralizerH Z)).map (centralizerH Z).subtype = T)
    (hcenter : (center (closureU Z ZS)).map (closureU Z ZS).subtype = Z)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hVT : V ≤ T) (hTV : T ≤ normalizer (V : Set G))
    (hVQ : ¬ V ≤ coreQ Z)
    (hdisplacement : ⁅closureU Z ZS, V⁆ ≤ V)
    (hcard : Nat.card (vectorDisplacement Z ZS V) = 4)
    (hTaction : Nat.card (conjugationOnV T V hTV).range = 8)
    (hUaction : Nat.card (((closureU Z ZS).subgroupOf T).map
      (conjugationOnV T V hTV)) = 4)
    (hUQ : closureU Z ZS = coreQ Z) :
    residualSylow T Z = closureU Z ZS ⊔ (T ⊓ centralizer (V : Set G)) := by
  obtain ⟨hUK, _, _, hCT⟩ := residual_action_consequences a S hS hUQ.le hcenter
    hkernel hVT hVQ hdisplacement hcard
  have hUT := hUQ.le.trans ((core_le_sylow_image _ S).trans hS.le)
  exact transfer_description_of_centralizer_containment T Z ZS V S hS a.actorEquiv
    hUQ hUK (hCT hUQ) (transfer_index_of_conjugation_orders T Z ZS V hUT hTV
      hTaction hUaction)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
