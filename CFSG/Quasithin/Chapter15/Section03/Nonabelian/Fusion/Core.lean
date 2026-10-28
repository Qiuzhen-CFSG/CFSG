module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Reduction
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Index
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers

/-!
# The core, residual Sylow subgroup and supplement in 15.3.59

`source_lemma_15_3_59` proves all four source conclusions from precise earlier
local conclusions through 15.3.58. The residual action and marked Frattini
calculation first place T_K in YU and give its order bound. The centralizer
and coprime-action argument then proves U = O₂(H), and the actual recognized
actor quotient gives the index two. The two compatible s = 1 module actions
identify O²(M) with Y; the Sylow supplement gives M = YT, with both the set
product and an elementwise factorization.

`residualSylow_transfer_of_natural_action` also proves T_K = U C_T(V), with
its set product and element factors. It derives the order eight of the
T-action from the surjective natural M-action and the actual Sylow subgroup.
Only the earlier order-four U-action on V remains an explicit scalar input.

The interfaces retain the literal H-action on U/Z, actual natural/dual and
marked-partner coordinates, the common actor on V and P/V, and relative
normality. No clause of 15.3.59, residual-generation assertion or automizer
normalizer calculation is assumed. The enclosing subsection must supply the
earlier source witnesses; this module completes the conditional 15.3.59
argument without using the later cubic or residual-orbit calculations.
The previous reduction and index interfaces remain publicly available.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.59 on printed pp.1149–1150, with earlier local inputs from
15.3.48–58 on pp.1142–1149 and the natural action from 15.3.2(1).
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core
open Subgroup
open ResidualGeneration

variable {G : Type*} [Group G] [Finite G]

section Residual
variable {T Z ZS V Y Y₁ : Subgroup G} {y t : G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal] [IsExtraspecial 2 (closureU Z ZS)]
variable (d : LocalCoreData T Z ZS V Y)
variable (m : Partner.EarlierGeometry T Z ZS V Y₁ y t)
variable (hY₁ : Y₁ ≤ Y) (hVQ : ¬ V ≤ coreQ Z)
variable (hdisplacement : ⁅closureU Z ZS, V⁆ ≤ V)
variable (hcard : Nat.card (vectorDisplacement Z ZS V) = 4)
variable (hU : Nat.card (closureU Z ZS) = 2 ^ 7)
include d m hY₁ hVQ hdisplacement hcard hU

/-- The first three clauses of 15.3.59 from the genuine earlier local
conclusions and the actual recognized and marked actions. The residual
containment, commutator generation, Frattini calculation and size bound
are discharged before the centralizer and index arguments are applied. -/
theorem core_sylow_and_index_of_earlier_source :
    closureU Z ZS = coreQ Z ∧
      (∃ S : Sylow 2 (Y ⊔ closureU Z ZS : Subgroup G),
        (S : Subgroup (Y ⊔ closureU Z ZS : Subgroup G)).map
          (Y ⊔ closureU Z ZS).subtype = residualSylow T Z) ∧
      ((residualSylow T Z).subgroupOf T).index = 2 := by
  obtain ⟨hUK, hcomm, _, _, hcontain, hlower⟩ :=
    residual_generation_of_earlier_source d m hY₁ hVQ hdisplacement hcard hU
  exact core_sylow_and_index_of_local_calculations T Z ZS V Y d m.sylow
    m.sylow_map m.recognized.actorEquiv hUK hcomm hcontain hlower

open scoped Pointwise in
/-- The transfer description, including its actual product and element
factors. Only the earlier orders of the literal T- and U-actions on V
are supplied; U = Q_H and both residual containments are proved. -/
theorem residualSylow_transfer_of_earlier_source
    (hTaction : Nat.card (conjugationOnV T V d.normalizes_module).range = 8)
    (hUaction : Nat.card (((closureU Z ZS).subgroupOf T).map
      (conjugationOnV T V d.normalizes_module)) = 4) :
    residualSylow T Z = closureU Z ZS ⊔ (T ⊓ centralizer (V : Set G)) ∧
      (residualSylow T Z : Set G) =
        (closureU Z ZS : Set G) * (T ⊓ centralizer (V : Set G) : Subgroup G) ∧
      ∀ k ∈ residualSylow T Z,
        ∃ u ∈ closureU Z ZS, ∃ c ∈ T ⊓ centralizer (V : Set G), k = u * c := by
  have hcore := (core_sylow_and_index_of_earlier_source
    d m hY₁ hVQ hdisplacement hcard hU).1
  have hjoin := transfer_description_of_earlier_source m.recognized m.sylow
    m.sylow_map d.center_closure d.action_kernel d.module_le_sylow
    d.normalizes_module hVQ hdisplacement hcard hTaction hUaction hcore
  exact ⟨hjoin, residualSylow_product_of_join T Z ZS V d.T_le_H hjoin⟩

end Residual

/-- The actual Sylow subgroup induces the Sylow group of order eight in
the natural orthogonal action. This discharges the T-action order used
by the transfer calculation, independently of 15.3.59. -/
theorem sylow_conjugationOnV_card (T : Sylow 2 G) (M V : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (a : NaturalOrthogonalAction M V)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    Nat.card (conjugationOnV (T : Subgroup G) V hTV).range = 8 := by
  let f := a.actor.comp (inclusion hTM)
  have hk : f.ker = (conjugationOnV (T : Subgroup G) V hTV).ker := by
    rw [conjugationOnV_ker, ← MonoidHom.comap_ker, a.ker_actor]
    rfl
  have hr : f.range =
      ((T.subtype hTM).mapSurjective a.onto : Subgroup OrthogonalActor) := by
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype, MonoidHom.range_comp,
      inclusion_range]
  rw [← index_ker, ← hk, index_ker, hr, Sylow.card_eq_multiplicity,
    Automizers.LocalCore.orthogonalActor_card]
  decide +kernel

open scoped Pointwise in
/-- The transfer subgroup with the T-action order discharged by the genuine
natural M-action. The remaining order-four input is the U-action clause
of 15.3.51(2a), on the literal V. This theorem needs no later fusion data. -/
theorem residualSylow_transfer_of_natural_action
    (T : Sylow 2 G) (M Y V Z ZS Y₁ : Subgroup G) (y t : G)
    [(Z.subgroupOf (closureU Z ZS)).Normal] [IsExtraspecial 2 (closureU Z ZS)]
    (d : LocalCoreData (T : Subgroup G) Z ZS V Y)
    (m : Partner.EarlierGeometry (T : Subgroup G) Z ZS V Y₁ y t)
    (hY₁ : Y₁ ≤ Y) (hVQ : ¬ V ≤ coreQ Z)
    (hdisplacement : ⁅closureU Z ZS, V⁆ ≤ V)
    (hcard : Nat.card (vectorDisplacement Z ZS V) = 4)
    (hU : Nat.card (closureU Z ZS) = 2 ^ 7)
    (hTM : (T : Subgroup G) ≤ M) (a : NaturalOrthogonalAction M V)
    (hUaction : Nat.card (((closureU Z ZS).subgroupOf (T : Subgroup G)).map
      (conjugationOnV (T : Subgroup G) V d.normalizes_module)) = 4) :
    residualSylow (T : Subgroup G) Z =
        closureU Z ZS ⊔ ((T : Subgroup G) ⊓ centralizer (V : Set G)) ∧
      (residualSylow (T : Subgroup G) Z : Set G) = (closureU Z ZS : Set G) *
        ((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) ∧
      ∀ k ∈ residualSylow (T : Subgroup G) Z, ∃ u ∈ closureU Z ZS,
        ∃ c ∈ (T : Subgroup G) ⊓ centralizer (V : Set G), k = u * c :=
  residualSylow_transfer_of_earlier_source d m hY₁ hVQ hdisplacement hcard hU
    (sylow_conjugationOnV_card T M V hTM a d.normalizes_module) hUaction

section Supplement
variable (T : Sylow 2 G) (M Y I P V Z ZS Y₁ : Subgroup G) (y t : G)
variable [(Z.subgroupOf (closureU Z ZS)).Normal] [IsExtraspecial 2 (closureU Z ZS)]
variable (d : LocalCoreData (T : Subgroup G) Z ZS V Y)
variable (m : Partner.EarlierGeometry (T : Subgroup G) Z ZS V Y₁ y t)
variable (hY₁ : Y₁ ≤ Y) (hVQ : ¬ V ≤ coreQ Z)
variable (hdisplacement : ⁅closureU Z ZS, V⁆ ≤ V)
variable (hcard : Nat.card (vectorDisplacement Z ZS V) = 4)
variable (hU : Nat.card (closureU Z ZS) = 2 ^ 7)
variable (hTM : (T : Subgroup G) ≤ M) (hI : I = Y ⊔ closureU Z ZS)
variable (hIM : I ≤ M) (hMY : M ≤ normalizer (Y : Set G))
variable (hP : P = Stellmacher.twoCoreAmbient I) (hVP : V ≤ P)
variable {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
variable [(V.subgroupOf P).Normal]
variable (layers : Automizers.Models.LayerActions I Y P V hIP hIV)
variable (a : NaturalOrthogonalAction M V)
variable (hcentral : Y ⊓ centralizer (V : Set G) = Stellmacher.twoCoreAmbient Y)
variable (hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
variable (hcenter : V = (center P).map P.subtype)
include d m hY₁ hVQ hdisplacement hcard hU hTM hI hIM hMY hP hVP layers a
  hcentral hchar hcenter

open scoped Pointwise in
/-- All four conclusions of 15.3.59, conditionally on the earlier local
conclusions through 15.3.58. In addition to M = Y ⊔ T, the conclusion
retains M = YT as a set product and gives factors for every element.

`d` contains the earlier centralizer, fixed-point, normality and scalar
conclusions; `m` contains the literal marked partners and natural/dual
recognition on U/Z. The common actor in `layers` identifies the actions
on V and P/V, with P = O₂(I) and I = YU. The remaining inputs are the
earlier natural M-action, C_Y(V) = O₂(Y), characteristic two in M, and
V = Z(P). None of the four conclusions or the residual identity O²(M) = Y
is an input. The enclosing subsection owns construction of these earlier
source witnesses. -/
theorem source_lemma_15_3_59 :
    closureU Z ZS = coreQ Z ∧
      (∃ S : Sylow 2 (Y ⊔ closureU Z ZS : Subgroup G),
        (S : Subgroup (Y ⊔ closureU Z ZS : Subgroup G)).map
          (Y ⊔ closureU Z ZS).subtype = residualSylow (T : Subgroup G) Z) ∧
      ((residualSylow (T : Subgroup G) Z).subgroupOf (T : Subgroup G)).index = 2 ∧
      M = Y ⊔ (T : Subgroup G) ∧
      (M : Set G) = (Y : Set G) * (T : Set G) ∧
      ∀ x ∈ M, ∃ y ∈ Y, ∃ t ∈ (T : Subgroup G), x = y * t := by
  have hfirst := core_sylow_and_index_of_earlier_source
    d m hY₁ hVQ hdisplacement hcard hU
  have hresidual := Automizers.residual_eq_of_first_three_and_s1_actions
    T M Y I P V Z ZS hTM hI hIM hMY hP hVP layers a hcentral hfirst
    d.Y_perfect hchar hcenter
  have hsylow : ((T.subtype hTM : Sylow 2 M) : Subgroup M).map M.subtype =
      (T : Subgroup G) := map_subgroupOf_eq_of_le hTM
  exact ⟨hfirst.1, hfirst.2.1, hfirst.2.2,
    supplement_of_residual M Y (T : Subgroup G) (T.subtype hTM)
      hsylow hresidual (hTM.trans hMY)⟩

end Supplement
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core
