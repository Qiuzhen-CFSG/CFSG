module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.Relations
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.ComponentRecognition
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.ComplementAction
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.Marking
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Product embedding from the concrete HS subgroup calculations

Conjugation embeds the fixed candidate `H` in `Aut(D)` once its centralizer
of `D` is trivial. An actual equivalence `D ≃* A6` and the order of `H` then
make this action all of `MulAut A6`, whose order 1440 is already proved.
Since `t` centralizes `D`, faithfulness also proves that `H` meets `⟨t⟩`
trivially. Multiplication therefore embeds the exact product in `C(t)`.

The unconditional `exists_embedding` assembles the separately checked concrete
recognition of `D`, the order of `H`, and the triviality of `C_H(D)`. The
conditional assembly remains available. No assertion of the full centralizer's
order or structure is used.

Source: Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3 Table 5.3m,
class 2B. The words and checked relative normality are in the sibling
`ProductEmbedding.Seed` and `ProductEmbedding.Relations` modules.
-/

public section

namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding
open Sporadic.LeechRelated.HS Subgroup

local notation "C" => centralizer (Set.singleton t : Set Carrier)

/-- Conjugation on the actual normalized subgroup `D`. -/
def conjugationAction : H →* MulAut D :=
  D.normalizerMonoidHom.comp (Subgroup.inclusion H_le_normalizer)

/-- The action is literal conjugation in the exact ATLAS carrier. -/
theorem conjugationAction_apply (h : H) (d : D) :
    (conjugationAction h d : Carrier) = (h : Carrier) * (d : Carrier) * (h : Carrier)⁻¹ := by
  rfl

/-- A trivial relative centralizer makes the conjugation action faithful. -/
theorem conjugationAction_injective
    (hC : H ⊓ centralizer (D : Set Carrier) = ⊥) :
    Function.Injective conjugationAction := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro h hh
  have he : conjugationAction h = 1 := hh
  have hc : (h : Carrier) ∈ centralizer (D : Set Carrier) := by
    intro d hd
    have he' := congrArg (fun a : MulAut D => (a ⟨d, hd⟩ : Carrier)) he
    change (h : Carrier) * d * (h : Carrier)⁻¹ = d at he'
    exact ((mul_inv_eq_iff_eq_mul).mp he').symm
  have hb : (h : Carrier) ∈ (⊥ : Subgroup Carrier) := hC ▸ ⟨h.property, hc⟩
  exact Subtype.ext (mem_bot.mp hb)

/-- Recognition and equal finite orders identify the entire automorphism factor. -/
noncomputable def automorphismEquiv (e : D ≃* A6)
    (hcard : Nat.card H = 1440) (hC : H ⊓ centralizer (D : Set Carrier) = ⊥) :
    H ≃* MulAut A6 := by
  let f : H →* MulAut A6 := (MulAut.congr e).toMonoidHom.comp conjugationAction
  apply MulEquiv.ofBijective f
  apply (Nat.bijective_iff_injective_and_card f).mpr
  exact ⟨(MulAut.congr e).injective.comp (conjugationAction_injective hC),
    hcard.trans AlternatingSix.ShadowLocal.card_aut.symm⟩

/-- The marked involution supplies exactly the `C2` carrier from `Statements`. -/
noncomputable def involutionEquiv : C2 ≃* zpowers t :=
  mulEquivOfCyclicCardEq (by
    rw [Nat.card_zpowers, t_order]
    change Nat.card (Multiplicative (ZMod 2)) = 2
    simp)

private theorem cyclic_le_centralizer : zpowers t ≤ C :=
  zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)

private theorem cyclic_le_centralizer_D : zpowers t ≤ centralizer (D : Set Carrier) := by
  apply zpowers_le.mpr
  intro d hd
  exact mem_centralizer_singleton_iff.mp (D_le_centralizer hd)

private theorem cyclic_commutes_H (z : zpowers t) (h : H) :
    Commute (z : Carrier) (h : Carrier) := by
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp z.property
  rw [← hn]
  exact (show Commute t (h : Carrier) from
    (mem_centralizer_singleton_iff.mp (H_le_centralizer h.property)).symm).zpow_left n

private def localProduct : zpowers t × H →* C :=
  (Subgroup.inclusion cyclic_le_centralizer).noncommCoprod
    (Subgroup.inclusion H_le_centralizer)
    (fun z h => show Commute _ _ from Subtype.ext (cyclic_commutes_H z h).eq)

private theorem localProduct_injective
    (hC : H ⊓ centralizer (D : Set Carrier) = ⊥) :
    Function.Injective localProduct := by
  have hd : Disjoint (zpowers t) H := by
    apply disjoint_def.mpr
    intro x hx hH
    exact mem_bot.mp (hC ▸ (show x ∈ H ⊓ centralizer (D : Set Carrier) from
      ⟨hH, cyclic_le_centralizer_D hx⟩))
  intro x y he
  exact mul_injective_of_disjoint hd (congrArg Subtype.val he)

/-- All remaining inputs concern the fixed concrete subgroups. The map is
constructed from the faithful conjugation action, whose image is all of Aut(A₆)
by the proved automorphism-group order; multiplication adds the cyclic factor. -/
theorem exists_embedding_of_component_and_action
    (e : D ≃* A6) (hcard : Nat.card H = 1440)
    (hC : H ⊓ centralizer (D : Set Carrier) = ⊥) :
    ∃ f : C2 × MulAut A6 →* C, Function.Injective f := by
  let eH := automorphismEquiv e hcard hC
  let eP := involutionEquiv.prodCongr eH.symm
  exact ⟨localProduct.comp eP.toMonoidHom,
    (localProduct_injective hC).comp eP.injective⟩

/-- The exact source product embeds in the centralizer of the fixed marked HS
involution. All recognition, order, and faithfulness inputs are discharged by
the concrete subgroup calculations. -/
theorem exists_embedding :
    ∃ f : C2 × MulAut A6 →* C, Function.Injective f := by
  obtain ⟨e⟩ := D_equiv_A6
  exact exists_embedding_of_component_and_action e H_card H_inf_centralizer_D

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding
