module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.OddNormalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.ResidualSelection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# The selected outside subgroup and its literal quotient action

The original choice of H and K=L₁ put O²(H) in the actual quotient kernel
Y. Define X₁=C_X(K/O₂(K)) and C=⟨R₁,O²(H),X₁⟩, retaining the original
chosen module and point. Conjugation on W/(V₁.subgroupOf W) constructs
the action of every subgroup of G₁. Its kernel is characterized by the
literal commutators [a,W]≤V₁, and its quotient acts faithfully.

These constructions supply the common action for the two endings of
11.5.7. They do not assert the multiplicity-space embedding or its odd
order; those require the actual two-copy natural marking and block splitting.
Source: Aschbacher--Smith, combined manuscript, 11.5.7, printed p.782.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
open Subgroup
open scoped commutatorElement
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

def X₁ : Subgroup G := E.X ⊓ coreQuotientCentralizer E.K
def C : Subgroup G := (E.R₁ ⊔ outsideResidual E) ⊔ X₁ E

theorem seed_normalizer_le_M : normalizer (V : Set G) ≤ E.M :=
  D.normal_subgroup_normalizer_le E.input.source.toHypothesis1221
    (D.le_sylow.trans le_sup_right) D.ne_bot
    (sup_le D.normalizes E.input.sylow_normalizes)

theorem seed_le_point_normalizer : V ≤ E.G₁ := by
  let := D.elementary
  exact ((le_centralizer V).trans (centralizer_le E.V₁_le)).trans
    (Subgroup.centralizer_le_normalizer _)

theorem closure_le_point_normalizer : E.W ≤ E.G₁ :=
  conjugateSpanBy_le_self (seed_le_point_normalizer E)

theorem point_le_closure : E.V₁ ≤ E.W :=
  E.V₁_le.trans (le_conjugateSpanBy V E.G₁)

instance point_normal_in_closure : (E.V₁.subgroupOf E.W).Normal :=
  normal_subgroupOf_of_le_normalizer (closure_le_point_normalizer E)

theorem residual_le_Y
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHG : E.H ≤ E.G₁) (hKL : E.K = E.L₁)
    (hpoint : outsideResidual E ≤ centralizer (E.V₁ : Set G))
    (hselect : outsideResidual E ≤ E.K ∨
      ⁅E.K, outsideResidual E⁆ ≤ E.K.pCoreIn 2) : outsideResidual E ≤ E.Y := by
  have hc := E.selected_residual_centralizes_of_equal E.H hH
    D.sylow_normalizes_component hKL hselect
  rw [commutator_comm] at hc
  apply le_inf hpoint
  intro a ha
  let b : normalizer (E.K : Set G) :=
    ⟨a, E.G₁_normalizes_K (hHG (map_subtype_le _ ha))⟩
  refine ⟨b, ?_, rfl⟩
  apply MonoidHom.mem_ker.mpr
  ext z
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 E.K) z
  rw [coreQuotientAction_apply_mk]
  change QuotientGroup.mk' (pCore 2 E.K) (E.K.normalizerMonoidHom b k) =
    QuotientGroup.mk' (pCore 2 E.K) k
  apply QuotientGroup.eq_iff_div_mem.mpr
  obtain ⟨c, hcp, hce⟩ := hc (commutator_mem_commutator ha k.property)
  have he : c = E.K.normalizerMonoidHom b k / k := by
    apply Subtype.ext
    rw [div_eq_mul_inv, coe_mul, coe_inv, normalizerMonoidHom_apply_apply_coe]
    exact hce
  exact he ▸ hcp

theorem C_le_point_normalizer (hTG : (T : Subgroup G) ≤ E.G₁)
    (hHG : E.H ≤ E.G₁) (hXG : E.X ≤ E.G₁) : C E ≤ E.G₁ :=
  sup_le (sup_le ((pCoreIn_le 2 _).trans
    (sup_le (pointResidual_le_G₁ E) hTG)) ((map_subtype_le _).trans hHG))
    (inf_le_left.trans hXG)

def quotientAction (A : Subgroup G) (hA : A ≤ E.G₁) :
    A →* MulAut (E.W ⧸ E.V₁.subgroupOf E.W) := by
  let := point_normal_in_closure E
  exact Classical.choose (exists_quotient_conjugation_action A E.W E.V₁
    (hA.trans (le_normalizer_conjugateSpanBy V E.G₁)) hA
    (point_normal_in_closure E))

theorem quotientAction_apply_mk (A : Subgroup G) (hA : A ≤ E.G₁)
    (a : A) (u : E.W) :
    let := point_normal_in_closure E
    quotientAction E A hA a (QuotientGroup.mk' (E.V₁.subgroupOf E.W) u) =
      QuotientGroup.mk' (E.V₁.subgroupOf E.W)
        ⟨(a : G) * (u : G) * (a : G)⁻¹,
          (mem_normalizer_iff.mp
            ((hA.trans (le_normalizer_conjugateSpanBy V E.G₁)) a.property) u).mp
              u.property⟩ := by
  exact Classical.choose_spec (exists_quotient_conjugation_action A E.W E.V₁
    (hA.trans (le_normalizer_conjugateSpanBy V E.G₁)) hA
    (point_normal_in_closure E)) a u

def actionCentralizer (A : Subgroup G) (hA : A ≤ E.G₁) : Subgroup A :=
  (quotientAction E A hA).ker

theorem mem_actionCentralizer_iff (A : Subgroup G) (hA : A ≤ E.G₁) (a : A) :
    a ∈ actionCentralizer E A hA ↔ ∀ u ∈ E.W, ⁅(a : G), u⁆ ∈ E.V₁ := by
  let := point_normal_in_closure E
  constructor
  · intro ha u hu
    have he := congrArg (fun f : MulAut (E.W ⧸ E.V₁.subgroupOf E.W) =>
      f (QuotientGroup.mk' (E.V₁.subgroupOf E.W) ⟨u, hu⟩))
      (MonoidHom.mem_ker.mp ha)
    rw [quotientAction_apply_mk] at he
    have hc := QuotientGroup.eq_iff_div_mem.mp he
    simpa only [mem_subgroupOf, div_eq_mul_inv, coe_mul, coe_inv,
      commutatorElement_def] using hc
  · intro hc
    apply MonoidHom.mem_ker.mpr
    ext z
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (E.V₁.subgroupOf E.W) z
    rw [quotientAction_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa only [mem_subgroupOf, div_eq_mul_inv, coe_mul, coe_inv,
      commutatorElement_def] using hc u u.property

instance actionCentralizer_normal (A : Subgroup G) (hA : A ≤ E.G₁) :
    (actionCentralizer E A hA).Normal := MonoidHom.normal_ker _

def faithfulAction (A : Subgroup G) (hA : A ≤ E.G₁) :
    (A ⧸ actionCentralizer E A hA) →* MulAut (E.W ⧸ E.V₁.subgroupOf E.W) :=
  QuotientGroup.lift _ (quotientAction E A hA) le_rfl

theorem faithfulAction_injective (A : Subgroup G) (hA : A ≤ E.G₁) :
    Function.Injective (faithfulAction E A hA) := by
  exact QuotientGroup.kerLift_injective _

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
