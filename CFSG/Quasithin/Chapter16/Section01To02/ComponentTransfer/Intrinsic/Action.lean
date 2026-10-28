module

public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Basic
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# The actual involutory action in the proper component branch

Conjugation by t restricts to an automorphism of K and induces an automorphism
of K/O₂(K). In the proper component branch both automorphisms have order two:
if the first were trivial, relative component maximality would force L = K;
faithfulness on the central quotient gives the second assertion.

The pointwise transport equations identify these actions under any supplied
model equivalence. They do not classify the model automorphism as graph,
field, or graph-field. Such classification still requires the intrinsic tables.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.2(1), 16.1.3–16.1.5 and the proof of 16.1.7, pp.1170–1173.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.ComponentTransfer.Intrinsic

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] {K L : Subgroup G} {t : G}

/-- The restriction of conjugation by t to the actual normalized subgroup K. -/
def action (hn : t ∈ normalizer K) : MulAut K := K.normalizerMonoidHom ⟨t, hn⟩

/-- The induced automorphism acts by ambient conjugation. -/
theorem action_apply (hn : t ∈ normalizer K) (x : K) :
    (action hn x : G) = t * x * t⁻¹ := rfl

/-- Fixed points are exactly the elements of K centralizing t. -/
theorem mem_fixed_action (hn : t ∈ normalizer K) (x : K) :
    x ∈ (action hn).fixedSubgroup ↔ (x : G) ∈ involutionCentralizer t := by
  rw [MulAut.mem_fixedSubgroup, Subtype.ext_iff, action_apply,
    mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul, eq_comm]

/-- Identify the embedded centralizer with the intrinsic fixed subgroup. -/
def centralizerEquivFixed (hn : t ∈ normalizer K) :
    centralizerIn K t ≃* (action hn).fixedSubgroup where
  toFun x := ⟨⟨x, x.property.1⟩, (mem_fixed_action hn _).mpr x.property.2⟩
  invFun x := ⟨x, x.val.property, (mem_fixed_action hn _).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Transport of the action on K is tied to the actual conjugation map. -/
theorem model_action_transport {M : Type*} [Group M] (e : K ≃* M)
    (hn : t ∈ normalizer K) (x : K) :
    MulAut.congr e (action hn) (e x) = e (action hn x) := by
  change e (action hn (e.symm (e x))) = _
  rw [e.symm_apply_apply]

/-- Proper component containment makes the induced action an involution. -/
theorem action_order (ht : orderOf t = 2) (hn : t ∈ normalizer K)
    (hL : IsCentralizerComponent t L) [IsQuasisimple K] (hLK : L < K) :
    orderOf (action hn) = 2 := by
  have hs : action hn ^ 2 = 1 := by
    change K.normalizerMonoidHom (⟨t, hn⟩ : normalizer K) ^ 2 = 1
    rw [← map_pow, show (⟨t, hn⟩ : normalizer K) ^ 2 = 1 from
      Subtype.ext (ht ▸ pow_orderOf_eq_one t), map_one]
  apply orderOf_eq_prime hs
  intro he
  have hc : K ≤ involutionCentralizer t := by
    intro x hx
    exact (mem_fixed_action hn ⟨x, hx⟩).mp (by simp [he, MulAut.mem_fixedSubgroup])
  have hcomp := IsComponentIn.restrict hL hLK.le hc
  have htop : IsComponent K (⊤ : Subgroup K) :=
    ⟨.top, IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩
  have heq := hcomp.2.eq_of_le htop le_top
  exact hLK.not_ge (subgroupOf_eq_top.mp heq)

/-- The actual induced action on K/O₂(K). -/
def quotientAction (hn : t ∈ normalizer K) : MulAut (K ⧸ pCore 2 K) :=
  (pCore 2 K).quotientAut (action hn)

/-- The quotient action commutes with the canonical quotient map. -/
theorem quotientAction_apply (hn : t ∈ normalizer K) (x : K) :
    quotientAction hn (QuotientGroup.mk' (pCore 2 K) x) =
      QuotientGroup.mk' (pCore 2 K) (action hn x) :=
  quotientAut_apply_mk _ _ _

/-- Transport to a quotient model retains the quotient conjugation equation. -/
theorem quotient_model_action_transport {M : Type*} [Group M]
    (e : (K ⧸ pCore 2 K) ≃* M) (hn : t ∈ normalizer K) (x : K) :
    MulAut.congr e (quotientAction hn) (e (QuotientGroup.mk' (pCore 2 K) x)) =
      e (QuotientGroup.mk' (pCore 2 K) (action hn x)) := by
  change e (quotientAction hn (e.symm (e _))) = _
  rw [e.symm_apply_apply, quotientAction_apply]

/-- Perfectness and the center/core equality preserve the order on the quotient. -/
theorem quotientAction_order [Finite G] {𝒦 : GroupClass}
    (hG : Hypothesis1611 𝒦 G) {i : G} (h : Setup t i L)
    (hK : IsCentralizerComponent i K) (hn : t ∈ normalizer K) (hLK : L < K) :
    orderOf (quotientAction hn) = 2 := by
  let := hK.quasisimple
  have hc := hG.evenType.component_center_eq_twoCore h.involution_i hK
  have hf : Function.Injective ((pCore 2 K).quotientAut) := by
    intro a b hab
    apply MulAut.quotient_center_injective
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center K) q
    simp only [quotientAut_apply_mk]
    apply QuotientGroup.eq.mpr
    rw [hc]
    have he := congrArg
      (fun c : MulAut (K ⧸ pCore 2 K) => c (QuotientGroup.mk' (pCore 2 K) x)) hab
    rw [quotientAut_apply_mk, quotientAut_apply_mk] at he
    exact QuotientGroup.eq.mp he
  exact (orderOf_injective (pCore 2 K).quotientAut hf _).trans
    (action_order h.involution_t hn h.component hLK)

end CFSG.Quasithin.Chapter16.ComponentTransfer.Intrinsic
