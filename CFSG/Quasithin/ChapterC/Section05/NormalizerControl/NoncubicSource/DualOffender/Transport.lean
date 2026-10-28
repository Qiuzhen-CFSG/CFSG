module
public import Theory.Representation.CentralizerQuotientAction
public import Theory.Representation.QuadraticDuality
public import Theory.Representation.BinaryOffender.QuadraticSection
/-!
# B.4.7 on the canonical binary conjugation action

Linear displacements in the literal centralizer quotient lie in the actual
commutator subgroup. Annihilator duality bounds the dual fixed codimension
by its binary rank and transports quadraticity. The actor order is computed
from the original centralizer kernel, with no action-coordinate certificate.
Source: Aschbacher–Smith B.4.7 and C.5.13, printed pp.90 and162.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
variable {G : Type*} [Group G] [Finite G]
/-- B.4.7 on the literal centralizer quotient: the dual fixed codimension
is bounded by the binary rank of the actual commutator subgroup. -/
theorem canonical_dual_bounds (V B E : Subgroup G)
    [V.Normal] [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 B]
    (hcomm : ⁅B,V⁆ ≤ E) (hEC : E ≤ centralizer (B : Set G))
    (hne : ¬ B ≤ centralizer (V : Set G)) :
    let q := QuotientGroup.mk' (centralizer (V : Set G))
    let A := B.map q
    IsElementaryTwo A ∧ IsQuadratic (centralizerQuotient V).dual A ∧
      fixedCodim (centralizerQuotient V).dual A ≤ Nat.log 2 (Nat.card E) := by
  let q := QuotientGroup.mk' (centralizer (V : Set G))
  let A := B.map q
  let ρ := centralizerQuotient V
  let σ : Representation (ZMod 2) A (Additive V) := ρ.comp A.subtype
  let C : Submodule (ZMod 2) (Additive V) :=
    AddSubgroup.toZModSubmodule 2 ((E.subgroupOf V).toAddSubgroup)
  have hdisp (a : A) (v : Additive V) : ((σ a v-v).toMul : G) ∈ E := by
    obtain ⟨b,hb,he⟩ := a.property
    change q b = (a : G ⧸ centralizer (V : Set G)) at he
    simp only [toMul_sub,div_eq_mul_inv,Subgroup.coe_mul,Subgroup.coe_inv]
    change (((ρ (a : G ⧸ centralizer (V : Set G)) v).toMul : G) * (v.toMul : G)⁻¹) ∈ E
    rw [← he,centralizerQuotient_apply]
    exact hcomm (commutator_mem_commutator hb v.toMul.property)
  have hC : Coinvariants.ker σ ≤ C := by
    rw [Coinvariants.ker,Submodule.span_le]
    rintro _ ⟨⟨a,v⟩,rfl⟩
    exact hdisp a v
  have hfixed : C ≤ σ.invariants := by
    intro w hw a
    obtain ⟨b,hb,he⟩ := a.property
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((ρ (a : G ⧸ centralizer (V : Set G)) w).toMul : G) = (w.toMul : G)
    rw [← he,centralizerQuotient_apply]
    have hc : b * (w.toMul : G) = (w.toMul : G) * b := hEC hw b hb
    rw [hc,mul_inv_cancel_right]
  have hdual := (commutator_le_invariants_iff_dual σ).mp (hC.trans hfixed)
  have hquad : IsQuadratic ρ.dual A := by
    intro a ha b hb v
    exact (commutator_le_invariants_iff σ.dual).mp hdual ⟨a,ha⟩ ⟨b,hb⟩ v
  have hc : Nat.card (Coinvariants.ker σ) ≤ Nat.card E :=
    Nat.card_le_card_of_injective (fun w : Coinvariants.ker σ =>
      (⟨w.val.toMul,hC w.property⟩ : E)) (by
        intro a b he
        apply Subtype.ext
        apply Additive.toMul.injective
        apply Subtype.ext
        exact congrArg (fun e : E => (e : G)) he)
  have hdim : Module.finrank (ZMod 2) (Coinvariants.ker σ) ≤ Nat.log 2 (Nat.card E) := by
    have hh := Nat.log_monotone (b := 2) hc
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      Nat.log_pow (by decide : 1 < 2)] at hh
    exact hh
  refine ⟨⟨?_,IsElementaryAbelian.map q⟩,hquad,?_⟩
  · intro hz
    have hh := (map_eq_bot_iff B).mp hz
    exact hne (by simpa only [q,QuotientGroup.ker_mk'] using hh)
  · change Module.finrank (ZMod 2) (Module.Dual (ZMod 2) (Additive V) ⧸ σ.dual.invariants) ≤ _
    rw [finrank_dual_quotient_invariants]
    exact hdim

omit [Finite G] in
/-- The canonical actor order is the original index of its actual kernel. -/
theorem canonical_actor_card (V B E : Subgroup G) [V.Normal]
    (hE : B ⊓ centralizer (V : Set G) = E) :
    Nat.card (B.map (QuotientGroup.mk' (centralizer (V : Set G)))) = E.relIndex B := by
  rw [← relIndex_ker,QuotientGroup.ker_mk',← inf_relIndex_left,hE]
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
