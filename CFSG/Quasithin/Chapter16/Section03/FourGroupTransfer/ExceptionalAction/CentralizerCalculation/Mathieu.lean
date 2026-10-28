module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Bounds
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Transport
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Quotient
public import Theory.GroupTheory.CentralKernelSubgroupEmbedding
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The M₁₂–A₅ fixer calculation: transport to the concrete model

The image of the actual embedded L under I → I/O₂(I) ≃ M₁₂ is still A₅:
the kernel is central and A₅ has trivial center. Faithful descent of cover
automorphisms and the given order-four action provide a lower bound of four
for the pointwise fixer of this image. A concrete model calculation then
transfers its upper bound and square identities back to I.

`ModelBound` specifies the remaining intrinsic M₁₂ calculation. It is not
asserted here. In particular `mathieuBound_of_model` is a conditional
assembly, not a proof of the source theorem without that input. The model
input includes the available lower bound, so no calculation for embeddings
with trivial fixer is required. It neither presupposes that E is elementary
abelian nor that every quotient automorphism lifts to I.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.5(4),
16.1.7(3f), and 16.3.5, printed pp.1171–1173 and 1178–1179. The exact
involution-table statements and partial proofs are in
`OtherPreliminaries.Mathieu.Statements` and `OtherPreliminaries.Mathieu.M12Table`;
they do not already assert this full automorphism-fixer calculation.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Mathieu
open Subgroup Theory.GroupTheory ClassificationModels Sporadic.Mathieu
universe u
variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
variable {E L I : Subgroup G} {t i : G}

/-- The outstanding concrete calculation, restricted to fixers large enough
to contain the faithful order-four action. This definition asserts no bound. -/
def ModelBound : Prop :=
  ∀ P : Subgroup M12, Nonempty (P ≃* alternatingGroup (Fin 5)) →
    4 ≤ Nat.card (fixingSubgroup (MulAut M12) (P : Set M12)) →
    Nat.card (fixingSubgroup (MulAut M12) (P : Set M12)) ≤ 4 ∧
      ∀ a : fixingSubgroup (MulAut M12) (P : Set M12), a ^ 2 = 1

/-- The projected subgroup keeps the actual embedding in the specified M₁₂ model. -/
noncomputable def projected (h : PairContext E L I t i) (hG : Hypothesis1611 𝒦 G)
    (e : (I ⧸ pCore 2 I) ≃* M12) : Subgroup M12 :=
  (L.subgroupOf I).map (h.coreCover hG e).toMonoidHom

/-- A₅ survives the actual central quotient without a kernel. -/
theorem projected_equiv (h : PairContext E L I t i) (hG : Hypothesis1611 𝒦 G)
    (e : (I ⧸ pCore 2 I) ≃* M12) (eL : L ≃* alternatingGroup (Fin 5)) :
    Nonempty (projected h hG e ≃* alternatingGroup (Fin 5)) := by
  let P := L.subgroupOf I
  let a := (subgroupOfEquivOfLe h.proper.le).trans eL
  have hc : center P = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hm : a x ∈ center (alternatingGroup (Fin 5)) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := a.surjective y
      rw [← map_mul, ← map_mul, mem_center_iff.mp hx y]
    have hx1 : a x = 1 := by
      simpa only [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 5)),
        mem_bot] using hm
    apply mem_bot.mpr
    exact a.injective (hx1.trans (map_one a).symm)
  let f := h.coreCover hG e
  exact ⟨(f.toMonoidHom.subgroupMapEquivOfKerLeCenter f.ker_le_center P hc).symm.trans a⟩

/-- The inherited faithful order-four action forces the projected fixer to
have order at least four, even when the cover is nontrivial. -/
theorem four_le_projected_fixer (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* M12) :
    4 ≤ Nat.card (fixingSubgroup (MulAut M12) (projected h hG e : Set M12)) := by
  calc
    4 = Nat.card E := h.card.symm
    _ ≤ Nat.card (pairFixer L I) :=
      card_le_pairFixer h.normalizes h.centralizes h.faithful
    _ ≤ Nat.card (fixingSubgroup (MulAut M12) (projected h hG e : Set M12)) :=
      Nat.le_of_dvd Nat.card_pos
        ((h.coreCover hG e).card_fixing_dvd (h.coreCover_kernel hG e) (L.subgroupOf I))

/-- Conditional assembly through the actual projected A₅. The intrinsic
`ModelBound` remains a separate proof obligation. -/
theorem mathieuBound_of_model (hmodel : ModelBound)
    (h : PairContext E L I t i) (hG : Hypothesis1611 𝒦 G) : MathieuBound L I := by
  change Nonempty ((I ⧸ pCore 2 I) ≃* M12) →
    Nonempty (L ≃* alternatingGroup (Fin 5)) → FourBound L I
  rintro ⟨e⟩ ⟨eL⟩
  obtain ⟨hb, hsq⟩ := hmodel (projected h hG e) (projected_equiv h hG e eL)
    (four_le_projected_fixer h hG e)
  exact fourBound_of_cover (h.coreCover hG e) (h.coreCover_kernel hG e) hb hsq

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Mathieu
