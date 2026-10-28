module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.NaturalCovers
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# Faithfulness across the binary natural chief flag

The full kernel of a noncentral section is contained in the embedded center
of F*. For the binary SL4 and SL5 groups that center is trivial. Hence every
noncentral member of the original LA-chief flag is faithful for LA, before
any further module identification. The statement retains the literal section
representations and consumes the source natural-group marking.

Source: Aschbacher--Smith B.5.1, pp.100–101, the covering step after (++).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem faithful_of_centerfree_fitting [Finite G]
    [IsQuasisimple (generalizedFitting G)]
    (hz : center (generalizedFitting G) = ⊥)
    (hn : subspaceCommutator ρ ⊤ (generalizedFitting G) ≠ ⊥) :
    Function.Injective ρ := by
  have hk := section_kernel_central ρ inferInstance hn
  rw [hz, Subgroup.map_bot] at hk
  have hi : Function.Injective (actionHom ρ) := (MonoidHom.ker_eq_bot_iff _).mp (bot_unique hk)
  intro x y hxy
  apply hi
  apply imageRepresentation_injective ρ
  exact hxy

/-- In the binary degree-four/five families every noncentral chief factor
is already faithful on the original LA actor, since its central kernel is trivial. -/
theorem binary_flag_factor_faithful [Finite G]
    [IsQuasisimple (generalizedFitting G)]
    {d : ℕ} (hd : d = 4 ∨ d = 5) (e : generalizedFitting G ≃* SL(d,ZMod 2))
    (f : ReducibleChiefFlag ρ (generalizedFitting G)) {i : ℕ} (hi : i ∈ f.noncentral) :
    Function.Injective (sectionRepresentation ρ (f.chain i) (f.chain (i + 1))) := by
  have hz : center (generalizedFitting G) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [Nat.card_congr (centerCongr e).toEquiv,
      BinaryLinear.OuterCyclic.binary_center_eq_bot (by rcases hd with rfl | rfl <;> decide)]
    exact Subgroup.card_bot
  exact faithful_of_centerfree_fitting _ hz ((f.mem_noncentral i).mp hi).2

/-- The actual original source LA chief flag inherits faithfulness in both
binary natural alternatives; no image actor is substituted in the conclusion. -/
theorem binary_source_flag_faithful [Finite G]
    {K : GroupClass.{u}} {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (e : L ≃* SL(d,ZMod 2))
    {A : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (f : ReducibleChiefFlag (ρ.comp (L ⊔ A).subtype) (generalizedFitting ↥(L ⊔ A)))
    {i : ℕ} (hi : i ∈ f.noncentral) :
    Function.Injective (sectionRepresentation (ρ.comp (L ⊔ A).subtype)
      (f.chain i) (f.chain (i + 1))) := by
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  let H := L ⊔ A
  have hp : IsPGroup 2 A := hA.1.1.2.isPGroup 2 A
  have hfit : generalizedFitting H = L.subgroupOf H :=
    IrreducibleBranch.local_generalizedFitting L A h.fitting h.twoCore hp
  let : IsQuasisimple (L.subgroupOf H) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).symm
  let : IsQuasisimple (generalizedFitting H) := hfit.symm ▸ inferInstance
  exact binary_flag_factor_faithful (ρ.comp H.subtype) hd
    ((MulEquiv.subgroupCongr hfit).trans
      ((subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).trans e)) f hi

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
