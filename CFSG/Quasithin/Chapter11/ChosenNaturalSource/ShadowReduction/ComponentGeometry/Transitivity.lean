module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import Theory.Representation.SpecialLinearThreeTransitivity
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry
public import Theory.Representation.G2NaturalTransitivity

/-!
# Nonzero-vector transitivity on the original chosen module

The full SL3, Sp4 and G2 markings supply actual transporters in their natural
modules. Their binary intertwiners transfer those transporters to the literal
central quotient. Once C_V(L) vanishes, the original quotient projection is
injective, so lifting the actor through L/O2(L) gives conjugation transitivity
on V itself. All group and module maps retain the original choice D.

Source: Aschbacher--Smith, 11.0.2(2) and 11.4.1(1), combined manuscript,
1 March 2004, printed pp.759 and 775--776.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)

private theorem transfer_transitive
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) A W)
    (e : ActionEquiv D.centralQuotientAction σ)
    (ht : ∀ x y : W, x ≠ 0 → y ≠ 0 → ∃ a, σ a x = y)
    (x y : D.chosenCentralQuotient) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ a, D.centralQuotientAction a x = y := by
  obtain ⟨a, ha⟩ := ht (e.linearEquiv x) (e.linearEquiv y)
    (fun h => hx (e.linearEquiv.map_eq_zero_iff.mp h))
    (fun h => hy (e.linearEquiv.map_eq_zero_iff.mp h))
  refine ⟨e.groupEquiv.symm a, e.linearEquiv.injective ?_⟩
  rw [e.intertwines, e.groupEquiv.apply_symm_apply]
  exact ha

include S in
/-- All three actual marked natural actions are transitive on nonzero
vectors of the original quotient, without a new orbit premise. -/
theorem centralQuotient_transitive
    (x y : D.chosenCentralQuotient) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ a, D.centralQuotientAction a x = y := by
  cases S.natural with
  | sl3 m =>
    apply transfer_transitive D _ m.some _ x y hx hy
    intro v w hv hw
    exact Matrix.SpecialLinearGroup.exists_mulVec_eq_three v w hv hw
  | sp4 m =>
    apply transfer_transitive D _ m.some _ x y hx hy
    intro v w hv hw
    exact Theory.SpecificGroups.SymplecticFour.TwoLocalCover.nonzero_vector_transitive hv hw
  | g2 m =>
    apply transfer_transitive D _ m.some _ x y hx hy
    intro v w hv hw
    exact Atlas.G2.Natural.action_transitive hv hw

omit [Finite G] in
/-- After fixed-space vanishing the original quotient projection is injective. -/
theorem centralQuotient_injective (hfix : V ⊓ centralizer (L : Set G) = ⊥) :
    Function.Injective D.toCentralQuotient := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro v hv
  apply mem_bot.mpr
  apply Subtype.ext
  have hf : (v : G) ∈ V ⊓ centralizer (L : Set G) :=
    ⟨v.property, (LocalGeometry.quotient_eq_one_iff D v).mp hv⟩
  exact mem_bot.mp (hfix ▸ hf)

/-- The literal quotient map intertwines the original chosen action. -/
theorem centralQuotient_chosenAction (l : L) (v : D.space) :
    D.toCentralQuotient (D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l v))) =
      Multiplicative.ofAdd (D.centralQuotientAction (QuotientGroup.mk' (pCore 2 L) l)
        (D.toCentralQuotient (D.spaceEquiv (Multiplicative.ofAdd v))).toAdd) := by
  change Multiplicative.ofAdd (Submodule.Quotient.mk
      (D.spaceEquiv.symm (D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l v)))).toAdd) =
    Multiplicative.ofAdd (D.centralQuotientAction (QuotientGroup.mk' (pCore 2 L) l)
      (Submodule.Quotient.mk (D.spaceEquiv.symm
        (D.spaceEquiv (Multiplicative.ofAdd v))).toAdd))
  rw [D.spaceEquiv.symm_apply_apply, D.spaceEquiv.symm_apply_apply]
  rfl

include D S in
/-- The transitivity clause of 11.4.1(1) on the original ambient V. -/
theorem vector_transitive (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    {x y : G} (hx : x ∈ V) (hy : y ∈ V) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ l ∈ L, (MulAut.conj l) x = y := by
  let v : V := ⟨x, hx⟩
  let w : V := ⟨y, hy⟩
  have hinj := centralQuotient_injective D hfix
  have hv : (D.toCentralQuotient v).toAdd ≠ 0 := by
    intro he
    have hv1 : v = 1 := hinj (he.trans (D.toCentralQuotient.map_one).symm)
    exact hx1 (congrArg V.subtype hv1)
  have hw : (D.toCentralQuotient w).toAdd ≠ 0 := by
    intro he
    have hw1 : w = 1 := hinj (he.trans (D.toCentralQuotient.map_one).symm)
    exact hy1 (congrArg V.subtype hw1)
  obtain ⟨a, ha⟩ := centralQuotient_transitive D S _ _ hv hw
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) a
  let v' := (D.spaceEquiv.symm v).toAdd
  have he : D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l v')) = w := by
    apply hinj
    have hv' : D.spaceEquiv (Multiplicative.ofAdd v') = v := D.spaceEquiv.apply_symm_apply v
    rw [centralQuotient_chosenAction, hv']
    exact congrArg Multiplicative.ofAdd ha
  refine ⟨l, l.property, ?_⟩
  have hval : (v'.val.toMul.val : G) = x :=
    (D.spaceEquiv_apply v').symm.trans
      (congrArg V.subtype (D.spaceEquiv.apply_symm_apply v))
  have hh := congrArg (fun v : V => (v : G)) he
  rw [D.spaceEquiv_apply] at hh
  change (l : G) * (v'.val.toMul.val : G) * (l : G)⁻¹ = y at hh
  change (l : G) * x * (l : G)⁻¹ = y
  rwa [hval] at hh
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
