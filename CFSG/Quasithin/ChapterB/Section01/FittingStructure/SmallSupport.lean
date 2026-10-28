module

public import Theory.Representation.BinaryGroupAction
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDecomposition
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.Basic

/-!
# Independent binary planes in the Fitting subgroup

We apply the proved D.2.12(1–2) to the actual elementary abelian group
underlying the binary representation. `BinaryGroupAction` identifies its
commutator supports, dimensions and fixed points with the original subspaces.
Thus all cubic factors with two-dimensional support commute and form an
internal independent family; their supports are independent and distinct
factors fix one another's supports.

The final application uses the specific family {[F(G),A] ≠ 1 : A ∈ P*}.
The separate `LocalPlaneLaw` input supplies only the individual cubic orders
and plane dimensions; global independence and generation follow here. This
conditional application is the D.2.12 step of B.1.9, not the completed B.1.9.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.1.9,
printed p.71, and D.2.12(1–2), printed pp.183–184.
-/

@[expose] public section

open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.FittingStructure
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

variable [Finite G] [FiniteDimensional (ZMod 2) V]

omit [Finite G] in
theorem mem_smallFittingFactors_iff (X : Subgroup G) :
    letI := Representation.BinaryGroupAction.action ρ
    X ∈ smallFittingFactors ρ ↔
      X ∈ ChapterD.smallSupportFactors G (Multiplicative V) 1 := by
  let := Representation.BinaryGroupAction.action ρ
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  rw [Representation.BinaryGroupAction.commutator_card]
  norm_num only [mul_one, Nat.reduceAdd, Nat.reducePow]
  exact and_congr_right (fun _ => and_congr_right (fun _ =>
    ⟨fun h => by rw [h]; rfl, fun h => Nat.pow_right_injective (by decide) h⟩))

theorem smallFittingFactors_decomposition (hρ : Function.Injective ρ) :
    iSupIndep (fun X : smallFittingFactors ρ => X.val) ∧
    (∀ X ∈ smallFittingFactors ρ, ∀ Y ∈ smallFittingFactors ρ,
      X ≤ Subgroup.centralizer (Y : Set G)) ∧
    iSupIndep (fun X : smallFittingFactors ρ => subspaceCommutator ρ ⊤ X.val) ∧
    subspaceCommutator ρ ⊤ (sSup (smallFittingFactors ρ)) =
      ⨆ X : smallFittingFactors ρ, subspaceCommutator ρ ⊤ X.val := by
  let := Representation.BinaryGroupAction.action ρ
  let := Representation.BinaryGroupAction.elementary (V := V)
  let := Representation.BinaryGroupAction.faithful ρ hρ
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let f : smallFittingFactors ρ → ChapterD.smallSupportFactors G (Multiplicative V) 1 :=
    fun X => ⟨X.val, (mem_smallFittingFactors_iff ρ X.val).mp X.property⟩
  have hf : Function.Injective f := by
    intro X Y h
    apply Subtype.ext
    exact congrArg (fun Z : ChapterD.smallSupportFactors G (Multiplicative V) 1 => Z.val) h
  have hd := ChapterD.smallSupport_decomposition (G := G) (V := Multiplicative V)
    (k := 1) (Or.inl rfl)
  refine ⟨hd.1.comp hf, ?_, ?_, ?_⟩
  · intro X hX Y hY
    exact ChapterD.smallSupportFactors_commutingFamily (k := 1) (Or.inl rfl) X
      ((mem_smallFittingFactors_iff ρ X).mp hX) Y
      ((mem_smallFittingFactors_iff ρ Y).mp hY)
  · have hi := hd.2.2.1.comp hf
    have hm := hi.map_orderIso
      (Representation.BinaryGroupAction.submoduleEquivSubgroup (V := V)).symm
    change iSupIndep (fun X : smallFittingFactors ρ =>
      (Representation.BinaryGroupAction.submoduleEquivSubgroup (V := V)).symm
        (commutatorAction X.val (Multiplicative V))) at hm
    simpa only [Representation.BinaryGroupAction.commutator_eq,
      OrderIso.symm_apply_apply] using hm
  · rw [sSup_eq_iSup', Representation.BinaryGroupAction.moved_iSup]

end CFSG.Quasithin.ChapterB.FittingStructure

namespace CFSG.Quasithin.ChapterB.FittingStructure
open Subgroup Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem minimalMovedFactors_subset_small (hlocal : LocalPlaneLaw ρ) :
    minimalMovedFactors ρ ⊆ smallFittingFactors ρ := by
  rintro X ⟨A, hA, hn, rfl⟩
  obtain ⟨d⟩ := hlocal A hA hn
  exact ⟨commutator_le_left _ _, d.odd_card, d.dimension⟩

variable [Finite G] [FiniteDimensional (ZMod 2) V]

theorem minimalMovedFactors_decomposition (hρ : Function.Injective ρ)
    (hlocal : LocalPlaneLaw ρ) :
    iSupIndep (fun X : minimalMovedFactors ρ => X.val) ∧
    (∀ X ∈ minimalMovedFactors ρ, ∀ Y ∈ minimalMovedFactors ρ,
      X ≤ centralizer (Y : Set G)) ∧
    iSupIndep (fun X : minimalMovedFactors ρ => subspaceCommutator ρ ⊤ X.val) ∧
    fittingMoved ρ = (⨆ X : minimalMovedFactors ρ, X.val) ∧
    subspaceCommutator ρ ⊤ (fittingMoved ρ) =
      ⨆ X : minimalMovedFactors ρ, subspaceCommutator ρ ⊤ X.val := by
  have hs := minimalMovedFactors_subset_small ρ hlocal
  let f : minimalMovedFactors ρ → smallFittingFactors ρ := fun X => ⟨X.val, hs X.property⟩
  have hf : Function.Injective f := by
    intro X Y h
    apply Subtype.ext
    exact congrArg (fun Z : smallFittingFactors ρ => Z.val) h
  obtain ⟨hi, hc, hv, _⟩ := smallFittingFactors_decomposition ρ hρ
  have hi' : iSupIndep (fun X : minimalMovedFactors ρ => X.val) :=
    hi.comp (f := f) hf
  have hv' : iSupIndep (fun X : minimalMovedFactors ρ => subspaceCommutator ρ ⊤ X.val) :=
    hv.comp (f := f) hf
  refine ⟨hi', fun X hX Y hY => hc X (hs hX) Y (hs hY), hv', ?_, ?_⟩
  · rw [fittingMoved_eq_sSup, sSup_eq_iSup']
  · rw [fittingMoved_eq_sSup, sSup_eq_iSup', Representation.BinaryGroupAction.moved_iSup]

end CFSG.Quasithin.ChapterB.FittingStructure

namespace CFSG.Quasithin.ChapterB.FittingStructure
open Subgroup Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [Finite G] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem smallFittingFactors_cross_fixed (hρ : Function.Injective ρ)
    {X Y : Subgroup G} (hX : X ∈ smallFittingFactors ρ) (hY : Y ∈ smallFittingFactors ρ)
    (hne : X ≠ Y) : subspaceCommutator ρ ⊤ Y ≤ fixedSpace ρ X := by
  let := Representation.BinaryGroupAction.action ρ
  let := Representation.BinaryGroupAction.elementary (V := V)
  let := Representation.BinaryGroupAction.faithful ρ hρ
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have h := ChapterD.smallSupportFactors_cross_fixed (k := 1) (Or.inl rfl)
    ((mem_smallFittingFactors_iff ρ X).mp hX)
    ((mem_smallFittingFactors_iff ρ Y).mp hY) hne
  rw [Representation.BinaryGroupAction.commutator_eq,
    Representation.BinaryGroupAction.fixedPoints_eq] at h
  exact (Representation.BinaryGroupAction.submoduleEquivSubgroup (V := V)).le_iff_le.mp h

theorem minimalMovedFactors_cross_fixed (hρ : Function.Injective ρ)
    (hlocal : LocalPlaneLaw ρ) {X Y : Subgroup G}
    (hX : X ∈ minimalMovedFactors ρ) (hY : Y ∈ minimalMovedFactors ρ) (hne : X ≠ Y) :
    subspaceCommutator ρ ⊤ Y ≤ fixedSpace ρ X :=
  smallFittingFactors_cross_fixed ρ hρ
    (minimalMovedFactors_subset_small ρ hlocal hX)
    (minimalMovedFactors_subset_small ρ hlocal hY) hne

end CFSG.Quasithin.ChapterB.FittingStructure
