module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.HallJanko.FirstParabolic
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.HallJanko.SecondParabolic
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.HallJanko.Transport
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Automorphisms.Full

/-!
# Concrete Hall--Janko exceptional amalgam models

The checked centralizer and relative normal-closure calculations construct
both marked models of F.1.12(I)(10)--(11), with no remaining local premises.
The whole Borels have orders 384 and 768, and the Sylow subgroups have orders
128 and 256. Each amalgam uses the inclusions of this whole Borel into LᵢB.

For the outer model, the generator-pair calculations identify the concrete
permutation extension with the actual full automorphism group. Transport by
that equivalence preserves the marked local factors, intrinsic two-cores,
quotients and overlap maps. Compatibility here concerns only this constructed
transport. The recognition predicates for arbitrary amalgams remain the
carrier-indexed `ParabolicEquiv` predicates; no uniqueness theorem is asserted.

Source: Aschbacher--Smith, F.1.1, F.1.3 and F.1.12(I)(10)--(11), printed
pp.259--263, especially p.263 (PDF p.274). The carrier is the original ATLAS
degree-100 permutation group, without a comparison to the icosian model.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.HallJanko
open Theory.GroupTheory
open Sporadic.LeechRelated.J2
open ExceptionalParabolics

/-- The concrete J₂ marking with all four source local calculations discharged. -/
noncomputable def j2Model : J2Model where
  toMarking := SecondParabolic.sourceMarking FirstParabolic.first_local_orders.1
  L₁_core := FirstParabolic.l₁_core_isQuaternionDihedralCore
  L₁_quotient := FirstParabolic.l₁_quotient_isPSL
  L₂_quotient := SecondParabolic.l₂_quotient_isPSL
  L₂_core_card := ExceptionalParabolics.SecondParabolic.l₂_core_card

/-- The same fixed local factors in the explicit permutation extension. -/
noncomputable def extensionModel : ExtensionModel where
  toMarking := SecondParabolic.outerSourceMarking FirstParabolic.first_local_orders.1
  L₁S_quotient := FirstParabolic.l₁s_quotient_equiv
  L₁_core := FirstParabolic.outerL₁_core_isQuaternionDihedralCore
  L₂_quotient := ExceptionalParabolics.SecondParabolic.outerL₂_quotient
  L₂_core_card := ExceptionalParabolics.SecondParabolic.outerL₂_core_card

/-- The source outer model lives in the full automorphism group of the actual carrier. -/
noncomputable def autJ2Model : AutJ2Model := extensionModel.map extensionEquivAut

@[simp] theorem j2Model_L : j2Model.L = Seed.L := rfl

@[simp] theorem j2Model_S : (j2Model.S : Subgroup Carrier) = Seed.s := rfl

@[simp] theorem j2Model_B :
    j2Model.toMarking.B = ExceptionalParabolics.SecondParabolic.Overlap.B :=
  SecondParabolic.marking_B FirstParabolic.first_local_orders.1
    PairNormalizer.p₂_quotient_equiv

@[simp] theorem j2Model_P_zero : j2Model.toMarking.P 0 = Seed.l₁ := by
  change Seed.l₁ ⊔ j2Model.toMarking.B = Seed.l₁
  rw [j2Model_B, sup_of_le_left ExceptionalParabolics.SecondParabolic.Overlap.B_le_l₁]

@[simp] theorem j2Model_P_one : j2Model.toMarking.P 1 = Seed.p₂ := by
  change Seed.l₂ ⊔ j2Model.toMarking.B = Seed.p₂
  rw [j2Model_B]
  exact ExceptionalParabolics.SecondParabolic.Overlap.l₂_sup_B
    FirstParabolic.first_local_orders.1 PairNormalizer.card_p₂

@[simp] theorem extensionModel_L : extensionModel.L = Seed.outerL := rfl

@[simp] theorem extensionModel_S :
    (extensionModel.S : Subgroup Extension) = Seed.outerS := rfl

@[simp] theorem extensionModel_B :
    extensionModel.toMarking.B = ExceptionalParabolics.SecondParabolic.Overlap.outerB :=
  SecondParabolic.outerMarking_B FirstParabolic.first_local_orders.1
    PairNormalizer.p₂_quotient_equiv

/-- The first outer quotient has the literal numerator L₁S. -/
@[simp] theorem extensionModel_LS_zero : extensionModel.toMarking.LS 0 = Seed.l₁s := rfl

/-- The whole first outer parabolic is the numerator used in the S₅ quotient. -/
@[simp] theorem extensionModel_P_zero : extensionModel.toMarking.P 0 = Seed.l₁s := by
  change Seed.outerL 0 ⊔ extensionModel.toMarking.B = Seed.l₁s
  rw [extensionModel_B, ExceptionalParabolics.FirstParabolic.l₁s_eq_sup_outerElement]
  change Seed.l₁.map intoExtension ⊔
    (ExceptionalParabolics.SecondParabolic.Overlap.B.map intoExtension ⊔ _) = _
  rw [← sup_assoc, sup_of_le_left
    (Subgroup.map_mono ExceptionalParabolics.SecondParabolic.Overlap.B_le_l₁)]
  rfl

/-- The second full outer parabolic adjoins the fixed outer word to the full normalizer. -/
@[simp] theorem extensionModel_P_one : extensionModel.toMarking.P 1 =
    Seed.p₂.map intoExtension ⊔ Subgroup.zpowers Seed.outerElement := by
  change Seed.outerL 1 ⊔ extensionModel.toMarking.B = _
  rw [extensionModel_B]
  change Seed.l₂.map intoExtension ⊔
    (ExceptionalParabolics.SecondParabolic.Overlap.B.map intoExtension ⊔ _) = _
  rw [← sup_assoc, ← Subgroup.map_sup,
    ExceptionalParabolics.SecondParabolic.Overlap.l₂_sup_B
      FirstParabolic.first_local_orders.1 PairNormalizer.card_p₂]

/-- The factors in the automorphism group are the inner images of the fixed factors. -/
@[simp] theorem autJ2Model_L (i : Fin 2) :
    autJ2Model.L i = (Seed.L i).map (MulAut.conj : Carrier →* MulAut Carrier) := by
  change ((Seed.L i).map intoExtension).map extensionEquivAut.toMonoidHom = _
  rw [Subgroup.map_map, extensionEquivAut_comp_intoExtension]

@[simp] theorem autJ2Model_S :
    (autJ2Model.S : Subgroup (MulAut Carrier)) =
      Seed.outerS.map extensionEquivAut.toMonoidHom := rfl

@[simp] theorem autJ2Model_B :
    autJ2Model.toMarking.B = extensionModel.toMarking.B.map extensionEquivAut.toMonoidHom :=
  Marking.map_B _ _

@[simp] theorem autJ2Model_P (i : Fin 2) :
    autJ2Model.toMarking.P i =
      (extensionModel.toMarking.P i).map extensionEquivAut.toMonoidHom :=
  Marking.map_P _ _ i

@[simp] theorem autJ2Model_LS_zero :
    autJ2Model.toMarking.LS 0 = Seed.l₁s.map extensionEquivAut.toMonoidHom :=
  Marking.map_LS _ _ 0

/-- Both inclusion maps commute for this particular ambient transport. -/
noncomputable def extensionAutAmalgamIso :
    RankTwoAmalgam.Iso extensionModel.toMarking.amalgam autJ2Model.toMarking.amalgam :=
  Marking.mapAmalgamIso _ extensionEquivAut

/-- The odd Borel factor is retained in the inner model. -/
theorem card_j2Model_B : Nat.card j2Model.toMarking.B = 384 :=
  SecondParabolic.card_sourceMarking_B _

theorem card_j2Model_S : Nat.card (j2Model.S : Subgroup Carrier) = 128 :=
  SecondParabolic.card_sourceMarking_S _

theorem card_extensionModel_B : Nat.card extensionModel.toMarking.B = 768 :=
  SecondParabolic.card_outerSourceMarking_B _

theorem card_extensionModel_S : Nat.card (extensionModel.S : Subgroup Extension) = 256 :=
  SecondParabolic.card_outerSourceMarking_S _

/-- Ambient transport preserves the full outer Borel, including its odd factor. -/
theorem card_autJ2Model_B : Nat.card autJ2Model.toMarking.B = 768 := by
  rw [autJ2Model_B, Subgroup.card_map_of_injective
    (f := extensionEquivAut.toMonoidHom) extensionEquivAut.injective]
  exact card_extensionModel_B

theorem card_autJ2Model_S : Nat.card (autJ2Model.S : Subgroup (MulAut Carrier)) = 256 := by
  rw [autJ2Model_S, Subgroup.card_map_of_injective
    (f := extensionEquivAut.toMonoidHom) extensionEquivAut.injective]
  exact card_extensionModel_S

theorem j2Model_B_ne_S : j2Model.toMarking.B ≠ (j2Model.S : Subgroup Carrier) := by
  intro h
  have hc := congrArg (fun K : Subgroup Carrier => Nat.card K) h
  rw [card_j2Model_B, card_j2Model_S] at hc
  contradiction

theorem autJ2Model_B_ne_S :
    autJ2Model.toMarking.B ≠ (autJ2Model.S : Subgroup (MulAut Carrier)) := by
  intro h
  have hc := congrArg (fun K : Subgroup (MulAut Carrier) => Nat.card K) h
  rw [card_autJ2Model_B, card_autJ2Model_S] at hc
  contradiction

/-- Both concrete source contracts are inhabited, with every premise discharged. -/
theorem models_exist : Nonempty J2Model ∧ Nonempty AutJ2Model :=
  ⟨⟨j2Model⟩, ⟨autJ2Model⟩⟩

end CFSG.Quasithin.ChapterF.GreenBook.HallJanko
