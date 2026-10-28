module
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.Triality
public import Theory.GroupTheory.Amalgam.RankTwoTransport
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Basic

/-!
# Triality normalizers in original automorphism extensions

Each endpoint normalizes the embedded native local factor and contains
its base parabolic. The arms endpoint is nonsolvable at every positive
field degree; the central endpoint is nonsolvable above degree one.
Thus a mixed-solvability source pair fixes the orientation and degree.

At degree one an outer two-group has trivial image in the actual outer
quotient. The two normalizers and their entire intersection are then the
images of the native parabolics and Borel through the same faithful inner
embedding. Restriction gives all three maps and both commuting squares.
The construction does not equate an original Sylow with a minimal one.

The general subgroup transport keeps conversion independent of the concrete
triality carrier. Source: Aschbacher–Smith F.1.12, pp.263–264, used in 5.2.2,
p.647; the native outer calculation retains the cubic coefficient field.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.Triality.ExtensionAmalgam
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.ParabolicOuterTwo
open Theory.GroupTheory.AutomorphismExtensionBorel

variable (m : ℕ) (hm : 0 < m)
  (E : Subgroup (MulAut (BinaryCarrier m hm)))
  (hE : MulAut.innerSubgroup (BinaryCarrier m hm) ≤ E)

@[expose] def endpoint (a : Node) : Subgroup E :=
  normalizer (((localFactor (binaryParameters m hm) a).map (innerEmbedding E hE)) : Set E)

@[expose] def overlap : Subgroup E := endpoint m hm E hE .arms ⊓ endpoint m hm E hE .central

@[expose] def amalgam : RankTwoAmalgam (endpoint m hm E hE .arms) (overlap m hm E hE)
    (endpoint m hm E hE .central) :=
  RankTwoAmalgam.ofSubgroups _ _ _ inf_le_left inf_le_right

theorem base_parabolic_le_endpoint (a : Node) :
    (parabolic (binaryParameters m hm) a).map (innerEmbedding E hE) ≤ endpoint m hm E hE a := by
  rw [← normalizer_localFactor _ rfl a]
  exact (localFactor (binaryParameters m hm) a).le_normalizer_map (innerEmbedding E hE)

theorem local_le_endpoint (a : Node) :
    (localFactor (binaryParameters m hm) a).map (innerEmbedding E hE) ≤ endpoint m hm E hE a :=
  (map_mono (localFactor_le_parabolic _ a)).trans (base_parabolic_le_endpoint m hm E hE a)

private theorem endpoint_eq_of_inner
    (hinner : E ≤ MulAut.innerSubgroup (BinaryCarrier m hm)) (a : Node) :
    endpoint m hm E hE a = (parabolic (binaryParameters m hm) a).map (innerEmbedding E hE) := by
  apply le_antisymm _ (base_parabolic_le_endpoint m hm E hE a)
  intro x hx
  obtain ⟨g,hg⟩ := hinner x.property
  have he : innerEmbedding E hE g = x := Subtype.ext hg
  refine ⟨g, ?_, he⟩
  have hn : g ∈ (normalizer (((localFactor (binaryParameters m hm) a).map
      (innerEmbedding E hE)) : Set E)).comap (innerEmbedding E hE) := by
    change innerEmbedding E hE g ∈ endpoint m hm E hE a
    rwa [he]
  rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
    comap_map_eq_self (by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr (carrierEmbedding_injective m hm E hE)]
      exact bot_le), normalizer_localFactor _ rfl a] at hn
  exact hn

variable (E₁ : Subgroup (MulAut (BinaryCarrier 1 Nat.zero_lt_one)))
  (hE₁ : MulAut.innerSubgroup (BinaryCarrier 1 Nat.zero_lt_one) ≤ E₁)
  (h2 : IsPGroup 2 (E₁.map (QuotientGroup.mk'
    (MulAut.innerSubgroup (BinaryCarrier 1 Nat.zero_lt_one)))))

include h2

theorem binary_endpoint_eq (a : Node) :
    endpoint 1 Nat.zero_lt_one E₁ hE₁ a =
      (parabolic (binaryParameters 1 Nat.zero_lt_one) a).map (innerEmbedding E₁ hE₁) :=
  endpoint_eq_of_inner 1 Nat.zero_lt_one E₁ hE₁
    (automorphismOvergroup_eq_inner_at_two E₁ hE₁ h2).le a

theorem binary_overlap_eq :
    overlap 1 Nat.zero_lt_one E₁ hE₁ =
      (borel (binaryParameters 1 Nat.zero_lt_one)).map (innerEmbedding E₁ hE₁) := by
  rw [overlap, binary_endpoint_eq E₁ hE₁ h2 .arms, binary_endpoint_eq E₁ hE₁ h2 .central,
    ← Subgroup.map_inf _ _ _ (carrierEmbedding_injective 1 Nat.zero_lt_one E₁ hE₁)]
  exact congrArg (Subgroup.map (innerEmbedding E₁ hE₁)) (Triality.overlap _ rfl)

omit h2

private theorem overlap_eq_of_inner (hinner : E ≤ MulAut.innerSubgroup (BinaryCarrier m hm)) :
    overlap m hm E hE = (borel (binaryParameters m hm)).map (innerEmbedding E hE) := by
  rw [overlap, endpoint_eq_of_inner m hm E hE hinner .arms,
    endpoint_eq_of_inner m hm E hE hinner .central,
    ← Subgroup.map_inf _ _ _ (carrierEmbedding_injective m hm E hE)]
  exact congrArg (Subgroup.map (innerEmbedding E hE)) (Triality.overlap _ rfl)

private def subgroupCongrIso {X : Type*} [Group X]
    (P B Q P' B' Q' : Subgroup X) (hP : B ≤ P) (hQ : B ≤ Q)
    (hP' : B' ≤ P') (hQ' : B' ≤ Q')
    (eP : P = P') (eB : B = B') (eQ : Q = Q') :
    RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P B Q hP hQ)
      (RankTwoAmalgam.ofSubgroups P' B' Q' hP' hQ') where
  left := MulEquiv.subgroupCongr eP
  middle := MulEquiv.subgroupCongr eB
  right := MulEquiv.subgroupCongr eQ
  left_commutes _ := Subtype.ext rfl
  right_commutes _ := Subtype.ext rfl

private def innerIso (hinner : E ≤ MulAut.innerSubgroup (BinaryCarrier m hm)) :
    RankTwoAmalgam.Iso (Triality.amalgam (binaryParameters m hm)) (amalgam m hm E hE) :=
  (RankTwoAmalgam.ofSubgroupsMapIso (innerEmbedding E hE) (carrierEmbedding_injective m hm E hE)
    (parabolic (binaryParameters m hm) .arms) (borel (binaryParameters m hm))
    (parabolic (binaryParameters m hm) .central)
    (borel_le_parabolic _ .arms) (borel_le_parabolic _ .central)).trans
      (subgroupCongrIso _ _ _ _ _ _ _ _ inf_le_left inf_le_right
        (endpoint_eq_of_inner m hm E hE hinner .arms).symm
        (overlap_eq_of_inner m hm E hE hinner).symm
        (endpoint_eq_of_inner m hm E hE hinner .central).symm)

include h2

def binaryIso : RankTwoAmalgam.Iso (Triality.amalgam (binaryParameters 1 Nat.zero_lt_one))
    (amalgam 1 Nat.zero_lt_one E₁ hE₁) :=
  innerIso 1 Nat.zero_lt_one E₁ hE₁ (automorphismOvergroup_eq_inner_at_two E₁ hE₁ h2).le

theorem binaryIso_left_apply (x : parabolic (binaryParameters 1 Nat.zero_lt_one) .arms) :
    ((binaryIso E₁ hE₁ h2).left x).val = innerEmbedding E₁ hE₁ x.val := by rfl

theorem binaryIso_middle_apply (x : borel (binaryParameters 1 Nat.zero_lt_one)) :
    ((binaryIso E₁ hE₁ h2).middle x).val = innerEmbedding E₁ hE₁ x.val := by rfl

theorem binaryIso_right_apply (x : parabolic (binaryParameters 1 Nat.zero_lt_one) .central) :
    ((binaryIso E₁ hE₁ h2).right x).val = innerEmbedding E₁ hE₁ x.val := by rfl

omit h2

private theorem endpoint_not_solvable_of_quotient (a : Node)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : (localFactor (binaryParameters m hm) a ⧸
      pCore 2 (localFactor (binaryParameters m hm) a)) ≃* SL(2,F)) :
    ¬ Group.IsSolvable (endpoint m hm E hE a) := by
  intro hs
  let := hs
  let j := ((localFactor (binaryParameters m hm) a).equivMapOfInjective
    (innerEmbedding E hE) (carrierEmbedding_injective m hm E hE)).toMonoidHom
  let f := (inclusion (local_le_endpoint m hm E hE a)).comp j
  let : Group.IsSolvable (localFactor (binaryParameters m hm) a) :=
    Group.isSolvable_of_isSolvable_injective (f := f)
      ((inclusion_injective (local_le_endpoint m hm E hE a)).comp
        ((localFactor (binaryParameters m hm) a).equivMapOfInjective
          (innerEmbedding E hE) (carrierEmbedding_injective m hm E hE)).injective)
  let : Group.IsSolvable SL(2,F) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_perfect hF
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple hF
  exact Group.IsPerfect.not_isSolvable SL(2,F) inferInstance

theorem arms_endpoint_not_solvable : ¬ Group.IsSolvable (endpoint m hm E hE .arms) := by
  let P := binaryParameters m hm
  have hlarge : 2 < Nat.card (ExtensionField P) := by
    rw [card_extensionField]
    change 2 < (2^m)^3
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 1 < m*3)
  exact endpoint_not_solvable_of_quotient m hm E hE .arms hlarge
    ((localFactorArmsQuotientEquivPSL2 P rfl).trans (Theory.PSL2.sl2QuotientEquiv _).symm)

theorem central_endpoint_not_solvable (hm' : 1 < m) :
    ¬ Group.IsSolvable (endpoint m hm E hE .central) := by
  let P := binaryParameters m hm
  have hlarge : 2 < Nat.card (GaloisField P.prime P.exponent) := by
    rw [GaloisField.card P.prime P.exponent (by change m ≠ 0; omega)]
    change 2 < 2^m
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) hm'
  exact endpoint_not_solvable_of_quotient m hm E hE .central hlarge
    ((localFactorCentralQuotientEquivPSL2 P rfl).trans (Theory.PSL2.sl2QuotientEquiv _).symm)

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.Triality.ExtensionAmalgam
