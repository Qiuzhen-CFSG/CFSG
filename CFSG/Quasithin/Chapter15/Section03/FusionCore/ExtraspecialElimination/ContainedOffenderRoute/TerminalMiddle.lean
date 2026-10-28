module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointTransport
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.PGroup
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.PointCore
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration.StarSetup
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalPoint
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection.Reduction
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection.PointGeometry.InverseSimilarity
public import Theory.Representation.BinaryOffender.InvariantAction

/-!
# Excluding the middle node using the late offender-generated actor

Apply the full corrected B.5.1 classification to the actual late actor P on
U_H/Z. Its component and generalized Fitting subgroup are supplied by the
proved reduction, and the later strong best offender supplies strict offending.
The four B.5.1 alternatives reduce to natural plus dual, with P = L*, or a
six-dimensional symmetric central quotient. The other natural branches are
excluded by inverse similarity in the given S₈ extension.

For the remaining symmetric branch, the literal component point stabilizer
has index 105. Passing through a fixed binary subspace preserves every odd
point orbit: the stabilizer's action on the fiber is a binary translation
homomorphism, whose image must have odd order and hence be trivial. The
six-dimensional quotient would therefore contain 105 distinct vectors, an
impossibility. This argument retains the possibly nonzero central subspace.

Natural-plus-dual coordinates are then constructed on `TerminalPoint.space`
itself. B.5.1 gives component membership for the actual later best offender;
its placement in O₂(Y₀*T*) transports to the intrinsic component point core.
The universal B.4.9(2iii) rank-four assertion contradicts the proved rank-at-most-
three bound for that same concrete core.

`exclude` is the conditional terminal helper. The component-section and orbit
implications, corrected universal B.5.1, and universal B.4.9 rank assertion remain
explicit source parameters. The parent retains construction of `TerminalPoint`
and its literal seed, fixed supplement and stabilizer marking, and final source
assembly. The older first-span interfaces are preserved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of 15.3.49,
printed p.1145; B.5.1, pp.99–103; and B.4.9(2iii), p.92. The cardinal comparisons
adapt `ModelExclusions.MiddleEight.Selection.Reduction` to the relative component
of the late actor; the coordinate and point-core calculations reuse that development.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalMiddle
open ModelExclusions ModelExclusions.MiddleEight ModelExclusions.MiddleEight.Selection
open ModelExclusions.MiddleEight.Selection.PointGeometry
open Chapter2.ComponentRefinement.LieType.Binary
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve (psl_five_card_ne)

private theorem sl_three_card_ne (F : BinaryField) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) ≠ 20160 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (Matrix.SpecialLinearGroup (Fin 3) F.Carrier))
  rw [Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin] at h
  have hc := h.trans (Matrix.PSL3.LinearThree.card_projective_mul_scalar F.Carrier)
  rw [hc, F.card_eq]
  intro he
  have hb : F.degree < 2 := by
    by_contra hn
    have hq : 4 ≤ 2 ^ F.degree := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ F.degree)
    have hh := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    omega
  have hd : F.degree = 1 := by have := F.degree_pos; omega
  norm_num [hd] at he

private theorem symplectic_card_ne (F : BinaryField) (hf : 1 < F.degree) :
    Nat.card (Matrix.symplecticGroup (Fin 2) F.Carrier) ≠ 20160 := by
  rw [Theory.SpecificGroups.SymplecticFour.card_sp, F.card_eq]
  have hq : 4 ≤ 2 ^ F.degree := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ F.degree)
  have hh := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.pow_le_pow_left hq 4)
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 4) 1)
  omega


variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) K V) (J P : Subgroup K) (hJP : J ≤ P)
    (U : Subrepresentation ρ)
    (hU : U.toSubmodule = Coinvariants.ker (ρ.comp J.subtype))
    (s : MovedSection (ρ.comp P.subtype) (J.subgroupOf P))

private theorem moved_eq_coinvariants :
    moved ρ J = Coinvariants.ker (ρ.comp J.subtype) := by
  unfold moved subspaceCommutator Coinvariants.ker
  congr 1
  ext v
  constructor
  · rintro ⟨g, hg, w, _, rfl⟩
    exact ⟨(⟨g, hg⟩, w), rfl⟩
  · rintro ⟨⟨g, w⟩, rfl⟩
    exact ⟨g, g.property, w, Submodule.mem_top, rfl⟩

include hJP hU in
private theorem space_eq : s.space.toSubmodule = U.toSubmodule :=
  s.space_eq.trans ((ReducedModels.NaturalSelection.moved_subgroupOf hJP).trans
    ((moved_eq_coinvariants ρ J).trans hU.symm))

private noncomputable def extendedSpace : Subrepresentation ρ where
  toSubmodule := s.space.toSubmodule
  apply_mem_toSubmodule g v hv := by
    rw [space_eq ρ J P hJP U hU s] at hv ⊢
    exact U.apply_mem_toSubmodule g hv

private noncomputable def extendedCentral [J.Normal] :
    Subrepresentation (extendedSpace ρ J P hJP U hU s).toRepresentation where
  toSubmodule := s.central.toSubmodule
  apply_mem_toSubmodule g v hv := by
    have heq : s.central.toSubmodule =
        fixedSpace (extendedSpace ρ J P hJP U hU s).toRepresentation J := by
      rw [s.central_eq]
      ext v
      constructor
      · intro h j
        exact h ((subgroupOfEquivOfLe hJP).symm j)
      · intro h j
        exact h ⟨j.val.val, j.property⟩
    rw [heq] at hv ⊢
    exact (fixedSpace_stable_of_normal _ J (mem_top g) v).2 hv

include hJP hU in
private theorem not_natural_quotient [J.Normal]
    (extension : K ≃* Equiv.Perm (Fin 8)) :
    ¬ Nonempty (ActionEquiv (s.action.comp (J.subgroupOf P).subtype)
      (linearNatural BinaryField.two 4)) := by
  rintro ⟨f⟩
  let τ := (extendedCentral ρ J P hJP U hU s).quotientRepresentation
  have hs := inverseSimilar_of_symmetric_extension τ
    (P.subtype.comp (J.subgroupOf P).subtype) extension
  exact natural_not_inverseSimilar (inverseSimilar_transport f hs)

include hJP hU in
private theorem not_repeated_natural (extension : K ≃* Equiv.Perm (Fin 8))
    (k : ℕ) (hk : 0 < k) :
    ¬ IsRepeatedLinearNatural
      (s.space.toRepresentation.comp (J.subgroupOf P).subtype) BinaryField.two 4 k := by
  rintro ⟨f⟩
  let τ := (extendedSpace ρ J P hJP U hU s).toRepresentation
  have hs := inverseSimilar_of_symmetric_extension τ
    (P.subtype.comp (J.subgroupOf P).subtype) extension
  exact repeated_not_inverseSimilar k hk (inverseSimilar_transport f hs)

include hJP hU in
private theorem coordinates_of_dual
    (hd : IsNaturalPlusDual (s.space.toRepresentation.comp (J.subgroupOf P).subtype) 4) :
    ∃ e : J ≃* PSL 4, Nonempty (NaturalDualCoordinates ρ J e U) := by
  obtain ⟨f⟩ := hd
  let j := (subgroupOfEquivOfLe hJP).symm
  let e : J ≃* PSL 4 := (j.trans f.groupEquiv).trans (slEquivPSL 4)
  let E : U.toSubmodule ≃ₗ[ZMod 2] s.space.toSubmodule :=
    LinearEquiv.ofEq _ _ (space_eq ρ J P hJP U hU s).symm
  refine ⟨e, ⟨{ component_space := hU
                coordinates := E.trans f.linearEquiv
                equivariant := ?_ }⟩⟩
  intro g v
  change f.linearEquiv (E (U.toRepresentation g v)) =
    BinaryGeometry.naturalDual 4 (e g) (f.linearEquiv (E v))
  have hE : E (U.toRepresentation g v) = s.space.toRepresentation (j g) (E v) :=
    Subtype.ext rfl
  rw [hE]
  exact (f.intertwines (j g) (E v)).trans (naturalDual_project 4 _ _)

private theorem strong_quotient [FiniteDimensional (ZMod 2) V]
    {A : Subgroup P} (hA : IsStrongOffender (ρ.comp P.subtype) A) :
    IsStrongOffender s.action A :=
  ⟨hA.1, (ReducedModels.NaturalSelection.movedSection_codim_le s A).trans_lt hA.2⟩

include hJP in
private theorem irreducible_natural_or_six [Finite K] [FiniteDimensional (ZMod 2) V]
    (hcard : Nat.card J = 20160) (hstrong : IsStrongFFModule (ρ.comp P.subtype))
    (h : ProjectiveLine.IrreducibleActionCase s.action (J.subgroupOf P)
      (offenderSubgroup s.action)) :
    Nonempty (ActionEquiv (s.action.comp (J.subgroupOf P).subtype)
      (linearNatural BinaryField.two 4)) ∨
      Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 6 := by
  obtain ⟨A, hA⟩ := hstrong
  have hratio := (isStrongFFModule_iff_quadraticRatio_lt_one s.action).mp
    ⟨A, strong_quotient ρ J P s hA⟩
  have hj : Nat.card (J.subgroupOf P) = 20160 :=
    (Nat.card_congr (subgroupOfEquivOfLe hJP).toEquiv).trans hcard
  cases h with
  | linearTwo _ _ _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim
  | linearThree F _ e _ =>
    exact (sl_three_card_ne F ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hj)).elim
  | symplectic F hf _ e _ =>
    exact (symplectic_card_ne F hf ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hj)).elim
  | symplecticTwo e _ =>
    have hc := Nat.card_congr (e.subgroupEquiv.trans binarySymplecticDerivedEquiv).toEquiv
    rw [hj, nat_card_alternatingGroup, Nat.card_fin] at hc
    norm_num at hc
  | g2 _ _ _ _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim
  | g2Two _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim
  | symmetric _ _ _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim
  | alternatingSix _ _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim
  | alternatingSeven _ _ _ _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim
  | tripleSix _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim
  | binaryLinear n hn _ e _ =>
    rcases hn with rfl | rfl
    · exact Or.inl ⟨e⟩
    · exact (sl_five_card_ne ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hj)).elim
  | orthogonalSix _ _ _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim
  | symmetricEight _ e _ =>
    right
    rw [e.action.linearEquiv.finrank_eq]
    exact BinaryPermutation.finrank_natural_even (Fin 8) (by decide)
  | exteriorFive _ _ _ _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim

include hJP hU in
/-- Strict offending removes the ratio-one rows. The symmetric extension
excludes natural and repeated-natural actions by inverse similarity; the
six-dimensional symmetric quotient remains as a separate source branch. -/
private theorem dual_or_six [Finite K] [FiniteDimensional (ZMod 2) V] [J.Normal]
    (extension : K ≃* Equiv.Perm (Fin 8))
    (hcard : Nat.card J = 20160) (hstrong : IsStrongFFModule (ρ.comp P.subtype))
    (h : ProjectiveLine.QuasisimpleActionCase (ρ.comp P.subtype) (J.subgroupOf P) s) :
    ((J.subgroupOf P) = ⊤ ∧
      IsNaturalPlusDual (s.space.toRepresentation.comp (J.subgroupOf P).subtype) 4) ∨
      Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 6 := by
  have hratio := (isStrongFFModule_iff_quadraticRatio_lt_one (ρ.comp P.subtype)).mp hstrong
  have hj : Nat.card (J.subgroupOf P) = 20160 :=
    (Nat.card_congr (subgroupOfEquivOfLe hJP).toEquiv).trans hcard
  cases h with
  | irreducible _ _ _ hs _ =>
    exact (irreducible_natural_or_six ρ J P hJP s hcard hstrong hs).resolve_left
      (not_natural_quotient ρ J P hJP U hU s extension) |> Or.inr
  | doubleThree _ _ _ _ hq => exact (not_lt_of_ge hq.ge hratio).elim
  | naturalDual n hn hw hd =>
    rcases hn with rfl | rfl
    · exact Or.inl ⟨hw, hd⟩
    · obtain ⟨f⟩ := hd
      exact (sl_five_card_ne ((Nat.card_congr f.groupEquiv.toEquiv).symm.trans hj)).elim
  | repeatedNatural n k hn hk hb hw hr =>
    rcases hn with rfl | rfl
    · exact (not_repeated_natural ρ J P hJP U hU s extension k hk hr).elim
    · obtain ⟨f⟩ := hr
      exact (sl_five_card_ne ((Nat.card_congr f.groupEquiv.toEquiv).symm.trans hj)).elim

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalMiddle


open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalMiddle.OddOrbit

variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)

omit [Finite D] in
private theorem point_index_le_card [Finite W] (w : W) :
    (pointStabilizer ρ w).index ≤ Nat.card W := by
  let : MulAction D W :=
    { smul g v := ρ g v
      one_smul v := by change ρ 1 v = v; rw [map_one]; rfl
      mul_smul g h v := by change ρ (g*h) v = ρ g (ρ h v); rw [map_mul]; rfl }
  change (MulAction.stabilizer D w).index ≤ Nat.card W
  exact Nat.card_le_card_of_injective _ (MulAction.injective_ofQuotientStabilizer D w)

/-- The stabilizer of the quotient point acts on its fiber by binary
translations. Its translation image has order dividing the odd point index,
so it is trivial and the two stabilizers coincide. -/
private theorem point_index_le_central_quotient
    (C : Subrepresentation ρ) (hC : C.toSubmodule ≤ ρ.invariants)
    [Finite (W ⧸ C.toSubmodule)] (w : W)
    (hodd : Odd (pointStabilizer ρ w).index) :
    (pointStabilizer ρ w).index ≤ Nat.card (W ⧸ C.toSubmodule) := by
  let A := pointStabilizer ρ w
  let B := pointStabilizer C.quotientRepresentation (C.toSubmodule.mkQ w)
  have hAB : A ≤ B := by
    intro g hg
    change C.toSubmodule.mkQ (ρ g w) = C.toSubmodule.mkQ w
    rw [show ρ g w = w from hg]
  have hcentral (g : B) : ρ g w - w ∈ C.toSubmodule := by
    apply (Submodule.Quotient.mk_eq_zero C.toSubmodule).mp
    change C.toSubmodule.mkQ (ρ g w - w) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr g.property
  let f : B →* Multiplicative W :=
    { toFun g := Multiplicative.ofAdd (ρ g w - w)
      map_one' := by change ρ 1 w - w = 0; simp
      map_mul' g h := by
        change ρ (g.val * h.val) w - w = (ρ g w - w) + (ρ h w - w)
        have hf := hC (hcentral h) g.val
        change ρ g (ρ h w - w) = ρ h w - w at hf
        rw [map_sub] at hf
        rw [map_mul, Module.End.mul_apply]
        have he : ρ g (ρ h w) = (ρ h w - w) + ρ g w := (sub_eq_iff_eq_add).mp hf
        rw [he]
        abel }
  have hk : f.ker = A.subgroupOf B := by
    ext g
    change (ρ g w - w = 0) ↔ ρ g w = w
    exact sub_eq_zero
  have hp : IsPGroup 2 f.range := by
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    change (2 : ℕ) • g.val.toAdd = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
    exact zero_smul _ _
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hd : Nat.card f.range ∣ A.index := by
    rw [← index_ker, hk]
    exact relIndex_dvd_index_of_le hAB
  have hn0 : n = 0 := by
    by_contra hn0
    have htwo : 2 ∣ 2^n := dvd_pow_self 2 hn0
    rw [← hn] at htwo
    exact hodd.not_two_dvd_nat (htwo.trans hd)
  have hker : f.ker = ⊤ := by
    apply index_eq_one.mp
    rw [index_ker, hn, hn0, pow_zero]
  have he : A = B := by
    apply le_antisymm hAB
    intro g hg
    have hh : (⟨g, hg⟩ : B) ∈ f.ker := hker ▸ mem_top _
    rw [hk] at hh
    exact hh
  change A.index ≤ _
  rw [he]
  exact point_index_le_card C.quotientRepresentation _

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalMiddle.OddOrbit
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalMiddle
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open ModelExclusions ModelExclusions.MiddleEight ModelExclusions.MiddleEight.Selection
open Chapter2.ComponentRefinement.LieType.Binary
open ComponentReduction.ModelReduction.BinaryModels
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve (card_of_alternating)
open scoped IsMulCommutative
universe u

/-- The component orbit has 105 points, whereas a six-dimensional central
quotient has only 64 vectors. Central fixed vectors do not shrink an odd orbit. -/
private theorem not_six_of_point_index
    {K W : Type*} [Group K] [Finite K] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) K W) (J P : Subgroup K) (hJP : J ≤ P)
    (U : Subrepresentation ρ)
    (hU : U.toSubmodule = Coinvariants.ker (ρ.comp J.subtype))
    (s : MovedSection (ρ.comp P.subtype) (J.subgroupOf P))
    (z : U.toSubmodule)
    (hi : (pointStabilizer (U.toRepresentation.comp J.subtype) z).index = 105) :
    Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) ≠ 6 := by
  intro hd
  let E : U.toSubmodule ≃ₗ[ZMod 2] s.space.toSubmodule :=
    LinearEquiv.ofEq _ _ (space_eq ρ J P hJP U hU s).symm
  let τ : Representation (ZMod 2) J s.space.toSubmodule := (extendedSpace ρ J P hJP U hU s).toRepresentation.comp J.subtype
  let j := (subgroupOfEquivOfLe hJP).symm
  let C : Subrepresentation τ :=
    { toSubmodule := s.central.toSubmodule
      apply_mem_toSubmodule g v hv := s.central.apply_mem_toSubmodule (j g).val hv }
  have hC : C.toSubmodule ≤ τ.invariants := by
    intro v hv g
    exact (s.central_eq ▸ hv) (j g)
  have he : pointStabilizer τ (E z) =
      pointStabilizer (U.toRepresentation.comp J.subtype) z := by
    ext g
    constructor
    · intro h
      apply Subtype.ext
      exact congrArg (fun v : s.space.toSubmodule => (v : W)) h
    · intro h
      apply Subtype.ext
      exact congrArg (fun v : U.toSubmodule => (v : W)) h
  have hi' : (pointStabilizer τ (E z)).index = 105 := he ▸ hi
  let : Finite (s.space.toSubmodule ⧸ C.toSubmodule) :=
    Module.finite_of_finite (ZMod 2)
  have h := OddOrbit.point_index_le_central_quotient τ C hC (E z)
    (hi' ▸ (by decide : Odd 105))
  rw [hi', Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h
  change 105 ≤ 2 ^ Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) at h
  rw [hd] at h
  norm_num at h

variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (r : ReducedModels.Input κ H M Y V Y0 T ZS Z E L upper)
    (p : TerminalPoint r)
    (m : BinaryGeometry.MiddleNodeEight (starImage H L) (componentParabolic H L Y0 T))
    (sections : ReducedModels.EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)

include p m sections orbits in
/-- The literal component point stabilizer has index 105: its Sylow subgroup
has order 64 and index three in the parabolic. The quotient intersection is
justified by the original Sylow witness. -/
theorem component_point_index :
    (pointStabilizer (p.space.toRepresentation.comp (starImage H L).subtype) p.point).index = 105 := by
  let d := r.reduced_data orbits (r.y_le_closure sections)
  obtain ⟨hc, hy, _, _, _, _, _⟩ := r.structure_of_earlier sections orbits
  obtain ⟨_, hPL, hi, _, _⟩ := r.parabolic_local hc hy
  obtain ⟨S, hS⟩ := BinaryGeneration.component_sylow d
  have hcard : Nat.card (starImage H L) = 20160 :=
    card_of_alternating ((m.extension.subgroupMap (starImage H L)).trans
      (MulEquiv.subgroupCongr m.component_image))
  have h64 : Nat.card S = 64 := by
    rw [S.card_eq_multiplicity, hcard]
    decide +kernel
  have h315 : (S : Subgroup (starImage H L)).index = 315 := by
    have hh := (S : Subgroup (starImage H L)).card_mul_index
    rw [h64, hcard] at hh
    omega
  have hle : (S : Subgroup (starImage H L)) ≤
      (componentParabolic H L Y0 T).subgroupOf (starImage H L) := by
    rw [hS]
    exact subgroupOf_mono _ le_sup_right
  have h3 : (S : Subgroup (starImage H L)).relIndex
      ((componentParabolic H L Y0 T).subgroupOf (starImage H L)) = 3 := by
    rw [hS, relIndex_subgroupOf hPL]
    exact hi
  have h105 : ((componentParabolic H L Y0 T).subgroupOf (starImage H L)).index = 105 := by
    have hh := relIndex_mul_index hle
    rw [h3, h315] at hh
    omega
  have he : (componentParabolic H L Y0 T).subgroupOf (starImage H L) =
      pointStabilizer (p.space.toRepresentation.comp (starImage H L).subtype) p.point := by
    rw [r.parabolic_intersection hy, p.stabilizer]
    ext g
    exact ⟨fun h => h.1, fun h => ⟨h, g.property⟩⟩
  rwa [he] at h105

include p m sections orbits in
/-- Exhaust the corrected B.5.1 alternatives on the late actor. The surviving
row makes that actor equal to the component, so the later best offender lies
in the component and the marked commutator has natural-plus-dual coordinates. -/
theorem coordinates_and_membership (s : StrongPlacement r)
    (source : ProjectiveLine.QuasisimpleClassificationInput.{u,u} κ) :
    starImage H s.selected.carrier ≤ starImage H L ∧
      ∃ e : starImage H L ≃* PSL 4,
        Nonempty (NaturalDualCoordinates r.placed.action.representation (starImage H L) e p.space) := by
  let d := r.reduced_data orbits (r.y_le_closure sections)
  let := BinaryGeneration.star_component_normal d
  obtain ⟨c⟩ := r.late_source_conclusion sections orbits source
  have hJP := r.component_le_late_actor sections orbits
  have hstrong : IsStrongFFModule
      (r.placed.action.representation.comp (lateActor r.placed.action).subtype) :=
    ⟨_, s.late_offender.2.2⟩
  have hcard := card_of_alternating ((m.extension.subgroupMap (starImage H L)).trans
      (MulEquiv.subgroupCongr m.component_image))
  have hdual := (dual_or_six r.placed.action.representation (starImage H L)
    (lateActor r.placed.action) hJP p.space p.component_space c.sectionData
    m.extension hcard hstrong c.clause_one).resolve_right
      (not_six_of_point_index r.placed.action.representation (starImage H L)
        (lateActor r.placed.action) hJP p.space p.component_space c.sectionData p.point
        (component_point_index r p m sections orbits))
  exact ⟨s.in_late_actor.trans (subgroupOf_eq_top.mp hdual.1),
    coordinates_of_dual r.placed.action.representation (starImage H L)
      (lateActor r.placed.action) hJP p.space p.component_space c.sectionData hdual.2⟩

include p m sections orbits in
/-- The conditional middle-node contradiction on the actual later offender.
The remaining source parameters are precisely the component sections, orbit
implication, corrected universal B.5.1 and universal B.4.9(2iii) rank assertion.
Coordinates, component membership and the concrete point-core bound are proved. -/
theorem exclude (s : StrongPlacement r)
    (source : ProjectiveLine.QuasisimpleClassificationInput.{u,u} κ)
    (rank_source : NaturalDualBestRank) : False := by
  obtain ⟨hAL, e, ⟨c⟩⟩ := coordinates_and_membership r p m sections orbits s source
  exact exclude_of_coordinates r.placed.action.representation (starImage H L)
    (starImage H Y0 ⊔ starImage H T) (starImage H s.selected.carrier) e p.space
    c p.point p.stabilizer hAL s.core s.selected.best rank_source naturalDualPointCoreBound

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalMiddle
