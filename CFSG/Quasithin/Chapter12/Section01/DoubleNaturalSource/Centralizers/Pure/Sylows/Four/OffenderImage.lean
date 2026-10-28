module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Thompson
public import Theory.Representation.BinaryOffender.DualDisplacement
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# The original Thompson image is the unique dimension-four offender

The natural and dual displacement bounds force every offender to have rank
at least four. The checked elementary catalogue in the given inner Sylow
then identifies it with the marked A0 of order sixteen. Its fixed codimension
is exactly four. Images of maximum elementary subgroups either vanish or
are this same A0, so the moving original Thompson subgroup has image A0.

The final application uses the original chosen module and the contrary
ambient Sylow branch. It discharges the unique-offender step of 12.1.4
without an MS-classification or a whole-module splitting premise. The
parabolic and whole-module arguments remain with this task; the parent
qt-d-double-natural-centralizers retains final source assembly.
Source: Aschbacher--Smith, 12.1.4, printed p.790, B.4.9(2iii), pp.92,94,
and H.9.3(3--4), pp.391--392.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
open SourceFourActors
variable {M E : Type*} [Group M] [AddCommGroup E] [Module (ZMod 2) E]
  (S : SourceSetup 4 M E)

theorem four_offender_rank_ge_four (A : Subgroup M) (hA : IsOffender S.representation A) :
    4 ≤ rank A := by
  let := S.finite_group
  let : FiniteDimensional (ZMod 2) E := S.model.coordinates.symm.finiteDimensional
  have hAL := S.four_offender_le_layer A hA
  let f : A →* BinaryLinear.OuterCyclic.LinearGroup 4 :=
    S.layer.toMonoidHom.comp (inclusion hAL)
  let ρ : Representation (ZMod 2) A (BinaryLinear.OuterCyclic.Space 4) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f
  have hf : Function.Injective ρ := by
    intro a b hab
    apply Subtype.ext
    have hh : f a = f b := LinearEquiv.toLinearMap_injective hab
    exact congrArg (fun z : componentLayer M => (z : M)) (S.layer.injective hh)
  have he (a : A) (v : E) :
      S.model.coordinates ((S.representation.comp A.subtype) a v) =
        (ρ.prod ρ.dual) a (S.model.coordinates v) := by
    rw [MonoidHom.comp_apply, S.model.equivariant]
    have hmark : S.model.group a = MulAut.conj (f a) := S.model.on_layer (inclusion hAL a)
    change (BinaryNaturalDual.ModelOrbits.AutomorphismModel.coordinateAction S.degree).representation
      (S.model.group (a : M)) (S.model.coordinates v) = _
    rw [hmark, BinaryNaturalDual.CoordinateAction.on_inner,
      BinaryNaturalDual.naturalDualRepresentation_apply]
    apply Prod.ext
    · rfl
    · apply LinearMap.ext
      intro x
      change (S.model.coordinates v).2 ((f a).symm x) =
        (S.model.coordinates v).2 (f a⁻¹ x)
      rw [map_inv]
      rfl
  have hc : fixedCodim (ρ.prod ρ.dual) ⊤ = fixedCodim S.representation A := by
    have hh := fixedCodim_map_equivariant (S.representation.comp A.subtype)
      (ρ.prod ρ.dual) (MonoidHom.id A) S.model.coordinates he (⊤ : Subgroup A)
    simp only [Subgroup.map_id] at hh
    rw [←hh]
    unfold fixedCodim
    rw [fixedSpace_comp_map, ← MonoidHom.range_eq_map, range_subtype]
  have hn : (⊤ : Subgroup A) ≠ ⊥ := by
    intro hn
    have hh := congrArg (Subgroup.map A.subtype) hn
    exact hA.1.1 (by simpa only [←MonoidHom.range_eq_map, range_subtype, Subgroup.map_bot] using hh)
  let := hA.1.2
  have h1 := fixedCodim_pos_of_faithful ρ hf hn
  have h2 := fixedCodim_pos_of_faithful ρ.dual (faithful_dual ρ hf) hn
  have hm := rank_le_fixedCodim_mul_dual ρ hf (⊤ : Subgroup A)
  have hr : rank (⊤ : Subgroup A) = rank A := by
    unfold rank
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv]
  rw [hr] at hm
  have hs := hA.2
  rw [←hc, fixedCodim_prod] at hs
  have hp : 2 ≤ fixedCodim ρ ⊤ := by
    by_contra! hh
    have hq : fixedCodim ρ ⊤ = 1 := by omega
    rw [hq, one_mul] at hm
    omega
  have hq : 2 ≤ fixedCodim ρ.dual ⊤ := by
    by_contra! hh
    have hq : fixedCodim ρ.dual ⊤ = 1 := by omega
    rw [hq, mul_one] at hm
    omega
  omega
end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup

namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
open SourceFourActors
variable {M E : Type*} [Group M] [AddCommGroup E] [Module (ZMod 2) E]
  (S : SourceSetup 4 M E)

/-- Every offender in the given Sylow is its marked inner elementary sixteen. -/
theorem four_offender_eq_A0 (P : Sylow 2 M) (A : Subgroup M)
    (hAP : A ≤ (P : Subgroup M)) (hA : IsOffender S.representation A) :
    A = A0 S P := by
  let := S.finite_group
  let := hA.1.2
  have hAL := S.four_offender_le_layer A hA
  have hle : A ≤ S.naturalSylowNormalizer P := by
    rw [naturalSylowNormalizer, S.naturalNormalizer_eq_layer]
    exact le_inf hAP hAL
  have hc : 16 ≤ Nat.card A := by
    rw [hA.1.card_eq_two_pow_rank]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (S.four_offender_rank_ge_four A hA)
  let := hA.1.2.map (group S P).toMonoidHom
  apply Subgroup.map_injective (f := (group S P).toMonoidHom) (group S P).injective
  rw [actor_map]
  apply BinaryNaturalDual.FourActors.PermutationCatalogue.T0_inner_elementary_eq_A0_of_card_ge
  · rw [← naturalSylow_map S P]
    exact map_mono hle
  · rwa [card_map_of_injective (group S P).injective]

/-- The offender budget is sharp: every offender has rank and fixed codimension four. -/
theorem four_offender_parameters (A : Subgroup M) (hA : IsOffender S.representation A) :
    rank A = 4 ∧ fixedCodim S.representation A = 4 := by
  let := S.finite_group
  let : FiniteDimensional (ZMod 2) E := S.model.coordinates.symm.finiteDimensional
  obtain ⟨P,hP⟩ := hA.1.2.isPGroup.exists_le_sylow
  rw [S.four_offender_eq_A0 P A hP hA]
  have hc := actor_card S P 0
  have hf := (A0_parameters S P).1
  have hd : Module.finrank (ZMod 2) E = 8 := by
    rw [S.model.coordinates.finrank_eq]
    simp [BinaryNaturalDual.CoordinateSpace, BinaryNaturalDual.Space,
      BinaryLinear.OuterCyclic.Space, Module.finrank_prod, Subspace.dual_finrank_eq]
  constructor
  · unfold rank
    rw [hc]
    decide
  · have hs := fixedCodim_add_finrank S.representation (A0 S P)
    change Module.finrank (ZMod 2) (fixedSpace S.representation (A0 S P)) = 4 at hf
    omega
end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup

namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
open SourceFourActors Stellmacher
variable {M E : Type*} [Group M] [AddCommGroup E] [Module (ZMod 2) E]
  (S : SourceSetup 4 M E)

/-- A moving Thompson image on the original action is exactly the marked
inner elementary sixteen. No equality of Thompson subgroups across a
noninjective quotient is assumed. -/
theorem four_thompson_image_eq {H : Type*} [Group H] [Finite H]
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* M) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H))
    (e : Additive U ≃ₗ[ZMod 2] E)
    (he : ∀ a v, e (NormalElementaryQuotient.representation U q hq hk a v) =
      S.representation a (e v))
    (R : Subgroup H) (hUR : U ≤ R) (P : Sylow 2 M)
    (hRP : R.map q ≤ (P : Subgroup M))
    (hm : ¬ elementaryAbelianMaxJ R ≤ q.ker) :
    (elementaryAbelianMaxJ R).map q = A0 S P := by
  let := S.finite_group
  have himage (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups R)
      (hn : ¬ A ≤ q.ker) : A.map q = A0 S P := by
    have ho := NormalElementaryQuotient.maxElementary_isOffender U q hq hk R A hUR hA hn
    have ho' := ho.map_equivariant _ S.representation (MonoidHom.id M)
      Function.injective_id e he
    rw [Subgroup.map_id] at ho'
    exact S.four_offender_eq_A0 P _ ((map_mono hA.1).trans hRP) ho'
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    apply sSup_le
    intro A hA
    rw [←map_le_iff_le_comap]
    by_cases hn : A ≤ q.ker
    · rw [(map_eq_bot_iff A).mpr hn]
      exact bot_le
    · exact (himage A hA hn).le
  · obtain ⟨A,hA,hn⟩ : ∃ A ∈ elementaryAbelianMaxSubgroups R, ¬ A ≤ q.ker := by
      by_contra! hh
      exact hm (sSup_le hh)
    rw [←himage A hA hn]
    exact map_mono (le_sSup hA)
end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
open Stellmacher ChapterH.NaturalDual.SourceFourActors
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {B : DoubledBranch T L V 4}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

/-- Literal normalizer-quotient version of the unique offender assertion. -/
theorem four_thompson_image (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hm : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (componentOrbit V (T : Subgroup G) : Set G)) :
    ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf (normalizer (L : Set G))).map
      B.actionProjection =
        A0 S.setup ((T.subtype hTM).mapSurjective B.actionProjection_surjective) := by
  let W := componentOrbit V (T : Subgroup G)
  let M := normalizer (L : Set G)
  have hWM : W ≤ M := hWT.trans hTM
  have hMW : M ≤ normalizer (W : Set G) := by
    dsimp [W,M]
    rw [B.orbit_eq]
    exact le_normalizer_componentOrbit _ _
  let U := W.subgroupOf M
  let : U.Normal := normal_subgroupOf_of_le_normalizer hMW
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hWM
  let q := B.actionProjection
  have hq : Function.Surjective q := B.actionProjection_surjective
  have hk : q.ker = centralizer (U : Set M) := by
    rw [show q.ker = (normalizerAction T L V B.orbit_eq).ker from QuotientGroup.ker_mk' _,
      normalizerAction_ker]
    ext m
    constructor
    · intro hm u hu
      exact Subtype.ext (hm u hu)
    · intro hm w hw
      exact congrArg M.subtype (hm ⟨w,hWM hw⟩ hw)
  let ρ := NormalElementaryQuotient.representation U q hq hk
  let E : Additive U ≃ₗ[ZMod 2] Additive W :=
    LinearEquiv.ofBijective ((subgroupOfEquivOfLe hWM).toMonoidHom.toAdditive.toZModLinearMap 2)
      (subgroupOfEquivOfLe hWM).bijective
  have hE (a : B.ActionQuotient) (v : Additive U) :
      E (ρ a v) = S.setup.representation a (E v) := by
    obtain ⟨m,rfl⟩ := hq a
    apply Additive.toMul.injective
    apply Subtype.ext
    change (((ρ (q m) v).toMul : M) : G) =
      ((S.setup.representation (q m) (E v)).toMul : G)
    rw [S.representation_eq]
    change (((ρ (q m) v).toMul : M) : G) =
      (B.quotientAction (B.actionProjection m) (E v).toMul : G)
    rw [B.quotientAction_projection_apply]
    exact congrArg M.subtype (NormalElementaryQuotient.representation_apply U q hq hk m v)
  let R := (T : Subgroup G).subgroupOf M
  have hJR : (elementaryAbelianMaxJ R).map M.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,
      map_subgroupOf_eq_of_le hTM]
  have hJR' : elementaryAbelianMaxJ R =
      (elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf M := by
    apply map_injective M.subtype_injective
    have hJM : elementaryAbelianMaxJ (T : Subgroup G) ≤ M :=
      (show elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) from
        sSup_le fun _ hA => hA.1).trans hTM
    rw [hJR,map_subgroupOf_eq_of_le hJM]
  have hn : ¬ elementaryAbelianMaxJ R ≤ q.ker := by
    intro hc
    apply hm
    rw [←hJR]
    rintro _ ⟨a,ha,rfl⟩ w hw
    exact congrArg M.subtype ((hk ▸ hc ha) ⟨w,hWM hw⟩ hw)
  have hh := S.setup.four_thompson_image_eq U q hq hk E hE R
    (fun x hx => hWT hx)
    ((T.subtype hTM).mapSurjective B.actionProjection_surjective) le_rfl hn
  rwa [hJR'] at hh
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Stellmacher ChapterH.NaturalDual.SourceFourActors
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The contrary ambient Sylow branch constructs the original rank-four
Thompson image needed by the parabolic step of 12.1.4. -/
theorem doubleNatural_four_pure_thompson_image_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf (normalizer (L : Set G))).map
        B.actionProjection = A0 S.setup
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  exact S.four_thompson_image D.sylow_normalizes_component (D.doubledOrbit_E322 h).le_sylow
    (D.doubleNatural_four_pure_thompson_moves_of_many h hmany B S w hw hp hfix hf).2
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
