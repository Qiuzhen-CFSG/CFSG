module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.FixedSpace
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
public import CFSG.Quasithin.ChapterE.Section01.Basic

/-!
# Literal point centralizers and outside-subgroup selection

The point is an actual nonidentity Sylow-fixed element of the source line.
Its order is two, so C_G(z) is N_G(<z>) and is a genuine two-local subgroup.
The escape argument of §11.4 and finite minimal descent construct an H-star
subgroup inside this same centralizer. The conjugate-generated component
is normal only relative to that centralizer.

The final structures are output specifications for the remaining source
proofs. They use the actual R1 Sylow image and O^2(H), the two-residual;
they do not assert existence or supply the generation-one conclusion.
Source: Aschbacher--Smith, 11.4.2--4 and 11.5.1, pp.776--779.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- The source G_z, separate from the final G1 = N_G(V1). -/
def Gz : Subgroup G := centralizer ({E.z} : Set G)
/-- The source M_z. -/
def Mz : Subgroup G := E.M ⊓ Gz E
/-- The actual quotient centralizer inside G_z, using K/O2(K). -/
def Yz : Subgroup G := Gz E ⊓ Closure.coreQuotientCentralizer E.K

/-- An elementary source point is an involution in the literal Sylow omega-center. -/
theorem point_involution (hz : E.z ∈ E.V₁) (hzt : E.z ∈ centralizer (T : Set G))
    (hz1 : E.z ≠ 1) :
    orderOf E.z = 2 ∧
      E.z ∈ omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) := by
  let := D.elementary
  have hz2 : E.z ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian E.z (E.V₁_le hz)
  refine ⟨orderOf_eq_prime hz2 hz1, (omegaOneAmbient_le_iff _ _).mp le_rfl E.z ?_ hz2⟩
  refine ⟨⟨E.z, D.le_sylow (E.V₁_le hz)⟩, ?_, rfl⟩
  exact mem_center_iff.mpr (fun t => Subtype.ext (hzt t t.property))

/-- C_G(z) is the normalizer used in the literal definition of K(V,<z>). -/
theorem point_normalizer_eq (hz : E.z ∈ E.V₁) (hzt : E.z ∈ centralizer (T : Set G))
    (hz1 : E.z ≠ 1) : normalizer (zpowers E.z : Set G) = Gz E :=
  normalizer_zpowers_eq_centralizer_of_order_two E.z (point_involution E hz hzt hz1).1

/-- The point centralizer is a genuine two-local subgroup. -/
theorem point_twoLocal (hz : E.z ∈ E.V₁) (hzt : E.z ∈ centralizer (T : Set G))
    (hz1 : E.z ≠ 1) : IsTwoLocal (Gz E) := by
  have ho := (point_involution E hz hzt hz1).1
  have hp : IsPGroup 2 (zpowers E.z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho, pow_one])
  exact ⟨zpowers E.z, fun he => hz1 (mem_bot.mp (he ▸ mem_zpowers E.z)),
    hp, (point_normalizer_eq E hz hzt hz1).symm⟩

/-- Finite descent selects the actual H-star inside G_z after the escape
step. No outside subgroup or generation value is supplied as an input. -/
theorem exists_outside_in_pointCentralizer
    (hz : E.z ∈ E.V₁) (hzt : E.z ∈ centralizer (T : Set G)) (hz1 : E.z ≠ 1)
    (h1132 : ∀ H, Hypothesis1131At D E.input E.point H →
      Proposition1132At D E.input E.point H) :
    ∃ H, H ∈ Chapter3.HStar (T : Subgroup G) E.M ∧ H ≤ Gz E := by
  classical
  have hTG : (T : Subgroup G) ≤ Gz E := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hzt t ht)
  have hout : ¬ Gz E ≤ E.M :=
    point_centralizer_outside D E.input E.point E.z hz
      (point_involution E hz hzt hz1).2 h1132
  let family : Set (Subgroup G) :=
    {H | (H ∈ Chapter1.HOver G (T : Set G) ∧ ¬ H ≤ E.M) ∧ H ≤ Gz E}
  have hmem : Gz E ∈ family :=
    ⟨⟨⟨Chapter1.mem_H_of_isTwoLocal (point_twoLocal E hz hzt hz1), hTG⟩, hout⟩, le_rfl⟩
  obtain ⟨H, hH⟩ := (Set.toFinite family).exists_minimalFor id family ⟨Gz E, hmem⟩
  refine ⟨H, ⟨hH.1.1, ?_⟩, hH.1.2⟩
  intro J hJ hJH
  exact hH.2 ⟨hJ, hJH.trans hH.1.2⟩ hJH

/-- The definition Kz = <L1^Gz> gives relative, not ambient, normality. -/
theorem point_component_relative_normal
    (hL1 : E.L₁ ≤ centralizer (E.V₁ : Set G)) (hz : E.z ∈ E.V₁) :
    E.Kz ≤ Gz E ∧ (E.Kz.subgroupOf (Gz E)).Normal := by
  have hLz : E.L₁ ≤ Gz E :=
    hL1.trans (centralizer_le (Set.singleton_subset_iff.mpr hz))
  have hKz : E.Kz ≤ Gz E := conjugateSpanBy_le_self hLz
  exact ⟨hKz, (normal_subgroupOf_iff_le_normalizer hKz).mpr
    (le_normalizer_conjugateSpanBy _ _)⟩

/-- Source selection for the surviving endgame. O^2(H) is the residual,
not the two-core; both commutator and containment are ambient statements. -/
def SelectedResidualAlternative : Prop :=
  ⁅E.K, (pResidual 2 E.H).map E.H.subtype⁆ ≤ E.K.pCoreIn 2 ∨
    (pResidual 2 E.H).map E.H.subtype ≤ E.K

/-- Output required from the 11.4.4 and 11.5.1 source construction.
There is no existence theorem for these data in this module. -/
structure OutsideRadicalWitness where
  H₁ : Subgroup G
  sylow : Sylow 2 H₁
  sylow_image : (sylow : Subgroup H₁).map H₁.subtype = E.R₁
  inside : H₁ ≤ E.H
  outside : ¬ H₁ ≤ E.M
  generation_one : ChapterE.generationParameter H₁ = 1

/-- The exact last step in the prime PSL2 alternative of 11.5.1. The
model-specific premise R1=O2(KT) is retained for the signalizer calculation. -/
theorem prime_case_impossible
    (hcore : E.R₁ = (E.K ⊔ (T : Subgroup G)).pCoreIn 2)
    (hout : ¬ E.K ≤ E.M)
    (hweak : normalizer (ChapterE.indexedWeakClosure V E.R₁ 0 : Set G) ≤ E.M) : False := by
  apply hout
  have hK : E.K ≤ normalizer (E.R₁ : Set G) := by
    rw [hcore]
    exact (le_sup_left : E.K ≤ E.K ⊔ (T : Subgroup G)).trans
      ((E.K ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  exact hK.trans ((ChapterE.normalizer_le_weakClosure_normalizer V E.R₁ 0).trans hweak)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
