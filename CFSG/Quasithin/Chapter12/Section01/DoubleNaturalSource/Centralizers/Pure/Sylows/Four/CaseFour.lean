module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.MSPair
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.CentralElimination
public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary
public import Theory.GroupTheory.PGroup.OmegaCenterIn

/-!
# Selecting the fourth MS alternative at the original pure point

The doubled orbit lies in O₂(L_wT₁), and its natural summand is perfect
under L_w. Thus the original point w belongs to Q=[O₂(L_wT₁),L_w].
Since L_wT₁ centralizes w, it belongs to Z(Q) and to Ω₁(Z(T₁)).
The natural modules in C.1.34(1)--(3) have no nonidentity fixed points,
so these alternatives cannot contain w. MS3 excludes the central omega
assertion in case (5). This leaves every literal section of case (4),
with its common quotient marking. Its central elementary four-group,
together with MS3, forces |Ω₁(Z(T₁))|>4.

The universal binary C.1.34 implication remains explicit and belongs to
`qt-rank-two-ms93`. The later Sylow contradiction and the full pure-vector
assembly remain with `qt-d-double-natural-pure-fusion`; its final parent
is `qt-d-double-natural-centralizers`. No dimension-four weak closure or
unproved local Sylow/core assertion is assumed.
Source: Aschbacher--Smith, 12.1.4, printed p.790, and C.1.34, pp.136--137.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
local notation "msCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
local notation "msOmega" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn

private theorem section_fixed_free {G A E : Type*} [Group G] [Group A]
    [AddCommGroup E] [Module (ZMod 2) E] {X U : Subgroup G}
    {a : X →* A} {ρ : Representation (ZMod 2) A E}
    (h : HasSectionModel X U ⊥ a ρ) (ha : Function.Surjective a)
    (hf : ∀ v : E, (∀ g : A, ρ g v = v) → v = 0)
    {z : G} (hz : z ∈ U) (hc : z ∈ centralizer (X : Set G)) : z = 1 := by
  obtain ⟨_,_,_,hn,e,he⟩ := h
  let := hn
  let q : U ⧸ (⊥ : Subgroup G).subgroupOf U := QuotientGroup.mk' _ ⟨z,hz⟩
  have heq : Multiplicative.toAdd (e q) = 0 := by
    apply hf
    intro g
    obtain ⟨x,rfl⟩ := ha g
    apply (he x ⟨z,hz⟩ ⟨z,hz⟩ ?_).symm
    rw [hc x x.property,mul_inv_cancel_right]
  have hq : q = 1 := e.injective (heq.trans (map_one e).symm)
  exact (QuotientGroup.eq_one_iff (⟨z,hz⟩ : U)).mp hq

private theorem natural_fixed_free (v : Fin 3 → ZMod 2)
    (hv : ∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      Representation.specialLinearNatural 3 g v = v) : v = 0 := by
  have hf : v ∈ Representation.OneCohomology.fixed
      (Representation.specialLinearNatural (k := ZMod 2) 3) := hv
  rw [Representation.OneCohomology.SLHigherNatural.fixed_eq_bot (by decide)] at hf
  exact hf

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

include S in
/-- The original point is central in the actual MS core and lies in the marked omega center. -/
theorem pure_point_ms_centers
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    (w : G) ∈ msCenter (msQ (B.pointResidual w) (B.pointSylow w)) ∧
      (w : G) ∈ msCenter (B.pointResidual w ⊔ B.pointSylow w) ∧
      (w : G) ∈ msOmega (B.pointSylow w) := by
  let W := componentOrbit V (T : Subgroup G)
  let X := B.pointResidual w
  let R := B.pointSylow w
  let J := X ⊔ R
  have hWH : W ≤ B.pointCentralizer w := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨x,hx⟩ : W) w))
  have hWR : W ≤ R := le_inf hWT hWH
  have hJH : J ≤ B.pointCentralizer w :=
    sup_le ((B.pointResidual_le w).trans inf_le_right) inf_le_right
  have hJM : J ≤ normalizer (L : Set G) :=
    sup_le (B.pointResidual_le_normalizer w) (inf_le_left.trans hTM)
  have hcore : W ≤ J.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 W)
      (hWR.trans le_sup_right) (hNM.symm ▸ hJM)
  have hNQ : B.naturalSummand ≤ msQ X R := by
    rw [← (S.pure_residual_commutators hNM w hw hp).1]
    exact commutator_mono (B.naturalSummand_le.trans hcore) le_rfl
  have hwQ : (w : G) ∈ msQ X R := hNQ ((B.mem_naturalSummand w).mpr hp)
  have hQJ : msQ X R ≤ J :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le (pCoreIn_le 2 J) le_sup_left)
  have hcentral : ∀ A : Subgroup G, A ≤ J → (w : G) ∈ A → (w : G) ∈ msCenter A := by
    intro A hAJ hwA
    refine ⟨⟨w,hwA⟩,mem_center_iff.mpr ?_,rfl⟩
    intro a
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hJH (hAJ a.property))
  refine ⟨hcentral _ hQJ hwQ,hcentral _ le_rfl (hQJ hwQ),?_⟩
  apply (mem_omegaCenterIn_iff R (w : G)).mpr
  refine ⟨hWR w.property,?_,elemPow_eq_one_of_isElementaryAbelian (p := 2) _ w.property⟩
  intro r hr
  exact mem_centralizer_singleton_iff.mp (hJH (mem_sup_right hr))

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Case (4) of C.1.34, with every layer and the same literal actor. -/
@[expose] def PureFourMSLayeredAlternative (X R : Subgroup G)
    (e : (X ⧸ pCore 2 X) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Prop :=
  let Q := msQ X R
  let Z := msCenter Q
  let C := Q ⊓ centralizer (X : Set G)
  let U := ⁅Z,X⁆
  let Phi := frattiniIn Q
  let D := Q ⊓ centralizer (Phi : Set G)
  let a := linearThreeActor e
  let v := Representation.specialLinearNatural (k := ZMod 2) 3
  IsElementaryAbelian 2 C ∧ Nat.card C = 4 ∧
    C ≤ msCenter (X ⊔ R) ∧ Z = C ⊔ U ∧ C ⊓ U = ⊥ ∧
    HasSectionModel X U ⊥ a v ∧ HasSectionModel X Phi Z a v.dual ∧
    HasSectionModel X D Phi a (v.dual.prod v.dual) ∧
    HasSectionModel X Q D a (v.prod v) ∧ MSNotCentralizerCore X R R

private theorem layered_of_ms_central_point {X R : Subgroup G}
    (hms : MSNoCharacteristicNormal X R)
    (e : (X ⧸ pCore 2 X) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcases : MSModuleAlternatives X R R 1 (ZMod 2) e)
    {w : G} (hw : w ≠ 1) (hwZ : w ∈ msCenter (msQ X R))
    (hwX : w ∈ centralizer (X : Set G)) (hwO : w ∈ msOmega R) :
    PureFourMSLayeredAlternative X R e := by
  have ha : Function.Surjective (linearThreeActor e) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hwQ : w ∈ msQ X R := map_subtype_le _ hwZ
  rcases hcases with h | h | h | h | h
  · exact (hw (section_fixed_free h.2.2 ha natural_fixed_free hwQ hwX)).elim
  · have hf : ∀ v : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2),
        (∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
          ((Representation.specialLinearNatural 3).prod
            (Representation.specialLinearNatural 3)) g v = v) → v = 0 := by
      intro v hv
      exact Prod.ext (natural_fixed_free v.1 (fun g => congrArg Prod.fst (hv g)))
        (natural_fixed_free v.2 (fun g => congrArg Prod.snd (hv g)))
    exact (hw (section_fixed_free h.1 ha hf hwQ hwX)).elim
  · exact (hw (section_fixed_free h.1 ha natural_fixed_free hwZ hwX)).elim
  · exact h
  · have hne : 1 < Nat.card (msOmega R) := by
      let : Nontrivial (msOmega R) := ⟨⟨⟨w,hwO⟩,1,fun he => hw (congrArg Subtype.val he)⟩⟩
      exact Finite.one_lt_card
    exact (omegaCenter_not_central hms hne h.2.2.2.1).elim

/-- The complete source case (4) and the central-omega bound, conditional only on binary C.1.34. -/
theorem doubleNatural_four_pure_layered_ms_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (classification : BinaryLinearThreeMSClassification KnownSimple.IsKnownSimple.{u}) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      ∃ e : (B.pointResidual w ⧸ pCore 2 (B.pointResidual w)) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        PureFourMSLayeredAlternative (B.pointResidual w) (B.pointSylow w) e ∧
          4 < Nat.card (msOmega (B.pointSylow w)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  obtain ⟨hms,he,hs⟩ := D.doubleNatural_four_pure_smallMSPair_of_many h hmany B S w hw hp hfix hf
  obtain ⟨e,hcases⟩ := classification G _ _ hms he _ hs le_rfl
  have hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G) := by
    simpa only [D.fundamentalSetup_module] using (D.fundamentalSetup h.toHypothesis1221).module_le_sylow
  obtain ⟨hwZ,hwJ,hwO⟩ := S.pure_point_ms_centers
    (D.doubledOrbit_normalizer_eq h B.orbit_eq) hWT D.sylow_normalizes_component w hw hp
  have hwX : (w : G) ∈ centralizer (B.pointResidual w : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp ((B.pointResidual_le w hx).2)
  have hl := layered_of_ms_central_point hms.characteristic e hcases
    (fun he => hw (Subtype.ext he)) hwZ hwX hwO
  refine ⟨e,hl,?_⟩
  let := hl.1
  exact lt_of_not_ge (fun hb => no_central_four hs hms.characteristic hb hl.2.1 hl.2.2.1)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
