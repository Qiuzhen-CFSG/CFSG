module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.MovingFirst

/-!
# The literal quotient controlling the residual fixed factor

Conjugation acts on K/Vcirc for the actual core K. A bound [K,Q] <= Vcirc
makes this action descend through LocalSource.projection to SL3(2).
Residual idempotence gives full movement. If the quotient is elementary
and a nonidentity involution has fixed index at most 16, the established
three-conjugate estimate bounds its dimension by twelve and order by 4096.

Elementarity and the geometric fixed-index estimate remain explicit source
inputs. The earlier bounds and three subgroups derive Q-triviality from
elementarity without any further premise. The bound feeds FixedFactorReduction and the
original InputSetup consumer. Quotienting by the entire Z-layer would
lose precisely the fixed part at issue.
Source: Meierfrankenfeld--Stellmacher (1993), (1.1) and (4.5), printed
p.832 and pp.895,898--900.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center.CoreQuotient
open Higher Representation Representation.BinaryOffender
variable {M : Type*} [Group M] (R : Subgroup M)

instance moving_normal : ((Vcirc R (alpha R)).subgroupOf (core R (alpha R))).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((DistanceTwo.core_le_Q _).trans (fun _ hx => Vcirc_normalized _ hx.1))

abbrev Space := core R (alpha R) ⧸ (Vcirc R (alpha R)).subgroupOf (core R (alpha R))

instance [Finite M] : Finite (Space R) := by
  let := DistanceTwo.finite_core (R := R) (alpha R)
  infer_instance

private theorem action_exists :
    ∃ ρ : Mbar R →* MulAut (Space R),
      ∀ (g : Mbar R) (x : core R (alpha R)),
        ρ g (QuotientGroup.mk x) = QuotientGroup.mk
          (⟨(g : FreeAmalgam R) * (x : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹,
            le_normalizer_iff.mp (HomSaturation.core_normalized (R := R)) _ g.property _ x.property⟩ : core R (alpha R)) := by
  exact exists_quotient_conjugation_action (Mbar R) (core R (alpha R)) (Vcirc R (alpha R))
    HomSaturation.core_normalized (by
      simpa only [alpha,stabilizer_m_base] using Vcirc_normalized (R := R) (alpha R))
    (moving_normal R)

noncomputable def localAction : M →* MulAut (Space R) :=
  (Classical.choose (action_exists R)).comp (embedM R).rangeRestrict

theorem localAction_conjugation (m : M) (x y : core R (alpha R))
    (hy : (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹) :
    localAction R m (QuotientGroup.mk x) = QuotientGroup.mk y := by
  exact (Classical.choose_spec (action_exists R) ((embedM R).rangeRestrict m) x).trans
    (congrArg (QuotientGroup.mk' ((Vcirc R (alpha R)).subgroupOf (core R (alpha R))))
      (Subtype.ext hy.symm))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center.CoreQuotient

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center.CoreQuotient
open Higher Representation Representation.BinaryOffender
variable {M : Type*} [Group M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- Q-triviality, retained as an explicit source obligation, permits descent
through the literal LocalSource projection. -/
theorem projected_action [Finite M]
    (hQ : ⁅core R (alpha R),Q R (alpha R)⁆ ≤ Vcirc R (alpha R)) :
    ∃ ρ : SL →* MulAut (Space R), ∀ m, ρ (source.projection m) = localAction R m := by
  let τ := Classical.choose (action_exists R)
  have hkill := quotient_conjugation_action_kills_commutator_layer
    (Mbar R) (core R (alpha R)) (Vcirc R (alpha R)) (Q R (alpha R))
    (moving_normal R) HomSaturation.core_normalized hQ τ
    (Classical.choose_spec (action_exists R))
  have hk : source.projection.ker ≤ (localAction R).ker := by
    intro m hm
    rw [source.projection_kernel] at hm
    apply hkill
    change embedM R m ∈ Q R (alpha R)
    rw [Q_alpha R source.two_group source.core_le]
    exact mem_map_of_mem _ hm
  refine ⟨source.projection.liftOfSurjective source.projection_surjective
    ⟨localAction R,hk⟩,?_⟩
  intro m
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- Residual idempotence makes the entire literal core quotient a moving group. -/
theorem full_movement [Finite M] (ρ : SL →* MulAut (Space R))
    (hρ : ∀ m, ρ (source.projection m) = localAction R m) :
    commutatorAction ρ.range (Space R) = ⊤ := by
  let P := stabilizer R (alpha R)
  let K := core R (alpha R)
  let D := Vcirc R (alpha R)
  let e := Quotients.FirstDirect.baseEquiv R
  let ζ : P →* SL := source.projection.comp e.symm.toMonoidHom
  let τ : P →* MulAut (Space R) := ρ.comp ζ
  have hPK : P ≤ normalizer K := DistanceTwo.core_normalized _
  have hconj (g : P) (x : K) :
      τ g (QuotientGroup.mk x) = QuotientGroup.mk
        (⟨(g : FreeAmalgam R) * (x : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹,
          (mem_normalizer_iff.mp (hPK g.property) x).mp x.property⟩ : K) := by
    obtain ⟨m,rfl⟩ := e.surjective g
    change ρ (source.projection (e.symm (e m))) _ = _
    rw [e.symm_apply_apply,hρ]
    exact localAction_conjugation R m x _ rfl
  have hLm : L.map source.projection = ⊤ := by
    have hm := congrArg (Subgroup.map source.projection) source.residual_sup_core
    rw [Subgroup.map_sup,← source.projection_kernel,map_ker_self,sup_bot_eq,
      map_top_of_surjective _ source.projection_surjective] at hm
    exact hm
  have hJ : ((Ltilde R (alpha R)).subgroupOf P).map τ = ρ.range := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨ζ x,rfl⟩
    · rintro _ ⟨g,rfl⟩
      obtain ⟨m,hm,hg⟩ := hLm.ge (mem_top g)
      refine ⟨e m,?_,?_⟩
      · change embedM R m ∈ Ltilde R (alpha R)
        rw [Ltilde_alpha,source.residual]
        exact mem_map_of_mem _ hm
      · change ρ (source.projection (e.symm (e m))) = ρ g
        rw [e.symm_apply_apply,hg]
  have hi := quotient_conjugation_commutatorAction_eq_image P K D (Ltilde R (alpha R))
    hPK (Ltilde_le_stabilizer _) (moving_normal R) τ hconj
  rw [hJ,source.core_full_commutation (alpha R) rfl,subgroupOf_self,
    map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hi
  exact hi

private theorem card_le_of_involution [Finite M] [IsElementaryAbelian 2 (Space R)]
    (ρ : SL →* MulAut (Space R)) (hfull : commutatorAction ρ.range (Space R) = ⊤)
    (t : SL) (ht : t ^ 2 = 1) (hne : t ≠ 1)
    (hsmall : (FixedPoints.subgroup (zpowers (ρ t)) (Space R)).index ≤ 16) :
    Nat.card (Space R) ≤ 4096 := by
  let space : Subgroup (Space R) ≃o Submodule (ZMod 2) (Additive (Space R)) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)
  let C := commutatorAction (zpowers (ρ t)) (Space R)
  have hd := (MulAut.involution_fixed_displacement_card_data (ρ t)
    (by rw [← map_pow,ht,map_one])).1
  have hi := (FixedPoints.subgroup (zpowers (ρ t)) (Space R)).card_mul_index
  have hp : 0 < Nat.card (FixedPoints.subgroup (zpowers (ρ t)) (Space R)) := Nat.card_pos
  have hcard : Nat.card C ≤ 16 := by dsimp only [C]; nlinarith
  have hc : 2 ^ Module.finrank (ZMod 2) (space C) ≤ 2 ^ 4 := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := space C)
    rw [Nat.card_zmod] at he
    rw [← he]
    exact hcard
  have hdim : Module.finrank (ZMod 2) (space C) ≤ 4 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  have hcodim : fixedCodim (Offenders.linearize ρ) (zpowers t) ≤ 4 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    apply (Submodule.finrank_mono (t := space C) ?_).trans hdim
    rintro _ ⟨v,rfl⟩
    change ρ t v.toMul / v.toMul ∈ commutatorAction (zpowers (ρ t)) (Space R)
    rw [div_eq_mul_inv,commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨⟨ρ t,mem_zpowers (ρ t)⟩,v.toMul,mul_comm _ _⟩
  have hmove : space (commutatorAction ρ.range (Space R)) =
      Coinvariants.ker (Offenders.linearize ρ) := by
    apply le_antisymm
    · change commutatorAction ρ.range (Space R) ≤
        (Coinvariants.ker (Offenders.linearize ρ)).toAddSubgroup.toSubgroup'
      rw [commutatorAction_eq_closure,Subgroup.closure_le]
      rintro _ ⟨⟨a,g,rfl⟩,v,rfl⟩
      change -Additive.ofMul v + Offenders.linearize ρ g (Additive.ofMul v) ∈
        Coinvariants.ker (Offenders.linearize ρ)
      simpa only [sub_eq_add_neg,add_comm] using
        Coinvariants.sub_mem_ker (ρ := Offenders.linearize ρ) g (Additive.ofMul v)
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨g,v⟩,rfl⟩
      change ρ g v.toMul / v.toMul ∈ commutatorAction ρ.range (Space R)
      rw [div_eq_mul_inv,commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨⟨ρ g,g,rfl⟩,v.toMul,mul_comm _ _⟩
  have hb := ModuleAlternatives.Models.commutator_finrank_le_three_mul
    (Offenders.linearize ρ) t ht hne
  have hrank : Module.finrank (ZMod 2) (Coinvariants.ker (Offenders.linearize ρ)) ≤ 12 := by omega
  rw [hfull,space.map_top] at hmove
  have hwhole : Module.finrank (ZMod 2) (Additive (Space R)) ≤ 12 := by
    rw [← hmove,finrank_top] at hrank
    exact hrank
  change Nat.card (Additive (Space R)) ≤ 4096
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hwhole

/-- The two remaining source inputs imply the sharp moving index. The
geometric fixed-index estimate is on this exact quotient and action. -/
theorem moving_index_bound [Finite M] [IsElementaryAbelian 2 (Space R)]
    (hQ : ⁅core R (alpha R),Q R (alpha R)⁆ ≤ Vcirc R (alpha R))
    (m : M) (ht : source.projection m ^ 2 = 1) (hne : source.projection m ≠ 1)
    (hsmall : (FixedPoints.subgroup (zpowers (localAction R m)) (Space R)).index ≤ 16) :
    (Vcirc R (alpha R)).relIndex (core R (alpha R)) ≤ 4096 := by
  obtain ⟨ρ,hρ⟩ := projected_action (source := source) hQ
  have h := card_le_of_involution ρ (full_movement ρ hρ) (source.projection m) ht hne
    (by rwa [hρ])
  exact h

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center.CoreQuotient

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center.CoreQuotient
open Higher
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- Elementarity of the literal quotient already implies Q-triviality,
using the preceding source commutator bounds and residual idempotence. -/
theorem Q_commutator_le_of_elementary
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    [IsElementaryAbelian 2 (Space R)] :
    ⁅core R (alpha R),Q R (alpha R)⁆ ≤ Vcirc R (alpha R) := by
  obtain ⟨p⟩ := Early.sourcePath_nonempty source common earlier (alpha R) rfl
  let K := core R (alpha R)
  let D := Vcirc R (alpha R)
  let A := hatV R (alpha R) (p.walk.getVert 6)
  let P := stabilizer R (alpha R)
  have hderived : ⁅K,K⁆ ≤ D := by
    apply commutator_le.mpr
    intro x hx y hy
    let π := QuotientGroup.mk' (D.subgroupOf K)
    have he : π ⁅(⟨x,hx⟩ : K),(⟨y,hy⟩ : K)⁆ = 1 := by
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    change ⁅(⟨x,hx⟩ : K),(⟨y,hy⟩ : K)⁆ ∈ D.subgroupOf K
    exact (QuotientGroup.eq_one_iff _).mp he
  have hAD : ⁅A,Ltilde R (alpha R)⁆ ≤ D := by
    have hDlocal : D ≤ P :=
      (Vcirc_le_core rfl common.large_distance).trans
        ((DistanceTwo.core_le_Q _).trans (fun _ hx => hx.1))
    have hpre : A ≤ commutatorPreimage P (Ltilde R (alpha R)) D := by
      dsimp only [A]
      rw [(Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatV_eq]
      apply sup_le
      · exact le_commutatorPreimage hDlocal
          (le_normalizer_iff_commutator_le_left.mp
            ((Ltilde_le_stabilizer _).trans (Vcirc_normalized _)))
      · exact le_commutatorPreimage (Z_le_stabilizer R _)
          (commutator_mono (Z_le_VBall R _ 2) le_rfl)
    exact (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le P (Ltilde R (alpha R)) D (Vcirc_normalized _))
  have hKQ : ⁅K,Q R (alpha R)⁆ ≤ A :=
    (commutator_mono (Early.Orbit.Source.Complete.core_le_third_hat common earlier p) le_rfl).trans
      (OrbitGeometry.Source.Q_commutator_le common earlier p)
  rw [← source.core_full_commutation (alpha R) rfl]
  apply commutator_commutator_le_of_rotate_of_le_normalizer
    (((DistanceTwo.core_le_Q _).trans (fun _ hx => hx.1)).trans (Vcirc_normalized _))
    ((Ltilde_le_stabilizer _).trans (Vcirc_normalized _))
    ((show Q R (alpha R) ≤ P from fun _ hx => hx.1).trans (Vcirc_normalized _))
  · rw [commutator_comm (Ltilde R (alpha R))]
    exact hderived
  · rw [commutator_comm (Q R (alpha R))]
    exact (commutator_mono hKQ le_rfl).trans hAD

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center.CoreQuotient
