module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.ShiftedType
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Homogeneity.PointMarking
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.BinaryTwo
public import Theory.LinearAlgebra.AlternatingPlaneStabilizer
public import Theory.GroupTheory.PPerfectHom

/-!
# The shifted involution and the marked seed-plane stabilizer

The point residual L1 has nontrivial image on U/Z(U), since its natural
cubic action on V/V1 survives the equality V intersect Z(U) = V1.
Uniqueness of alternating displacement on a binary plane makes the shifted
involution commute with the original plane stabilizer. Its centralizer in
the faithful action quotient therefore contains both a full Sylow and the
nontrivial two-perfect image of L1; it cannot be a two-group.

The final theorem transports this witness through an actual quotient
isomorphism. SymmetricFive and AlternatingSix use it to exclude their
literal earlier action rows. The 14.3.25 seed exclusion remains explicit
and stays with this centerlessness owner, as do the other final branches.

Source: Aschbacher--Smith, 12.8.5, 14.3.30--31, printed pp.850,1002--1003.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The natural cubic action of the actual point residual survives in U/Z(U). -/
theorem source_point_residual_uhat_nontrivial (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) :
    ∃ k : F.Li L 1, F.uhatAction ⟨k, (F.Li_le L 1 k.property).2⟩ ≠ 1 := by
  let := chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient (by decide) L chosen.normalizes h.naturalMarking
  have hvz := (CaseOneGeometry.source_closure d earlier hq chosen structural alternatives F hne).2.2
  by_contra hall
  have hk (k : F.Li L 1) : k ∈ pCore 2 (F.Li L 1) := by
    rw [← D.seedAction_ker]
    apply (F.mem_tildeAction_ker_iff _ _ _
      ((le_conjugateSpanBy V F.H).trans F.U_le_H) _ k).mpr
    intro v hv
    rw [← hvz]
    constructor
    · have hn := chosen.normalizes (F.Li_le L 1 k.property).1
      change (k : G) * v * (k : G)⁻¹ * v⁻¹ ∈ V
      exact V.mul_mem
        ((mem_normalizer_iff.mp hn v).mp hv) (V.inv_mem hv)
    · have he : F.uhatAction ⟨k, (F.Li_le L 1 k.property).2⟩ = 1 := by
        by_contra hn
        exact hall ⟨k, hn⟩
      exact (F.mem_uhatAction_ker_iff _).mp he v (le_conjugateSpanBy V F.H hv)
  obtain ⟨c, hc⟩ := BinaryLinear.OuterCyclic.BinaryTwo.derived_transitive_nonzero
    (by decide : (![1,0] : Fin 2 → ZMod 2) ≠ 0)
    (by decide : (![0,1] : Fin 2 → ZMod 2) ≠ 0)
  obtain ⟨q, hq⟩ := D.quotientEquiv.surjective c
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.Li L 1)) q
  have he : QuotientGroup.mk' (pCore 2 (F.Li L 1)) k = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (hk k)
  rw [he, map_one] at hq
  rw [← hq] at hc
  have hf := congrFun hc 0
  norm_num at hf

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Uniqueness of alternating displacement on the marked binary plane forces
commutation with every element of its stabilizer in the original H-action. -/
theorem uhat_commute_of_alternating_plane (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (hB : B.Nondegenerate)
    (hi : ∀ (h : F.H) (x y : F.Uhat),
      B (Additive.ofMul (F.uhatAction h x)) (Additive.ofMul (F.uhatAction h y)) =
        B (Additive.ofMul x) (Additive.ofMul y))
    (hd : Module.finrank (ZMod 2) (F.hatSubspace V) = 2)
    (a : F.H) (ha : F.uhatAction a ≠ 1)
    (hAlt : ∀ x, B (F.uhatDisplacement a x) x = 0)
    (hmove : (F.uhatDisplacement a).range ≤ F.hatSubspace V)
    (b : F.H) (hb : (b : G) ∈ normalizer (V : Set G)) :
    Commute (F.uhatAction a) (F.uhatAction b) := by
  let t (h : F.H) : Additive F.Uhat ≃ₗ[ZMod 2] Additive F.Uhat :=
    { (F.uhatAction h).toAdditive with map_smul' := ZMod.map_smul (F.uhatAction h).toAdditive }
  have hta : t a ≠ 1 := by
    intro he
    apply ha
    ext x
    exact Additive.ofMul.injective (LinearEquiv.congr_fun he (Additive.ofMul x))
  have hstable : (F.hatSubspace V).map (t b).toLinearMap ≤ F.hatSubspace V := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨v, hv, he⟩ := hw
    change F.uhatProjection v = w.toMul at he
    refine ⟨F.uAction b v, (mem_normalizer_iff.mp hb (v : G)).mp hv, ?_⟩
    change F.uhatProjection (F.uAction b v) = F.uhatAction b w.toMul
    rw [← he]
    exact (F.uhatAction_apply_mk b v).symm
  have hh := Theory.LinearAlgebra.alternating_plane_actor_commutes B hB (F.hatSubspace V)
    hd (t a) (t b) hta hAlt hmove (fun x y => hi b x.toMul y.toMul) hstable
  apply MulEquiv.ext
  intro x
  exact Additive.ofMul.injective (LinearEquiv.congr_fun hh (Additive.ofMul x))

/-- The actual shifted involution has a full Sylow in its centralizer,
which is not a two-group. Every group identification uses the literal action
kernel quotient, without a two-core identification. -/
theorem source_involution_large_centralizer (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥)
    {D : Type*} [Group D] [Finite D] (e : (F.H ⧸ F.uhatAction.ker) ≃* D) :
    ∃ a : D, orderOf a = 2 ∧ ∃ P : Sylow 2 D,
      (P : Subgroup D) ≤ centralizer ({a} : Set D) ∧
      ¬ IsPGroup 2 (centralizer ({a} : Set D)) := by
  obtain ⟨_, g, l, z, _, _, _, _, _, _, _, _, _, _, _, _, haH, ha, hfaith,
    ⟨helem, B, hAlt, hND, hi, hmove, halt⟩, _⟩ :=
    source_shifted_amalgam_type d earlier hq chosen structural alternatives F hne hseed hI
  let := helem
  let a : F.H := ⟨l⁻¹ * z * l, haH⟩
  let := chosen.elementary
  let q := e.toMonoidHom.comp (QuotientGroup.mk' F.uhatAction.ker)
  have hqs : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqa : q a ≠ 1 := by
    intro hh
    have hh' : QuotientGroup.mk' F.uhatAction.ker a = 1 :=
      e.injective (hh.trans e.map_one.symm)
    exact hfaith ((QuotientGroup.eq_one_iff _).mp hh')
  have hq2 : orderOf (q a) = 2 := by
    apply orderOf_eq_prime_iff.mpr
    refine ⟨?_, hqa⟩
    rw [← map_pow]
    have hh : a ^ 2 = 1 := Subtype.ext (orderOf_eq_prime_iff.mp ha).1
    rw [hh, map_one]
  have hcomm (b : F.H) (hb : (b : G) ∈ normalizer (V : Set G)) :
      Commute (q a) (q b) := by
    have hdim := CaseOneGeometry.seed_hat_dimension F
      (CaseOneGeometry.source_closure d earlier hq chosen structural alternatives F hne).2.2
    have hc := uhat_commute_of_alternating_plane F B hND hi hdim a hfaith
      (fun x => hAlt.eq_iff.mp (halt x)) hmove.le b hb
    have hqcomm : Commute (QuotientGroup.mk' F.uhatAction.ker a)
        (QuotientGroup.mk' F.uhatAction.ker b) := by
      apply (QuotientGroup.kerLift_injective F.uhatAction)
      simpa only [map_mul, QuotientGroup.mk'_apply, QuotientGroup.kerLift_mk] using hc.eq
    exact hqcomm.map e.toMonoidHom
  let P := (T.subtype (F.invariant 1)).mapSurjective hqs
  have hPC : (P : Subgroup _) ≤ centralizer ({q a} : Set _) := by
    rintro y hy
    obtain ⟨b, hb, rfl⟩ := hy
    have hn : (b : G) ∈ normalizer (F.Vi 3 : Set G) := F.invariant 3 hb
    rw [F.last] at hn
    exact mem_centralizer_singleton_iff.mpr (hcomm b hn).symm.eq
  let f := q.comp (inclusion (show F.Li L 1 ≤ F.H from (F.Li_le L 1).trans inf_le_right))
  have hp : IsPPerfect 2 (F.Li L 1) := by
    change IsPPerfect 2 ((pResidual 2 (↥(L ⊓ F.Gi 1))).map (L ⊓ F.Gi 1).subtype)
    exact isPPerfect_embedded_pResidual 2 _
  refine ⟨q a, hq2, P, hPC, ?_⟩
  intro htwo
  let f' := f.codRestrict (centralizer ({q a} : Set D)) (fun k =>
    mem_centralizer_singleton_iff.mpr
      (hcomm _ (chosen.normalizes (F.Li_le L 1 k.property).1)).symm.eq)
  have hf' := hp.hom_eq_one_of_isPGroup htwo f'
  have hf : f = 1 := by
    apply MonoidHom.ext
    intro k
    exact congrArg Subtype.val (congrArg (fun f => f k) hf')
  obtain ⟨k, hk⟩ := source_point_residual_uhat_nontrivial d earlier hq chosen structural alternatives F hne
  have hh : q ⟨k, (F.Li_le L 1 k.property).2⟩ = 1 := congrArg (fun f => f k) hf
  have hh' : QuotientGroup.mk' F.uhatAction.ker ⟨k, (F.Li_le L 1 k.property).2⟩ = 1 :=
    e.injective (hh.trans e.map_one.symm)
  exact hk ((QuotientGroup.eq_one_iff _).mp hh')

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
