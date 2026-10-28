module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.ResidualPair
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.ThreeSpace
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupAction.ElementaryEightPointEnlargement
public import Theory.Representation.BinaryConjugacyOrbit

/-!
# The seven-point involution orbit in the HS contrary branch

The literal omitted-point parabolic has index seven in LT and equals I₂T.
It centralizes e in Z(I₂) intersect Ω₁(Z(T)). Its prime index makes it the
whole stabilizer unless LT centralizes e, which the preceding 14.3.25
excludes. Thus the original orbit has exactly seven points.

The reduced module Ve = ⟨e^L⟩ also equals ⟨e^LT⟩. Its centralizer is exactly
O₂(LT): reducedness gives one containment, and simplicity of the original
natural quotient gives the other. The binary orbit-sum map is an actual
surjective intertwiner from the seven-point permutation module to Ve, with
three ≤ dim(Ve) ≤ seven and the exact two-core kernel. The final theorem
applies this to the involution supplied by the actual contrary center.

These are the orbit and kernel inputs to 14.3.29. The Fano-line comparison,
the dual-natural quotient, and Thompson normality remain to be proved.
The explicit 14.3.25 exclusion and the later centerlessness contradictions
remain with qt-d-hs-centerless-source; final LocalStructure assembly remains
with qt-d-hs-local-structure. No later natural S5 conclusion is used.

Source: Aschbacher--Smith, 14.3.29, printed p.1002; H.5.3, p.386,
and B.2.14, p.78, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original plane stabilizer has index seven in LT under its full natural action. -/
theorem source_plane_parabolic_index (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) :
    (F.P L).relIndex (L ⊔ (T : Subgroup G)) = 7 := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  let β := F.naturalFlagCoordinates
  let e := naturalFlagActorEquiv β
  let f := F.naturalFlagAction L chosen.normalizes
  have hf : Function.Surjective f := F.naturalFlagAction_surjective L chosen.normalizes h.full_L_action
  have hp : (F.P L).subgroupOf (L ⊔ (T : Subgroup G)) =
      (F.naturalFlagStabilizer 2).comap f := by
    ext x
    simp only [mem_comap, f, naturalFlagAction_mem_stabilizer, mem_subgroupOf,
      P, mem_inf, mem_iInf]
    exact ⟨fun hx => hx.2 2 ⟨by decide, by decide⟩,
      fun hx => ⟨x.property, fun i hi => by
        have hi2 : i = 2 := by omega
        simpa only [hi2] using hx⟩⟩
  change ((F.P L).subgroupOf (L ⊔ (T : Subgroup G))).index = 7
  rw [hp, index_comap_of_surjective _ hf]
  rw [← index_map_of_bijective (f := e.toMonoidHom) e.bijective (F.naturalFlagStabilizer 2),
    F.naturalFlagStabilizer_map β 2]
  exact BinaryLinear.FourParabolicAction.threeSpace_hyperplane_index _
    (Module.finrank_fin_fun (ZMod 2)) (F.naturalFlagSpace_finrank β 2 (by decide))

/-- The literal omitted-point parabolic is I₂T, with its normal two-core inside T. -/
theorem source_parabolic_eq_I₂_sylow (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) :
    F.P L = F.I₂ L ⊔ (T : Subgroup G) := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨g, hgP, hgH⟩ := source_conjugator d earlier hq chosen structural F
  obtain ⟨hc, hs⟩ := F.localKernel_commutator_squares d.qtke L
    (normalizer (L : Set G)) (by decide) chosen.le_sylow chosen.normalizes
    (h.sylow_normalizes structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape F alternatives)
  obtain ⟨_, _, _, _, _, _, _, _, hfactor, _⟩ := F.binary_generation (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT structural) hc hs
    (source_seed_geometry d earlier hq chosen F).2.1 hne g hgP hgH
  have hcore : (F.P L).pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 (F.P L)).le_sylow_of_normalized T
      ((F.binary_sylow_le_P L).trans ((F.P L).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (F.P L)))))
  apply le_antisymm
  · rw [hfactor]
    exact sup_le (hcore.trans le_sup_right) le_sup_left
  · exact sup_le (le_sup_right.trans hfactor.ge) (F.binary_sylow_le_P L)

/-- Source 14.3.25 makes I₂T the exact centralizer of the chosen involution in LT. -/
theorem source_involution_stabilizer (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (e : G) (he : orderOf e = 2)
    (heI : e ∈ Chapter12.Section08.centerIn (F.I₂ L)) (heT : e ∈ sylowOmega T) :
    (L ⊔ (T : Subgroup G)) ⊓ centralizer ({e} : Set G) = F.P L := by
  let A := L ⊔ (T : Subgroup G)
  let C := A ⊓ centralizer ({e} : Set G)
  have hPC : F.P L ≤ C := by
    apply le_inf inf_le_left
    change F.P L ≤ centralizer ({e} : Set G)
    rw [source_parabolic_eq_I₂_sylow d earlier hq chosen structural alternatives F hne]
    apply sup_le
    · obtain ⟨z, hz, rfl⟩ := heI
      intro x hx
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_center_iff.mp hz ⟨x, hx⟩))
    · intro t ht
      exact mem_centralizer_singleton_iff.mpr (omega_centralizes_sylow heT t ht)
  have hind := relIndex_mul_relIndex (F.P L) C A hPC inf_le_left
  rw [source_plane_parabolic_index d earlier hq chosen F] at hind
  rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp
    (dvd_of_mul_left_eq ((F.P L).relIndex C) hind) with hindex | hindex
  · have hAC : A ≤ C := relIndex_eq_one.mp hindex
    have heU : e ∈ F.U := (map_subtype_le (center F.U))
      ((source_center_location d earlier hq chosen structural alternatives F hne).1 heI)
    have heZ : e ∈ centralLTSeed F L := by
      refine ⟨?_, heU⟩
      rw [centerIn_eq_inf_centralizer]
      refine ⟨mem_sup_right ((source_center_location d earlier hq chosen structural alternatives F hne).2.1 heI), ?_⟩
      intro x hx
      exact mem_centralizer_singleton_iff.mp (hAC hx).2
    have he1 : e = 1 := by simpa [hseed] using heZ
    simp [he1] at he
  · have hrel : (F.P L).relIndex C = 1 := by rw [hindex] at hind; omega
    exact le_antisymm (relIndex_eq_one.mp hrel) hPC


/-- The orbit of the actual involution has seven elements, with ambient representatives. -/
theorem source_involution_orbit_card (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (e : G) (he : orderOf e = 2)
    (heI : e ∈ Chapter12.Section08.centerIn (F.I₂ L)) (heT : e ∈ sylowOmega T) :
    Nat.card {x : G // ∃ a ∈ L ⊔ (T : Subgroup G), a * e * a⁻¹ = x} = 7 := by
  have hc : Nat.card (Representation.BinaryConjugacyOrbit.Orbit (L ⊔ (T : Subgroup G)) e) = 7 := by
    rw [Representation.BinaryConjugacyOrbit.orbit_card, ← inf_relIndex_right,
      inf_comm (centralizer ({e} : Set G)),
      source_involution_stabilizer d earlier hq chosen structural alternatives F hne hseed e he heI heT]
    exact source_plane_parabolic_index d earlier hq chosen F
  have heq := Set.ext (fun x =>
    Representation.BinaryConjugacyOrbit.mem_orbit (L ⊔ (T : Subgroup G)) e x)
  rw [show {x : G // ∃ a ∈ L ⊔ (T : Subgroup G), a * e * a⁻¹ = x} =
    Representation.BinaryConjugacyOrbit.Orbit (L ⊔ (T : Subgroup G)) e from
      congrArg (fun S : Set G => ↥S) heq.symm]
  exact hc

/-- The reduced involution orbit has precisely O₂(LT) as its action centralizer. -/
theorem source_involution_orbit_centralizer (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (e : G) (he : orderOf e = 2)
    (heI : e ∈ Chapter12.Section08.centerIn (F.I₂ L)) (heT : e ∈ sylowOmega T) :
    (L ⊔ (T : Subgroup G)) ⊓ centralizer (conjugateSpanBy (zpowers e) L : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  let A := L ⊔ (T : Subgroup G)
  let W := conjugateSpanBy (zpowers e) L
  have hr := source_involution_orbit_reduced d earlier hq chosen structural F e he heT
  let : (W.subgroupOf A).Normal := hr.normal
  let N := centralizer (W.subgroupOf A : Set A)
  have hWA : W ≤ A := conjugateSpanBy_le
    (zpowers_le.mpr (mem_sup_right
      ((source_center_location d earlier hq chosen structural alternatives F hne).2.1 heI)))
    (le_sup_left.trans A.le_normalizer)
  have heW : e ∈ W := le_conjugateSpanBy (zpowers e) L (mem_zpowers e)
  have hNmap : N.map A.subtype = A ⊓ centralizer (W : Set G) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.property, fun w hw => ?_⟩
      exact congrArg Subtype.val (ha ⟨w, hWA hw⟩ hw)
    · intro hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      intro w hw
      exact Subtype.ext (hx.2 w hw)
  have hcore : pCore 2 A ≤ N := le_centralizer_iff.mp hr.le_centralizer_pCore
  let f := F.naturalFlagAction L chosen.normalizes
  have hf : Function.Surjective f := F.naturalFlagAction_surjective L chosen.normalizes h.full_L_action
  have hk : f.ker = pCore 2 A := by
    apply map_injective A.subtype_injective
    have hfk : f.ker = (centralizer (V : Set G)).subgroupOf A := by
      exact setupSeedAction_ker A V (sup_le chosen.normalizes (h.sylow_normalizes_seed structural))
    rw [hfk, subgroupOf_map_subtype, inf_comm]
    exact h.centralizer_LT structural
  obtain ⟨c⟩ := MulAut.elementaryEight_equiv_PSL3 (show Nat.card V = 8 by simpa [F.last] using F.card 3 (by decide))
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup (MulAut V) := c.isSimpleGroup
  have hnormal : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hN : N = pCore 2 A := by
    rcases hnormal.eq_bot_or_eq_top with hbot | htop
    · exact le_antisymm (hk ▸ (map_eq_bot_iff N).mp hbot) hcore
    · have hh := congrArg (comap f) htop
      rw [comap_map_eq, comap_top, hk, sup_eq_left.mpr hcore] at hh
      have hAC : A ≤ centralizer ({e} : Set G) := by
        intro a ha
        have ham : (⟨a, ha⟩ : A) ∈ N := hh.symm ▸ mem_top _
        exact mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (ham ⟨e, hWA heW⟩ heW)).symm
      have hP : F.P L = A := by
        rw [← source_involution_stabilizer d earlier hq chosen structural alternatives F hne hseed e he heI heT]
        exact inf_eq_left.mpr hAC
      have hi := source_plane_parabolic_index d earlier hq chosen F
      rw [hP, relIndex_self] at hi
      norm_num at hi
  rw [← hNmap, hN]
  rfl

open Representation.BinaryConjugacyOrbit

/-- Adjoining the Sylow does not enlarge the L-orbit span of its central involution. -/
theorem source_involution_span_eq (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : G) (heT : e ∈ sylowOmega T) :
    Span (L ⊔ (T : Subgroup G)) e = conjugateSpanBy (zpowers e) L := by
  exact conjugateSpanBy_sup_of_normalizes_seed _ _ _
    ((le_centralizer_iff.mp (zpowers_le.mpr (omega_centralizes_sylow heT))).trans
      (Subgroup.centralizer_le_normalizer _))
    ((higherRankHypothesis d earlier hq chosen).sylow_normalizes structural)

/-- The actual Ve is a faithful quotient, modulo O₂(LT), of its seven-point binary permutation module. -/
theorem source_involution_permutation_quotient (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (e : G) (he : orderOf e = 2)
    (heI : e ∈ Chapter12.Section08.centerIn (F.I₂ L)) (heT : e ∈ sylowOmega T) :
    Nat.card (Orbit (L ⊔ (T : Subgroup G)) e) = 7 ∧
    ∃ hE : IsElementaryAbelian 2 (Span (L ⊔ (T : Subgroup G)) e), letI := hE
      Function.Surjective (quotient (L ⊔ (T : Subgroup G)) e) ∧
      3 ≤ Module.finrank (ZMod 2) (Additive (Span (L ⊔ (T : Subgroup G)) e)) ∧
      Module.finrank (ZMod 2) (Additive (Span (L ⊔ (T : Subgroup G)) e)) ≤ 7 ∧
      (representation (L ⊔ (T : Subgroup G)) e).ker = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) ∧
      Span (L ⊔ (T : Subgroup G)) e = conjugateSpanBy (zpowers e) L ∧
      (L ⊔ (T : Subgroup G)) ⊓ centralizer (Span (L ⊔ (T : Subgroup G)) e : Set G) =
        (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let A := L ⊔ (T : Subgroup G)
  have hspan := source_involution_span_eq d earlier hq chosen structural e heT
  have hr : IsPReduced 2 ((Span A e).subgroupOf A) := by
    rw [hspan]
    exact source_involution_orbit_reduced d earlier hq chosen structural F e he heT
  have hWA : Span A e ≤ A := conjugateSpanBy_le_self (zpowers_le.mpr
    (mem_sup_right ((source_center_location d earlier hq chosen structural alternatives F hne).2.1 heI)))
  let := hr.elementary
  have hE : IsElementaryAbelian 2 (Span A e) := by
    rw [← map_subgroupOf_eq_of_le hWA]
    exact IsElementaryAbelian.map_subtype
  let := hE
  have hc : Nat.card (Orbit A e) = 7 := by
    rw [orbit_card, ← inf_relIndex_right,
      inf_comm (centralizer ({e} : Set G)),
      source_involution_stabilizer d earlier hq chosen structural alternatives F hne hseed e he heI heT]
    exact source_plane_parabolic_index d earlier hq chosen F
  refine ⟨hc, hE, quotient_surjective A e, ?_, ?_, ?_, hspan, ?_⟩
  · have hinj := Nat.card_le_card_of_injective _ (element_injective A e)
    rw [hc, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hinj
    by_contra hsmall
    change ¬ 3 ≤ Module.finrank (ZMod 2) (Additive (Span A e)) at hsmall
    have hd : Module.finrank (ZMod 2) (Additive (Span A e)) ≤ 2 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hd
    omega
  · exact (dimension_le_orbit_card A e).trans hc.le
  · apply map_injective A.subtype_injective
    rw [representation_ker, subgroupOf_map_subtype, inf_comm, hspan]
    exact source_involution_orbit_centralizer d earlier hq chosen structural alternatives F hne hseed e he heI heT
  · rw [hspan]
    exact source_involution_orbit_centralizer d earlier hq chosen structural alternatives F hne hseed e he heI heT

/-- Apply the orbit construction to an involution extracted from the actual
nontrivial parabolic center. The only later premise is the preceding 14.3.25
seed exclusion, still owned by this centerlessness branch. -/
theorem source_contrary_orbit_quotient (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ e : G, orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧ e ∈ F.ZU ∧ e ∉ F.Vi 1 ∧
      Nat.card (Orbit (L ⊔ (T : Subgroup G)) e) = 7 ∧
      ∃ hE : IsElementaryAbelian 2 (Span (L ⊔ (T : Subgroup G)) e), letI := hE
        Function.Surjective (quotient (L ⊔ (T : Subgroup G)) e) ∧
        3 ≤ Module.finrank (ZMod 2) (Additive (Span (L ⊔ (T : Subgroup G)) e)) ∧
        Module.finrank (ZMod 2) (Additive (Span (L ⊔ (T : Subgroup G)) e)) ≤ 7 ∧
        (representation (L ⊔ (T : Subgroup G)) e).ker = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) ∧
        Span (L ⊔ (T : Subgroup G)) e = conjugateSpanBy (zpowers e) L ∧
        (L ⊔ (T : Subgroup G)) ⊓ centralizer (Span (L ⊔ (T : Subgroup G)) e : Set G) =
          (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨e, he, heI, heT, heU, heV⟩ :=
    source_center_involution d earlier hq chosen structural alternatives F hne hI
  exact ⟨e, he, heI, heT, heU, heV,
    source_involution_permutation_quotient d earlier hq chosen structural alternatives F hne hseed e he heI heT⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
