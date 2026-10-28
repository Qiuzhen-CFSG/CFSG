module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Geometry
public import Theory.GroupTheory.ReducedNormal.CentralSeedOvergroup
public import Theory.GroupTheory.ConjugateSpanSupplement

/-!
# Reduced modules on the original HS centerlessness route

For the original central Sylow involution e, characteristic two makes
⟨e^L⟩ a reduced module for LT; adjoining the chosen seed preserves
reducedness. For Ke = ⟨KT,I₂T⟩, centralization of Z(U) by K puts Ke inside
C_G(e). Its original point orbit Ue is therefore reduced, and the literal
quotient Ke/C_Ke(Ue) has trivial two-core. The normal closure K = ⟨a^H⟩
is used in the final application, with centralization by the shifted
involution a still explicit.

These are the B.2.14 preparation steps in 14.3.29 and 14.3.31. They do not
assert the Goldschmidt hypotheses, its classification, or centerlessness.
Those source constructions remain with the same centerlessness owner.

Source: Aschbacher--Smith, printed pp.1002--1003; B.2.14, p.78.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_characteristic_in_overgroup (d : Counterexample T L)
    {A M : Subgroup G} (hlocal : IsTwoLocal M)
    (hTA : (T : Subgroup G) ≤ A) (hAM : A ≤ M) : HasCharacteristicTwo A := by
  obtain ⟨R, hMR, hR⟩ := Finite.exists_le_maximal hlocal
  have hAR := hAM.trans hMR
  have hTR := hTA.trans hAR
  have hc : HasCharacteristicTwo (A.subgroupOf R) :=
    centralizer_pCore_le_of_sylow_le (T.subtype hTR) (A.subgroupOf R)
      (comap_mono hTA) (d.qtke.evenCharacteristic T R hR hTR)
  exact hc.of_equiv (subgroupOfEquivOfLe hAR)

omit [Finite G] in
theorem point_centralizes_sylow (F : InvariantFlag T V 3) :
    F.Vi 1 ≤ centralizer (T : Set G) :=
  le_centralizer_iff.mp ((F.invariant 1).trans
    (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))))

omit [Finite G] in
theorem omega_centralizes_sylow : sylowOmega T ≤ centralizer (T : Set G) := by
  rintro e he t ht
  obtain ⟨z, hz, rfl⟩ := omegaOneAmbient_le _ he
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨t, ht⟩)

theorem source_centralizer_characteristic (d : Counterexample T L) (e : G)
    (he : orderOf e = 2) (heZ : e ∈ sylowOmega T) :
    HasCharacteristicTwo (centralizer ({e} : Set G)) := by
  apply source_characteristic_in_overgroup d (isTwoLocal_involution_centralizer he) ?_ le_rfl
  intro t ht
  exact mem_centralizer_singleton_iff.mpr (omega_centralizes_sylow heZ t ht)

theorem source_LT_characteristic (d : Counterexample T L)
    (chosen : ChosenModule T L V) (F : InvariantFlag T V 3) :
    HasCharacteristicTwo (L ⊔ (T : Subgroup G) : Subgroup G) := by
  let := chosen.elementary
  have hl : IsTwoLocal (normalizer (V : Set G)) :=
    ⟨V, chosen.ne_bot, IsElementaryAbelian.isPGroup 2 V, rfl⟩
  apply source_characteristic_in_overgroup d hl le_sup_right
  exact sup_le chosen.normalizes (by simpa only [F.last] using F.invariant 3)

/-- The literal L-orbit of the involution is a reduced module for LT. -/
theorem source_involution_orbit_reduced (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (e : G) (he : orderOf e = 2) (heZ : e ∈ sylowOmega T) :
    IsPReduced 2 ((conjugateSpanBy (zpowers e) L).subgroupOf (L ⊔ (T : Subgroup G))) := by
  let : IsElementaryAbelian 2 (zpowers e) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
      have hh := pow_card_eq_one' (x := x)
      simpa only [Nat.card_zpowers, he] using hh }
  have heT : e ∈ (T : Subgroup G) :=
    (map_subtype_le (center (T : Subgroup G))) (omegaOneAmbient_le _ heZ)
  have hZC : zpowers e ≤ centralizer (T : Set G) :=
    zpowers_le.mpr (omega_centralizes_sylow heZ)
  have hr := reduced_conjugateSpan_of_sylow_central T
    (L ⊔ (T : Subgroup G)) (zpowers e) le_sup_right (zpowers_le.mpr heT) hZC
    (source_LT_characteristic d chosen F)
  have hn : (T : Subgroup G) ≤ normalizer (zpowers e : Set G) :=
    (le_centralizer_iff.mp hZC).trans (Subgroup.centralizer_le_normalizer _)
  rwa [conjugateSpanBy_sup_of_normalizes_seed _ _ _ hn
    ((higherRankHypothesis d earlier hq chosen).sylow_normalizes structural)] at hr

/-- The source VVe belongs to R₂(LT), on the actual ambient subgroups. -/
theorem source_seed_sup_involution_orbit_reduced (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (e : G) (he : orderOf e = 2) (heZ : e ∈ sylowOmega T) :
    IsPReduced 2 ((V ⊔ conjugateSpanBy (zpowers e) L).subgroupOf
      (L ⊔ (T : Subgroup G))) := by
  have hV : V ≤ L ⊔ (T : Subgroup G) := chosen.le_sylow.trans le_sup_right
  have heT : e ∈ (T : Subgroup G) :=
    (map_subtype_le (center (T : Subgroup G))) (omegaOneAmbient_le _ heZ)
  have hE : conjugateSpanBy (zpowers e) L ≤ L ⊔ (T : Subgroup G) :=
    conjugateSpanBy_le (zpowers_le.mpr (mem_sup_right heT))
      (le_sup_left.trans (L ⊔ (T : Subgroup G)).le_normalizer)
  rw [subgroupOf_sup hV hE]
  exact ((higherRankHypothesis d earlier hq chosen).seed_reduced structural).sup
    (source_involution_orbit_reduced d earlier hq chosen structural F e he heZ)

/-- The exact group Ke = ⟨KT,I₂T⟩ on printed p.1003. -/
def amalgamGroup (F : InvariantFlag T V 3) (L K : Subgroup G) : Subgroup G :=
  (K ⊔ (T : Subgroup G)) ⊔ (F.I₂ L ⊔ (T : Subgroup G))

/-- The original point orbit Ue = ⟨V₁^Ke⟩. -/
def amalgamModule (F : InvariantFlag T V 3) (L K : Subgroup G) : Subgroup G :=
  conjugateSpanBy (F.Vi 1) (amalgamGroup F L K)

instance amalgamModule_normal (F : InvariantFlag T V 3) (L K : Subgroup G) :
    ((amalgamModule F L K).subgroupOf (amalgamGroup F L K)).Normal :=
  normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)

/-- The literal relative centralizer C_Ke(Ue), not the two-core of Ke. -/
def amalgamKernel (F : InvariantFlag T V 3) (L K : Subgroup G) :
    Subgroup (amalgamGroup F L K) :=
  centralizer ((amalgamModule F L K).subgroupOf (amalgamGroup F L K) :
    Set (amalgamGroup F L K))

instance amalgamKernel_normal (F : InvariantFlag T V 3) (L K : Subgroup G) :
    (amalgamKernel F L K).Normal := inferInstanceAs (centralizer _).Normal

abbrev AmalgamQuotient (F : InvariantFlag T V 3) (L K : Subgroup G) :=
  amalgamGroup F L K ⧸ amalgamKernel F L K

omit [Finite G] in
theorem sylow_le_amalgamGroup (F : InvariantFlag T V 3) (L K : Subgroup G) :
    (T : Subgroup G) ≤ amalgamGroup F L K := le_sup_right.trans le_sup_left

omit [Finite G] in
theorem amalgamGroup_le_centralizer (F : InvariantFlag T V 3) (K : Subgroup G)
    (e : G) (heI : e ∈ Chapter12.Section08.centerIn (F.I₂ L))
    (heT : e ∈ sylowOmega T) (heU : e ∈ F.ZU)
    (hK : K ≤ centralizer (F.ZU : Set G)) :
    amalgamGroup F L K ≤ centralizer ({e} : Set G) := by
  have hTC : (T : Subgroup G) ≤ centralizer ({e} : Set G) := fun t ht =>
    mem_centralizer_singleton_iff.mpr (omega_centralizes_sylow heT t ht)
  have hIC : F.I₂ L ≤ centralizer ({e} : Set G) := by
    obtain ⟨z, hz, rfl⟩ := heI
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hz ⟨x, hx⟩))
  exact sup_le (sup_le (fun k hk => mem_centralizer_singleton_iff.mpr
    (hK hk e heU).symm) hTC) (sup_le hIC hTC)

/-- B.2.14 on the actual point orbit in Ke. Only centralization of Z(U)
by the chosen K remains here; the shifted-center argument supplies it. -/
theorem source_amalgam_reduced (d : Counterexample T L) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) (K : Subgroup G) (e : G) (he : orderOf e = 2)
    (heI : e ∈ Chapter12.Section08.centerIn (F.I₂ L)) (heT : e ∈ sylowOmega T)
    (heU : e ∈ F.ZU) (hK : K ≤ centralizer (F.ZU : Set G)) :
    IsPReduced 2 ((amalgamModule F L K).subgroupOf (amalgamGroup F L K)) := by
  let := chosen.elementary
  let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
  have hTA := sylow_le_amalgamGroup F L K
  have hAC := amalgamGroup_le_centralizer F K e heI heT heU hK
  exact reduced_conjugateSpan_of_sylow_central T (amalgamGroup F L K) (F.Vi 1) hTA
    ((F.le_seed 1).trans chosen.le_sylow) (point_centralizes_sylow F)
    (source_characteristic_in_overgroup d (isTwoLocal_involution_centralizer he) hTA hAC)

/-- The first group-theoretic input to F.6.11, on Ke/C_Ke(Ue) itself. -/
theorem source_amalgam_quotient_core (d : Counterexample T L)
    (chosen : ChosenModule T L V) (F : InvariantFlag T V 3) (K : Subgroup G)
    (e : G) (he : orderOf e = 2)
    (heI : e ∈ Chapter12.Section08.centerIn (F.I₂ L)) (heT : e ∈ sylowOmega T)
    (heU : e ∈ F.ZU) (hK : K ≤ centralizer (F.ZU : Set G)) :
    pCore 2 (AmalgamQuotient F L K) = ⊥ :=
  (source_amalgam_reduced d chosen F K e he heI heT heU hK).quotient_pCore_eq_bot

omit [Finite G] in
/-- A shifted center involution centralizing Z(U) has an entire H-orbit
centralizing Z(U); this constructs the K used on printed p.1003. -/
theorem actor_span_centralizes (F : InvariantFlag T V 3) (a : G)
    (ha : a ∈ centralizer (F.ZU : Set G)) :
    conjugateSpanBy (zpowers a) F.H ≤ centralizer (F.ZU : Set G) :=
  conjugateSpanBy_le (zpowers_le.mpr ha)
    ((le_normalizer_conjugateSpanBy V F.H).trans
      ((normalizer_le_normalizer_characteristic_image F.U (center F.U)).trans
        (normalizer_le_normalizer_centralizer F.ZU)))

/-- Apply reducedness to the source's actual normal closure K = ⟨a^H⟩. -/
theorem source_actor_amalgam_quotient_core (d : Counterexample T L)
    (chosen : ChosenModule T L V) (F : InvariantFlag T V 3) (e a : G)
    (he : orderOf e = 2) (heI : e ∈ Chapter12.Section08.centerIn (F.I₂ L))
    (heT : e ∈ sylowOmega T) (heU : e ∈ F.ZU)
    (ha : a ∈ centralizer (F.ZU : Set G)) :
    pCore 2 (AmalgamQuotient F L (conjugateSpanBy (zpowers a) F.H)) = ⊥ :=
  source_amalgam_quotient_core d chosen F _ e he heI heT heU
    (actor_span_centralizes F a ha)

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
