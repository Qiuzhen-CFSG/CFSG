module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.Preparation
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.Reduced

/-!
# The reduced test module in the faithful-family argument

Set ZL = Z(LT) ∩ U and VH = ⟨ZL^H⟩. The full action moves the marked
point, so V₁ ∩ Z(LT) is trivial. The original square bound then makes
ZL elementary abelian. It is central in T and lies in Z(U). Applying
B.2.14 inside the actual H proves VH ∈ R₂(H), retaining VH ≤ Z(U).

This proves the module preparation at the start of 14.3.25. The
subsequent faithful-component and solvable-module exclusions are still
needed to prove ZL = 1; reducedness alone does not prove that assertion.

Source: Aschbacher--Smith, 14.3.25, printed p.1001; 12.8.4(2), p.850.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- ZL in the initial contrary branch of 14.3.25. -/
def centralLTSeed (F : InvariantFlag T V 3) (L : Subgroup G) : Subgroup G :=
  Chapter12.Section08.centerIn (L ⊔ (T : Subgroup G)) ⊓ F.U

/-- The actual H-orbit module VH of that central seed. -/
def faithfulTestModule (F : InvariantFlag T V 3) (L : Subgroup G) : Subgroup G :=
  conjugateSpanBy (centralLTSeed F L) F.H

omit [Finite G] in
private theorem centerIn_commutes {A : Subgroup G} {x y : G}
    (hx : x ∈ Chapter12.Section08.centerIn A) (hy : y ∈ A) : y * x = x * y := by
  obtain ⟨z, hz, rfl⟩ := hx
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)

theorem source_point_inf_centerLT (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) :
    F.Vi 1 ⊓ Chapter12.Section08.centerIn (L ⊔ (T : Subgroup G)) = ⊥ := by
  let := chosen.elementary
  obtain ⟨g, hgP, hgH⟩ := source_conjugator d earlier hq chosen structural F
  apply le_bot_iff.mp
  rintro x ⟨hp, hxZ⟩
  change x = 1
  by_contra hx
  have ho : orderOf x = 2 := orderOf_eq_prime_iff.mpr
    ⟨elemPow_eq_one_of_isElementaryAbelian x (F.le_seed 1 hp), hx⟩
  have he : zpowers x = F.Vi 1 := eq_of_le_of_card_ge (zpowers_le.mpr hp) (by
    rw [Nat.card_zpowers, ho]
    simpa using (F.card 1 (by decide)).le)
  have hgc : g ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr (centerIn_commutes hxZ hgP.1)
  have hgc' : g ∈ centralizer (zpowers x : Set G) := by
    simpa only [zpowers_eq_closure, centralizer_closure] using hgc
  apply hgH
  change g ∈ normalizer (F.Vi 1 : Set G)
  rw [← he]
  exact Subgroup.centralizer_le_normalizer _ hgc'

theorem source_centralLT_seed (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) :
    IsElementaryAbelian 2 (centralLTSeed F L) ∧ centralLTSeed F L ≤ F.ZU ∧
      L ⊔ (T : Subgroup G) ≤ normalizer (centralLTSeed F L : Set G) := by
  let h := higherRankHypothesis d earlier hq chosen
  let := chosen.elementary
  have hUT := source_closure_le_sylow d earlier hq chosen structural alternatives F
  have hZC : centralLTSeed F L ≤ centralizer ((L ⊔ (T : Subgroup G) : Subgroup G) : Set G) := by
    intro x hx y hy
    exact centerIn_commutes hx.1 hy
  let : IsMulCommutative (centralLTSeed F L) := le_centralizer_iff_isMulCommutative.mp
    (hZC.trans (centralizer_le (inf_le_right.trans (hUT.trans le_sup_right))))
  obtain ⟨_, hsquare⟩ := F.localKernel_commutator_squares d.qtke L
    (normalizer (L : Set G)) (by decide) chosen.le_sylow chosen.normalizes
    (h.sylow_normalizes structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape F alternatives)
  have hs : IsElementaryAbelian 2 (centralLTSeed F L) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
      apply Subtype.ext
      have hm : (x : G) ^ 2 ∈ F.Vi 1 ⊓
          Chapter12.Section08.centerIn (L ⊔ (T : Subgroup G)) :=
        ⟨hsquare x x.property.2, pow_mem x.property.1 2⟩
      rwa [source_point_inf_centerLT d earlier hq chosen structural F, mem_bot] at hm }
  have hZU : centralLTSeed F L ≤ F.ZU := by
    intro x hx
    refine ⟨⟨x, hx.2⟩, mem_center_iff.mpr ?_, rfl⟩
    intro y
    exact Subtype.ext (hZC hx y (mem_sup_right (hUT y.property)))
  exact ⟨hs, hZU, (le_centralizer_iff.mp hZC).trans (Subgroup.centralizer_le_normalizer _)⟩

/-- Construct the reduced H-module used to force faithful local membership. -/
theorem source_faithful_test_reduced (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) :
    faithfulTestModule F L ≤ F.ZU ∧
      IsPReduced 2 ((faithfulTestModule F L).subgroupOf F.H) := by
  obtain ⟨hs, hZ, _⟩ := source_centralLT_seed d earlier hq chosen structural alternatives F
  let := hs
  have hUT := source_closure_le_sylow d earlier hq chosen structural alternatives F
  have hZC : centralLTSeed F L ≤ centralizer (T : Set G) := by
    intro x hx t ht
    exact centerIn_commutes hx.1 (mem_sup_right ht)
  refine ⟨conjugateSpanBy_le hZ ((le_normalizer_conjugateSpanBy V F.H).trans
    (normalizer_le_normalizer_characteristic_image F.U (center F.U))), ?_⟩
  let h := higherRankHypothesis d earlier hq chosen
  exact reduced_conjugateSpan_of_sylow_central T F.H (centralLTSeed F L)
    (F.invariant 1) (inf_le_right.trans hUT) hZC
    (F.localKernel_characteristicTwo d.qtke L (normalizer (L : Set G)) F.H
      (h.point_mem_Hz F alternatives))

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
