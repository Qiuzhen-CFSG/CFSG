module

public import Theory.SpecificGroups.LieType.TheoremDRootNormalizer.CorootTorus
public import Theory.GroupTheory.QuasithinBasic
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-!
# Actual projective root normalizers

The coroot torus acts on each root subgroup after the literal center quotient.
A positive simple-root subgroup survives that quotient over every finite binary
field larger than two: centrality would force invariance under a nontrivial
squared coroot character. It is consequently a nontrivial two-subgroup.
Conversely, a central torus element has trivial character on every simple root.
These facts supply the quotient and normalization steps of the direct
Aschbacher–Smith A.2.18 torus obstruction (printed p.40).
-/

@[expose] public section

open RootPairing.IntegralGeckConstruction
noncomputable section
namespace ExceptionalSplit.TheoremDRootNormalizer
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]
  {F : Type*} [Field F] [Finite F] [CharP F 2]

def projectiveTorus : (b.support → Fˣ) →* Model P b F :=
  (projection P b F).comp elementaryTorus

theorem rootScale_eq_one_of_projectiveTorus_eq_one {u : b.support → Fˣ}
    (hu : projectiveTorus (P := P) u = 1) (i : b.support) :
    integralChevalleyRootScale (P := P) u i = 1 := by
  have hc : elementaryTorus (P := P) u ∈ Subgroup.center (rootGenerated P b F) :=
    (projection_eq_one_iff P b F _).mp hu
  have hcomm := Subgroup.mem_center_iff.mp hc (elementaryRoot P b F i 1)
  have he : (elementaryTorus (P := P) u)⁻¹ * elementaryRoot P b F i 1 *
      elementaryTorus (P := P) u = elementaryRoot P b F i 1 := by
    rw [mul_assoc, hcomm, inv_mul_cancel_left]
  rw [elementaryTorus_conjugation, mul_one] at he
  exact Units.ext (elementaryRoot_simple_injective i he)

def projectiveRootHom (r : ι) : Multiplicative F →* Model P b F where
  toFun x := rootElement P b F r x.toAdd
  map_one' := rootElement_zero P b F r
  map_mul' x y := rootElement_add P b F r x.toAdd y.toAdd

def rootSubgroup (r : ι) : Subgroup (Model P b F) :=
  (projectiveRootHom (b := b) (F := F) r).range

omit [Finite F] in
theorem rootSubgroup_isTwoGroup (r : ι) : IsPGroup 2 (rootSubgroup (b := b) (F := F) r) := by
  have h : IsPGroup 2 (Multiplicative F) := by
    intro x
    refine ⟨1, ?_⟩
    change (2 ^ 1 : ℕ) • x.toAdd = 0
    rw [pow_one, nsmul_eq_mul, CharP.cast_eq_zero F 2, zero_mul]
  exact h.of_surjective (projectiveRootHom (b := b) (F := F) r).rangeRestrict
    (projectiveRootHom (b := b) (F := F) r).rangeRestrict_surjective

private theorem exists_unit_square_ne_one (hq : 2 < Nat.card F) :
    ∃ u : Fˣ, (u : F) ^ 2 ≠ 1 := by
  have hcard : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨u, hu⟩ := exists_ne (1 : Fˣ)
  refine ⟨u, fun h => hu (Units.ext ?_)⟩
  apply (frobenius_inj F 2)
  change (u : F) ^ 2 = (1 : F) ^ 2
  simpa only [one_pow] using h

theorem projectiveRootHom_simple_injective (hq : 2 < Nat.card F) (i : b.support) :
    Function.Injective (projectiveRootHom (b := b) (F := F) i) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hc : elementaryRoot P b F i x.toAdd ∈ Subgroup.center (rootGenerated P b F) :=
    (projection_eq_one_iff P b F _).mp hx
  obtain ⟨u, hu⟩ := exists_unit_square_ne_one hq
  let v := integralChevalleySimpleCorootParameter i u
  have hcomm := Subgroup.mem_center_iff.mp hc (elementaryTorus (P := P) v)
  have he : (elementaryTorus (P := P) v)⁻¹ * elementaryRoot P b F i x.toAdd *
      elementaryTorus (P := P) v = elementaryRoot P b F i x.toAdd := by
    rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
  rw [elementaryTorus_conjugation] at he
  have hf := elementaryRoot_simple_injective i he
  have hf' : ((u : F) ^ 2 - 1) * x.toAdd = 0 := by
    simpa [v, sub_mul] using sub_eq_zero.mpr hf
  have hx0 := (mul_eq_zero.mp hf').resolve_left (sub_ne_zero.mpr hu)
  exact congrArg Multiplicative.ofAdd hx0

theorem rootNormalizer_isTwoLocal (hq : 2 < Nat.card F) (i : b.support) :
    IsTwoLocal (Subgroup.normalizer (rootSubgroup (b := b) (F := F) i : Set (Model P b F))) := by
  refine ⟨rootSubgroup i, ?_, rootSubgroup_isTwoGroup (b := b) (F := F) i, rfl⟩
  intro h
  have hx : projectiveRootHom (b := b) i (Multiplicative.ofAdd (1 : F)) = 1 := by
    have hm : projectiveRootHom (b := b) i (Multiplicative.ofAdd (1 : F)) ∈
        rootSubgroup (b := b) i := ⟨_, rfl⟩
    simpa [h] using hm
  have hi := projectiveRootHom_simple_injective hq i (hx.trans (map_one _).symm)
  exact one_ne_zero (congrArg Multiplicative.toAdd hi)

theorem projectiveTorus_conjugation (u : b.support → Fˣ) (r : ι) (t : F) :
    (projectiveTorus (P := P) u)⁻¹ * rootElement P b F r t *
        projectiveTorus (P := P) u =
      rootElement P b F r ((integralChevalleyRootScale (P := P) u r : F) * t) := by
  exact congrArg (projection P b F) (elementaryTorus_conjugation u r t)

theorem projectiveTorus_mem_normalizer (u : b.support → Fˣ) (r : ι) :
    projectiveTorus (P := P) u ∈ Subgroup.normalizer
      (rootSubgroup (b := b) (F := F) r : Set (Model P b F)) := by
  have hf (u : b.support → Fˣ) (g : Model P b F) (hg : g ∈ rootSubgroup (b := b) r) :
      (projectiveTorus (P := P) u)⁻¹ * g * projectiveTorus (P := P) u ∈
        rootSubgroup (b := b) r := by
    obtain ⟨x, rfl⟩ := hg
    change (projectiveTorus u)⁻¹ * rootElement P b F r x.toAdd * projectiveTorus u ∈ _
    rw [projectiveTorus_conjugation]
    exact ⟨Multiplicative.ofAdd _, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    simpa only [map_inv, inv_inv] using hf u⁻¹ g hg
  · intro hg
    simpa only [inv_mul_cancel_left, mul_assoc, mul_inv_cancel, inv_mul_cancel, mul_one] using hf u _ hg

def torusNormalizer (r : ι) : (b.support → Fˣ) →*
    Subgroup.normalizer (rootSubgroup (b := b) (F := F) r : Set (Model P b F)) :=
  projectiveTorus.codRestrict _ (fun u => projectiveTorus_mem_normalizer u r)

end ExceptionalSplit.TheoremDRootNormalizer
