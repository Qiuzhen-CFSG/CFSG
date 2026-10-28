module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityActionModelExclusions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The four-vector orbit of the canonical equality action

The actual linear intertwiner identifies U/⟨z⟩ with the two-dimensional
binary vector space. Its four vectors have a single nonzero orbit under
the full linear group. Lifting the actual actor quotient back to H gives
conjugation witnesses in H, and the literal quotient relation transfers
these witnesses to the quotient by the embedded center of P.

The natural-model and center premises in these helpers are discharged by
`EqualityActionPairAssembly`; they are not extra source assumptions.

Source: Aschbacher–Smith, Proposition 6.2.13, printed p.687 (PDF p.704).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open M22Recognition.CentralizerExtension

private theorem equality_linear_transitive {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : V ≃ₗ[ZMod 2] V, g x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V x hx
  let ey := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V y hy
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨g, ?_⟩
  have h := hg (ex 1)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ex, ey] using h.symm

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The natural model gives four quotient vectors and one nonzero orbit. -/
theorem LocalAnalysis.equality_quotient_four_orbit
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (hmodel : EqualityNaturalAction A h611 hz) :
    Nat.card (EqualityVectorQuotient (T : Subgroup G) L R z) = 4 ∧
      ∀ u v : EqualityVectorQuotient (T : Subgroup G) L R z, u ≠ 1 → v ≠ 1 →
        ∃ h : centralizer ({z} : Set G), equalityQuotientAction (T : Subgroup G) L R z h u = v := by
  let := A.sourceEqualityVectorQuotient_elementary h611 hz
  obtain ⟨ek, ev, stable, he⟩ := hmodel
  let e : Additive (EqualityVectorQuotient (T : Subgroup G) L R z) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    Submodule.topEquiv.symm.trans ev
  constructor
  · rw [Nat.card_congr (Additive.ofMul.trans e.toEquiv)]
    norm_num [Nat.card_fun]
  · intro u v hu hv
    let xu : (⊤ : Submodule (ZMod 2) (Additive (EqualityVectorQuotient (T : Subgroup G) L R z))) :=
      ⟨Additive.ofMul u, Submodule.mem_top⟩
    let xv : (⊤ : Submodule (ZMod 2) (Additive (EqualityVectorQuotient (T : Subgroup G) L R z))) :=
      ⟨Additive.ofMul v, Submodule.mem_top⟩
    have hx : ev xu ≠ 0 := by
      intro hh
      have h0 := ev.injective (hh.trans (map_zero ev).symm)
      have h1 := congrArg Subtype.val h0
      change Additive.ofMul u = 0 at h1
      exact hu (Additive.ofMul.injective h1)
    have hy : ev xv ≠ 0 := by
      intro hh
      have h0 := ev.injective (hh.trans (map_zero ev).symm)
      have h1 := congrArg Subtype.val h0
      change Additive.ofMul v = 0 at h1
      exact hv (Additive.ofMul.injective h1)
    obtain ⟨b, hb⟩ := equality_linear_transitive (ev xu) (ev xv) hx hy
    obtain ⟨k, hk⟩ := ek.surjective b
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective
      (pCore 2 (centralizer ({z} : Set G))) k.val
    refine ⟨h, ?_⟩
    have heq := he k xu
    change ev _ = ek k (ev xu) at heq
    rw [hk, hb] at heq
    have hvect := congrArg Subtype.val (ev.injective heq)
    change equalityRepresentation A k.val (Additive.ofMul u) = Additive.ofMul v at hvect
    rw [← hh, equalityRepresentation_mk] at hvect
    exact Additive.ofMul.injective hvect

/-- Transfer the literal quotient action to the embedded-center orbit contract. -/
theorem LocalAnalysis.equality_naturalFourOrbit_of_center
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (hmodel : EqualityNaturalAction A h611 hz)
    (hcenter : coreCenter (equalityCore L R z) = equalityLine z) :
    NaturalFourOrbit (equalityCore L R z) (equalityPlane (T : Subgroup G) L R z) := by
  obtain ⟨hcard, horbit⟩ := A.equality_quotient_four_orbit h611 hz hmodel
  constructor
  · rw [← relIndex_ker, QuotientGroup.ker_mk', hcenter, relIndex, index_eq_card]
    exact hcard
  · intro u hu v hv hun hvn
    have hu1 : QuotientGroup.mk' ((equalityLine z).subgroupOf
        (equalityClosure (T : Subgroup G) L R z)) ⟨u, hu⟩ ≠ 1 := by
      intro hh
      apply hun
      rw [hcenter]
      have hmem := (QuotientGroup.eq_one_iff (N := (equalityLine z).subgroupOf
        (equalityClosure (T : Subgroup G) L R z)) _).mp hh
      exact hmem
    have hv1 : QuotientGroup.mk' ((equalityLine z).subgroupOf
        (equalityClosure (T : Subgroup G) L R z)) ⟨v, hv⟩ ≠ 1 := by
      intro hh
      apply hvn
      rw [hcenter]
      have hmem := (QuotientGroup.eq_one_iff (N := (equalityLine z).subgroupOf
        (equalityClosure (T : Subgroup G) L R z)) _).mp hh
      exact hmem
    obtain ⟨h, he⟩ := horbit _ _ hu1 hv1
    refine ⟨h, QuotientGroup.eq_iff_div_mem.mpr ?_⟩
    rw [hcenter]
    rw [equalityQuotientAction_mk] at he
    have hh := QuotientGroup.eq_iff_div_mem.mp he
    exact hh

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
