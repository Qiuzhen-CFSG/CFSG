module

public import Theory.AtlasPort.LinearGroups.G2.ShortRootFieldWitness
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.AutomorphismDescription
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.FieldDegree
public import Theory.GroupTheory.DoubleCoverCentralizer.DisplacementTransport

/-!
# Non-two-central displacements for coefficient actions on G₂(4)

For a nonidentity automorphism σ of a four-element field, some parameter a
has a + σ(a) = 1. On the actual octonion short-root group this gives
C(a) σ(C(a))⁻¹ = C(1). The checked root geometry proves that C(1) is an
involution outside the center of every Sylow two-subgroup.

The last theorem uses the proved full inner-field automorphism description
and transports this witness through a specified solution of each involutory
G₂ cocycle. Constructing that solution remains an independent premise;
this module does not assert exhaustive outer-involution coverage without it.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, I.2.2,
observation (iii), printed p.411 / PDF p.422. The imported octonion formulas
retain their ATLAS attribution in LICENSES/ATLAS.txt and ATLAS-CITATION.cff.
-/

public section
namespace Theory.SpecificGroups.ExceptionalOuterDisplacements.G2
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
open Atlas.G2 Atlas.G2.LieAutomorphismExtensions

private theorem trace_four {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hc : Nat.card F = 4) (σ : F ≃+* F) (hσ : σ ≠ 1) :
    ∃ a : F, a + σ a = 1 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨a, ha⟩ : ∃ a : F, σ a ≠ a := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  have ha0 : a ≠ 0 := by rintro rfl; exact ha (map_zero σ)
  have ha1 : a ≠ 1 := by rintro rfl; exact ha (map_one σ)
  have ha10 : a + 1 ≠ 0 := by
    intro h
    apply ha1
    have := congrArg (fun x : F => x + 1) h
    simpa [add_assoc, CharTwo.add_self_eq_zero] using this
  have ha11 : a + 1 ≠ 1 := by simpa using ha0
  have haa1 : a ≠ a + 1 := by simp
  have hs : ({0, 1, a, a + 1} : Finset F) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← Nat.card_eq_fintype_card, hc]
    simp [haa1, Ne.symm ha0, Ne.symm ha1,
      Ne.symm ha10, Ne.symm ha11]
  have hm : σ a ∈ ({0, 1, a, a + 1} : Finset F) := hs ▸ Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hz | ho | he | he
  · exact (ha0 (σ.injective (hz.trans (map_zero σ).symm))).elim
  · exact (ha1 (σ.injective (ho.trans (map_one σ).symm))).elim
  · exact (ha he).elim
  · exact ⟨a, by rw [he, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]⟩

/-- A trace-one short-root parameter gives a non-two-central displacement. -/
theorem field_displacement {F : Type*} [Field F] [Finite F]
    (hc : Nat.card F = 4) (σ : F ≃+* F) (hσ : σ ≠ 1) :
    HasNonTwoCentralDisplacement (fieldAction σ) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (show Fintype.card F = 2 ^ 2 by simpa [Nat.card_eq_fintype_card] using hc)
  obtain ⟨a, ha⟩ := trace_four hc σ hσ
  have hd : rootC a * (fieldAction σ (rootC a))⁻¹ = rootC (1 : F) := by
    change rootC a * (fieldEquiv σ (rootC a))⁻¹ = _
    rw [ShortRootFieldWitness.fieldEquiv_rootC]
    have hi : (rootC (σ a))⁻¹ = rootC (σ a) := by
      apply inv_eq_of_mul_eq_one_left
      rw [rootC_add, CharTwo.add_self_eq_zero, rootC_zero]
    rw [hi, rootC_add, ha]
  have ho : orderOf (rootC (1 : F)) = 2 :=
    ShortRootProducts.shortRoot_order ⟨1, one_ne_zero, 1, by simp⟩
  refine ⟨rootC a, hd.symm ▸ ho, ?_⟩
  rw [hd]
  rintro ⟨P, hm, hz⟩
  apply ShortRootFieldWitness.rootC_one_not_twoCentral (F := F)
  refine ⟨ho, P, hm, ?_⟩
  intro x hx
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_center_iff.mp hz ⟨x, hx⟩))

/-- The actual inner-field description and a cocycle solver cover every outer
involution. The solver is the remaining independent G₂ descent input. -/
theorem outer_displacement_of_cocycle_solver {F : Type*} [Field F] [Finite F]
    (hc : Nat.card F = 4)
    (hsolve : ∀ (σ : F ≃+* F), orderOf σ = 2 → ∀ g : Model F,
      g * fieldAction σ g = 1 → ∃ c : Model F, g = c * fieldAction σ c⁻¹)
    (b : MulAut (Model F)) (hb : orderOf b = 2)
    (ho : ¬ ∃ s : Model F, b = MulAut.conj s) :
    HasNonTwoCentralDisplacement b := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (show Fintype.card F = 2 ^ 2 by simpa [Nat.card_eq_fintype_card] using hc)
  have hq : 2 < Nat.card F := by omega
  obtain ⟨g, σ, he⟩ := exists_inner_field hq b
  obtain ⟨hs, hg⟩ := EvenFieldFixedResidual.coefficient_involution_and_cocycle
    hq b (hb ▸ pow_orderOf_eq_one b) g σ he (fun s hs => ho ⟨s, hs⟩)
  obtain ⟨c, hc'⟩ := hsolve σ hs g hg
  have he' : b = MulAut.congr (MulAut.conj c) (fieldAction σ) := by
    rw [he, hc']
    apply MulEquiv.ext
    intro x
    change (c * fieldAction σ c⁻¹) * fieldAction σ x * (c * fieldAction σ c⁻¹)⁻¹ =
      c * fieldAction σ (c⁻¹ * x * c) * c⁻¹
    simp only [map_mul, map_inv]
    group
  rw [he']
  apply HasNonTwoCentralDisplacement.map
  exact field_displacement hc σ (by intro h; simp [h] at hs)

end Theory.SpecificGroups.ExceptionalOuterDisplacements.G2
