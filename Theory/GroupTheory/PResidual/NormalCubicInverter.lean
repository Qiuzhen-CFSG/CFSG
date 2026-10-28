module
public import Theory.GroupTheory.PResidual.NormalCubicLines

/-!
# Inverters on a normal cubic quotient image

Let Y be a normal cubic residual in X, and let S normalize X and Y.
If [Y,S] is not a two-group, some element of S inverts the image of Y
in the literal quotient X/O₂(X). Indeed, an automorphism of that cubic
image is either the identity or inversion. If every actor fixes it,
all commutators lie in the embedded O₂(X), a contradiction.

Relative normality supplies the cubic image through the core-intersection
comparison in `NormalCubicLines`; no image-injectivity assertion is made
for arbitrary subgroups. Source application: Aschbacher–Smith, proof of
12.4.6, printed p.814, the actor in T∩L on the moving residual line.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A non-two commutator subgroup forces inversion on the literal cubic image. -/
theorem exists_normalCubic_inverter_of_commutator_not_two
    (X Y S : Subgroup G) (hY : Y ∈ normalCubicResiduals X)
    (hSX : S ≤ normalizer (X : Set G)) (hSY : S ≤ normalizer (Y : Set G))
    (hcomm : ¬ IsPGroup 2 (⁅Y, S⁆ : Subgroup G)) :
    ∃ t : S, ∀ z ∈ normalCubicResidualImage X Y,
      normalCubicQuotientAction X ⟨t, hSX t.property⟩ z = z⁻¹ := by
  classical
  let C := normalCubicResidualImage X Y
  have hC : Nat.card C = 3 := normalCubicResidualImage_card hY
  by_contra hn
  have hfix (t : S) : ∀ z ∈ C,
      normalCubicQuotientAction X ⟨t, hSX t.property⟩ z = z := by
    let a := normalCubicQuotientAction X ⟨t, hSX t.property⟩
    have he : C.map a.toMonoidHom = C := by
      rw [← normalCubicResidualImage_conjugate X Y hY.1]
      exact congrArg (normalCubicResidualImage X)
        (mem_normalizer_iff_map_conj_eq.mp (hSY t.property))
    let b : MulAut C := (a.subgroupMap C).trans (MulEquiv.subgroupCongr he)
    rcases CubicAutomorphismLines.automorphism_eq_one_or_inv hC b with hb | hb
    · intro z hz
      have hh := congrArg (fun f : MulAut C => (f ⟨z, hz⟩ : X ⧸ pCore 2 X)) hb
      exact hh
    · exact False.elim (hn ⟨t, fun z hz => congrArg Subtype.val (hb ⟨z, hz⟩)⟩)
  apply hcomm
  have hle : ⁅Y, S⁆ ≤ (pCore 2 X).map X.subtype := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro t ht y hy
    let a : normalizer (X : Set G) := ⟨t, hSX ht⟩
    let yX : X := ⟨y, hY.1 hy⟩
    let q := QuotientGroup.mk' (pCore 2 X)
    have hh := hfix ⟨t, ht⟩ (q yX) (mem_map.mpr ⟨yX, hy, rfl⟩)
    change quotientAut (pCore 2 X) (X.normalizerMonoidHom a) (q yX) = q yX at hh
    rw [quotientAut_apply_mk] at hh
    have hk : X.normalizerMonoidHom a yX * yX⁻¹ ∈ pCore 2 X := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (X.normalizerMonoidHom a yX * yX⁻¹) = 1
      rw [map_mul, map_inv, hh, mul_inv_cancel]
    exact mem_map.mpr ⟨_, hk, rfl⟩
  exact (pCore_isPGroup.map X.subtype).to_le hle
end Subgroup
