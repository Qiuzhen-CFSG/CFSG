module
public import Theory.SpecificGroups.SymplecticFour.SmallNaturalDisplacement

/-!
# The complete action of an actor with small fixed index

An actor with fixed index at most four on the natural Sp4(4)-module has
no field twist. Restriction to the symplectic component gives an actual
matrix marking with exactly the original action kernel. Symplectic duality
bounds the displacement dimension by one and the image order by four.
An alternating form vanishes on a line, so that displacement is fixed by
the actor. The entire group commutator has order one or four.

The actor need not be elementary or faithful. Its original graph application
is Sp4Four.SourceComparison.OriginalSmallAction; the tensor application is
GenerationTwoSymplecticStrictAction.
Source: MS93 (5.9), printed p.920, using the natural-module calculation of
(3.3), printed p.867.
-/

public noncomputable section
open Subgroup Representation
open Theory.SpecificGroups.SymplecticFour.TwoLocalCover
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F]

/-- Small fixed codimension gives a displacement line fixed by the entire
actor, without an elementary-abelian hypothesis. -/
theorem small_inner_displacement_structure
    (hF : Nat.card F = 4) (A : Subgroup (Sp F))
    (hsmall : Nat.card (Vector F ⧸ TwoLocalCover.fixedSpace A) ≤ 4) :
    Module.finrank F (displacementSpace A) ≤ 1 ∧ Nat.card A ≤ 4 ∧
      displacementSpace A ≤ TwoLocalCover.fixedSpace A := by
  have hd : Module.finrank F (displacementSpace A) ≤ 1 := by
    rw [fixed_quotient_card,hF] at hsmall
    by_contra hn
    have hh := Nat.pow_le_pow_right (by decide : 0 < 4)
      (show 2 ≤ Module.finrank F (displacementSpace A) by omega)
    omega
  have hc := card_actor_le_displacement_dimension A
  rw [hF] at hc
  refine ⟨hd,?_,?_⟩
  · calc
      Nat.card A ≤ 4 ^ (Module.finrank F (displacementSpace A))^2 := hc
      _ ≤ 4 ^ 1 := Nat.pow_le_pow_right (by decide) (by nlinarith)
      _ = 4 := by norm_num
  · rw [←orthogonal_displacementSpace]
    by_cases hz : displacementSpace A = ⊥
    · rw [hz]; exact bot_le
    have he : Module.finrank F (displacementSpace A) = 1 := by
      have hh : Module.finrank F (displacementSpace A) ≠ 0 :=
        fun h => hz (Submodule.finrank_eq_zero.mp h)
      omega
    obtain ⟨v,hv,hv0⟩ := (displacementSpace A).ne_bot_iff.mp hz
    have hs := eq_span_singleton_of_mem_of_finrank_eq_one he hv hv0
    intro x hx y hy
    rw [hs] at hx hy
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨d,rfl⟩ := Submodule.mem_span_singleton.mp hy
    change form F (d • v) (c • v) = 0
    simp [form_alternating v]

variable {G J : Type*} [Group G] [Group J] [Finite J]
  [CharP F 2] [Algebra (ZMod 2) F]

/-- The original action restricts to actual symplectic matrices, preserving
its whole kernel and identifying the full small group commutator. -/
theorem small_natural_actor_marking
    (hF : Nat.card F = 4) (B : Subgroup J) [B.Normal]
    (hcent : centralizer (B : Set J) ≤ B) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) J (Vector F))
    (hB : ∀ b : B, ∀ v, ρ (b:J) v = symplecticNatural 2 (e b) v)
    (N A : Subgroup G) (j : Multiplicative (Vector F) →* G)
    (hj : Function.Injective j) (hjr : j.range = N) (α : A →* J)
    (hact : ∀ (a : A) v,
      j (Multiplicative.ofAdd (ρ (α a) v)) = a.val*j (Multiplicative.ofAdd v)*a.val⁻¹)
    (hsmall : (centralizer (A : Set G)).relIndex N ≤ 4) :
    ∃ f : A →* Sp F, f.ker = α.ker ∧
      (∀ (a : A) v, j (Multiplicative.ofAdd (f a • v)) =
        a.val*j (Multiplicative.ofAdd v)*a.val⁻¹) ∧
      Module.finrank F (displacementSpace f.range) ≤ 1 ∧ Nat.card f.range ≤ 4 ∧
      (Nat.card (⁅A,N⁆ : Subgroup G) = 1 ∨ Nat.card (⁅A,N⁆ : Subgroup G) = 4) ∧
      ⁅A,N⁆ ≤ centralizer (A : Set G) := by
  have hi := BinaryOffender.embedded_centralizer_index ρ N A j hj hjr α hact
  have hquot : Nat.card (Vector F ⧸ BinaryOffender.fixedSpace ρ α.range) ≤ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact hi ▸ hsmall
  have hinner := small_actor_le_symplectic_component hF B hcent e ρ hB α.range hquot
  let f : A →* Sp F := e.toMonoidHom.comp (α.codRestrict B (fun a => hinner ⟨a,rfl⟩))
  have hact' (a : A) v : j (Multiplicative.ofAdd (f a • v)) =
      a.val*j (Multiplicative.ofAdd v)*a.val⁻¹ := by
    rw [←hact]
    congr 2
    exact (hB ⟨α a,hinner ⟨a,rfl⟩⟩ v).symm
  let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
  have hi' := BinaryOffender.embedded_centralizer_index σ N A j hj hjr f hact'
  have hquot' : 2 ^ BinaryOffender.fixedCodim σ f.range =
      Nat.card (Vector F ⧸ TwoLocalCover.fixedSpace f.range) := by
    let C := TwoLocalCover.fixedSpace f.range
    have hfixed : BinaryOffender.fixedSpace σ f.range = C.restrictScalars (ZMod 2) := by
      ext v
      exact ⟨fun h g hg => h ⟨g,hg⟩,fun h g => h g.val g.property⟩
    change 2 ^ Module.finrank (ZMod 2) (Vector F ⧸ BinaryOffender.fixedSpace σ f.range) = _
    rw [hfixed]
    have hc := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) C).toEquiv
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
    exact hc
  have hsmall' : Nat.card (Vector F ⧸ TwoLocalCover.fixedSpace f.range) ≤ 4 := by
    rw [hi',hquot'] at hsmall
    exact hsmall
  obtain ⟨hd,hc,hfixed⟩ := small_inner_displacement_structure hF f.range hsmall'
  have hcomm := RootHyperplaneComparison.commutator_eq_displacement_image A N j hjr f hact'
  refine ⟨f,?_,hact',hd,hc,?_,?_⟩
  · ext a
    change e ⟨α a,hinner ⟨a,rfl⟩⟩ = 1 ↔ α a = 1
    rw [map_eq_one_iff e e.injective]
    exact Subtype.ext_iff
  · have hcard : Nat.card (⁅A,N⁆ : Subgroup G) =
        4 ^ Module.finrank F (displacementSpace f.range) := by
      rw [hcomm,card_map_of_injective hj]
      change Nat.card (displacementSpace f.range) = _
      rw [Module.natCard_eq_pow_finrank (K := F),hF]
    interval_cases hh : Module.finrank F (displacementSpace f.range) <;> simp_all
  · rw [hcomm]
    rintro _ ⟨v,hv,rfl⟩ a ha
    have hh := hact' ⟨a,ha⟩ v.toAdd
    have hvf : f ⟨a,ha⟩ • v.toAdd = v.toAdd := hfixed hv (f ⟨a,ha⟩) ⟨_,rfl⟩
    rw [hvf,ofAdd_toAdd] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm)
end Theory.SpecificGroups.SymplecticFour
