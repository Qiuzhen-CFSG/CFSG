module
public import Theory.Representation.SL2FourQuadraticRecognition.QuotientMap
public import Theory.Representation.SL2FourNaturalOrbits.SelfDual
public import Theory.Representation.BinaryOffender.TwoNoncentralLayers
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.LinearAlgebra.QuadraticRankOneDisplacement
/-!
# Fixed indices and moved kernels of the natural fixed quotient

An arbitrary binary module whose global fixed quotient is the natural SL₂(4)
module retains arbitrary fixed attachments. Every subgroup with nontrivial
image moves at least two binary dimensions. A subgroup with full image has
the original global fixed space, fixed index sixteen, and the original global
moved span. Restriction to that literal moved span preserves the exact action
kernel.

Nonidentity natural matrices have positive even binary displacement rank,
by restriction of scalars from F₄. The natural module is fully moved, so the
original moved span surjects onto it; natural faithfulness then detects the
original kernel. The final consumer obtains its coordinates from quadratic
Sylow recognition, discharging the natural-module premise internally.

Source: Niles, “Pushing-up in finite groups” (1979), Lemmas 2.8–2.9 and
Sections 4 and 7, especially the fixed-index and centralizer calculations
in 7.4 and 7.6. The literal group-conjugation transport is a separate adapter.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open SL2FourNatural SL2FourNatural.ProjectiveRecognition
namespace Representation.SL2FourQuadraticRecognition


private theorem natural_displacement_lower (g : SL) (hg : g ≠ 1) :
    2 ≤ fixedCodim naturalRepresentation (zpowers g) := by
  rw [fixedCodim_zpowers_eq_displacement_rank]
  have he : Module.finrank (ZMod 2) (LinearMap.range (naturalRepresentation g - LinearMap.id)) =
      2 * Module.finrank F (LinearMap.range
        ((Matrix.SpecialLinearGroup.toLin' g).toLinearMap - LinearMap.id)) := by
    exact (QuadraticForm.displacement_rank_restrictScalars (k := ZMod 2)
      (Matrix.SpecialLinearGroup.toLin' g)).trans (by rw [QuadraticAlgebra.finrank_eq_two])
  have hn : Module.finrank (ZMod 2) (LinearMap.range (naturalRepresentation g - LinearMap.id)) ≠ 0 := by
    intro hz
    have hh := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)
    have hg' : SL2FourNatural.action g = 1 := by
      apply LinearEquiv.ext
      intro v
      exact LinearMap.congr_fun (sub_eq_zero.mp hh) v
    apply hg
    apply SL2FourNatural.action_faithful
    simpa only [map_one] using hg'
  omega

private theorem natural_fixedCodim_lower (A : Subgroup SL) (hA : A ≠ ⊥) :
    2 ≤ fixedCodim naturalRepresentation A := by
  obtain ⟨a, ha⟩ := ne_bot_iff_exists_ne_one.mp hA
  have hn : (a : SL) ≠ 1 := fun h => ha (Subtype.ext h)
  have h := natural_displacement_lower a hn
  have hi := Submodule.finrank_mono (fixedSpace_antitone naturalRepresentation
    (zpowers_le.mpr a.property))
  have h1 := fixedCodim_add_finrank naturalRepresentation A
  have h2 := fixedCodim_add_finrank naturalRepresentation (zpowers (a : SL))
  omega

variable {H M : Type*} [Group H] [AddCommGroup M] [Module (ZMod 2) M]

/-- Every nontrivial natural quotient image moves at least two binary dimensions,
even when the original module has arbitrary fixed attachments. -/
theorem fixedCodim_lower_of_natural_quotient [FiniteDimensional (ZMod 2) M]
    (ρ : Representation (ZMod 2) H M) (q : H →* SL)
    (e : (M ⧸ fixedSpace ρ ⊤) ≃ₗ[ZMod 2] SL2FourNatural.V)
    (he : ∀ h v, e (fixedQuotient ρ ⊤ h v) = specialLinearNatural 2 (q h) (e v))
    (A : Subgroup H) (hA : A.map q ≠ ⊥) : 2 ≤ fixedCodim ρ A := by
  let f := e.toLinearMap.comp (fixedSpace ρ ⊤).mkQ
  have hf : Function.Surjective f := e.surjective.comp (fixedSpace ρ ⊤).mkQ_surjective
  have hfe (h : H) (v : M) : f (ρ h v) = (naturalRepresentation.comp q) h (f v) :=
    he h ((fixedSpace ρ ⊤).mkQ v)
  have hle := fixedCodim_le_of_equivariant_surjection ρ (naturalRepresentation.comp q) f hf hfe A
  have heq := fixedCodim_map_equivariant (naturalRepresentation.comp q) naturalRepresentation q
    (LinearEquiv.refl _ _) (fun _ _ => rfl) A
  rw [heq] at hle
  exact (natural_fixedCodim_lower _ hA).trans hle

/-- The additive fixed index is at least four whenever the natural image is nontrivial. -/
theorem fixedIndex_lower_of_natural_quotient [FiniteDimensional (ZMod 2) M]
    (ρ : Representation (ZMod 2) H M) (q : H →* SL)
    (e : (M ⧸ fixedSpace ρ ⊤) ≃ₗ[ZMod 2] SL2FourNatural.V)
    (he : ∀ h v, e (fixedQuotient ρ ⊤ h v) = specialLinearNatural 2 (q h) (e v))
    (A : Subgroup H) (hA : A.map q ≠ ⊥) :
    4 ≤ Nat.card (M ⧸ fixedSpace ρ A) := by
  have hd := fixedCodim_lower_of_natural_quotient ρ q e he A hA
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact (show 2 ^ 2 ≤ 2 ^ fixedCodim ρ A from Nat.pow_le_pow_right (by decide) hd)

/-- A subgroup surjecting onto the action quotient has exactly the original global fixed space. -/
theorem fixedSpace_eq_of_surjective_image
    (ρ : Representation (ZMod 2) H M) (q : H →* SL) (hk : q.ker ≤ ρ.ker)
    (L : Subgroup H) (hL : L.map q = ⊤) : fixedSpace ρ L = fixedSpace ρ ⊤ := by
  apply le_antisymm ?_ (fixedSpace_antitone ρ le_top)
  intro v hv h
  obtain ⟨l, hl, he⟩ := (show q (h : H) ∈ L.map q from hL.symm ▸ mem_top _)
  have hr : ρ l = ρ h := (ρ.eq_iff).mpr (hk ((q.eq_iff).mp he))
  exact (LinearMap.congr_fun hr v).symm.trans (hv ⟨l, hl⟩)

/-- The literal L-fixed quotient has dimension four for every subgroup with full image. -/
theorem fixedCodim_eq_four_of_natural_quotient
    (ρ : Representation (ZMod 2) H M) (q : H →* SL) (hk : q.ker ≤ ρ.ker)
    (e : (M ⧸ fixedSpace ρ ⊤) ≃ₗ[ZMod 2] SL2FourNatural.V)
    (L : Subgroup H) (hL : L.map q = ⊤) : fixedCodim ρ L = 4 := by
  unfold fixedCodim
  rw [fixedSpace_eq_of_surjective_image ρ q hk L hL, e.finrank_eq, finrank_vector]

/-- The literal L-fixed quotient has sixteen vectors for every subgroup with full image. -/
theorem fixedIndex_eq_sixteen_of_natural_quotient
    (ρ : Representation (ZMod 2) H M) (q : H →* SL) (hk : q.ker ≤ ρ.ker)
    (e : (M ⧸ fixedSpace ρ ⊤) ≃ₗ[ZMod 2] SL2FourNatural.V)
    (L : Subgroup H) (hL : L.map q = ⊤) : Nat.card (M ⧸ fixedSpace ρ L) = 16 := by
  rw [fixedSpace_eq_of_surjective_image ρ q hk L hL, Nat.card_congr e.toEquiv,
    Nat.card_eq_fintype_card, SL2FourNatural.card_vector]

private theorem natural_moved_top : subspaceCommutator naturalRepresentation ⊤ ⊤ = ⊤ := by
  apply top_unique
  intro v _
  let I := subspaceCommutator naturalRepresentation ⊤ ⊤
  have hx (x : F) : ![x, 0] ∈ I := by
    have h : naturalRepresentation (upper 1) ![0, x] - ![0, x] ∈ I :=
      Submodule.subset_span ⟨upper 1, mem_top _, ![0, x], Submodule.mem_top, rfl⟩
    convert h using 1
    funext i
    fin_cases i <;> simp [naturalRepresentation_apply, upper_action]
  have hy (y : F) : ![0, y] ∈ I := by
    have h := ((subspaceCommutator_invariant naturalRepresentation ⊤ ⊤) (mem_top weyl) ![y, 0]).2 (hx y)
    change specialLinearNatural 2 weyl ![y, 0] ∈ I at h
    rw [weyl_action] at h
    simpa using h
  have h := I.add_mem (hx (v 0)) (hy (v 1))
  convert h using 1
  funext i
  fin_cases i <;> simp

/-- Full image gives the literal global moved span, without a normality assumption on L. -/
theorem moved_eq_of_surjective_image
    (ρ : Representation (ZMod 2) H M) (q : H →* SL) (hk : q.ker ≤ ρ.ker)
    (L : Subgroup H) (hL : L.map q = ⊤) :
    subspaceCommutator ρ ⊤ L = subspaceCommutator ρ ⊤ ⊤ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨l, _, v, hv, rfl⟩
    exact Submodule.subset_span ⟨l, mem_top _, v, hv, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨h, _, v, hv, rfl⟩
    obtain ⟨l, hl, he⟩ := (show q h ∈ L.map q from hL.symm ▸ mem_top _)
    have hr : ρ l = ρ h := (ρ.eq_iff).mpr (hk ((q.eq_iff).mp he))
    rw [← hr]
    exact Submodule.subset_span ⟨l, hl, v, hv, rfl⟩

/-- The actual L-moved span is stable under the original ambient actor. -/
@[expose] noncomputable def movedSubrepresentation
    (ρ : Representation (ZMod 2) H M) (q : H →* SL) (hk : q.ker ≤ ρ.ker)
    (L : Subgroup H) (hL : L.map q = ⊤) : Subrepresentation ρ where
  toSubmodule := subspaceCommutator ρ ⊤ L
  apply_mem_toSubmodule g v hv := by
    rw [moved_eq_of_surjective_image ρ q hk L hL] at hv ⊢
    exact ((subspaceCommutator_invariant ρ ⊤ ⊤) (mem_top g) v).2 hv

/-- The original moved span surjects onto the entire natural fixed quotient. -/
theorem moved_map_eq_top_of_natural_quotient
    (ρ : Representation (ZMod 2) H M) (q : H →* SL)
    (e : (M ⧸ fixedSpace ρ ⊤) ≃ₗ[ZMod 2] SL2FourNatural.V)
    (he : ∀ h v, e (fixedQuotient ρ ⊤ h v) = specialLinearNatural 2 (q h) (e v))
    (L : Subgroup H) (hL : L.map q = ⊤) :
    (subspaceCommutator ρ ⊤ L).map (e.toLinearMap.comp (fixedSpace ρ ⊤).mkQ) = ⊤ := by
  have hh := map_moved_of_surjective_intertwining ρ (naturalRepresentation.comp q) L
    (e.toLinearMap.comp (fixedSpace ρ ⊤).mkQ)
    (e.surjective.comp (fixedSpace ρ ⊤).mkQ_surjective)
    (fun l v => he l ((fixedSpace ρ ⊤).mkQ v))
  rw [subspaceCommutator_comp_map, hL, natural_moved_top] at hh
  exact hh

/-- Fixing the literal moved span is equivalent to fixing the whole original module. -/
theorem fixes_moved_iff_of_natural_quotient
    (ρ : Representation (ZMod 2) H M) (q : H →* SL) (hk : q.ker ≤ ρ.ker)
    (e : (M ⧸ fixedSpace ρ ⊤) ≃ₗ[ZMod 2] SL2FourNatural.V)
    (he : ∀ h v, e (fixedQuotient ρ ⊤ h v) = specialLinearNatural 2 (q h) (e v))
    (L : Subgroup H) (hL : L.map q = ⊤) (h : H) :
    (∀ v ∈ subspaceCommutator ρ ⊤ L, ρ h v = v) ↔ h ∈ ρ.ker := by
  constructor
  · intro hh
    apply hk
    apply SL2FourNatural.action_faithful
    apply LinearEquiv.ext
    intro w
    let f := e.toLinearMap.comp (fixedSpace ρ ⊤).mkQ
    have htop : (subspaceCommutator ρ ⊤ L).map f = ⊤ :=
      moved_map_eq_top_of_natural_quotient ρ q e he L hL
    obtain ⟨v, hv, rfl⟩ := (show w ∈ (subspaceCommutator ρ ⊤ L).map f from
      htop.symm ▸ Submodule.mem_top)
    rw [map_one]
    change specialLinearNatural 2 (q h) (e ((fixedSpace ρ ⊤).mkQ v)) =
      e ((fixedSpace ρ ⊤).mkQ v)
    calc
      _ = e (fixedQuotient ρ ⊤ h ((fixedSpace ρ ⊤).mkQ v)) :=
        (he h ((fixedSpace ρ ⊤).mkQ v)).symm
      _ = e ((fixedSpace ρ ⊤).mkQ v) := by
        change e ((fixedSpace ρ ⊤).mkQ (ρ h v)) = e ((fixedSpace ρ ⊤).mkQ v)
        rw [hh v hv]
  · intro hh v _
    exact LinearMap.congr_fun hh v

/-- Restriction to the actual moved subrepresentation preserves the exact action kernel. -/
theorem movedSubrepresentation_ker_eq
    (ρ : Representation (ZMod 2) H M) (q : H →* SL) (hk : q.ker ≤ ρ.ker)
    (e : (M ⧸ fixedSpace ρ ⊤) ≃ₗ[ZMod 2] SL2FourNatural.V)
    (he : ∀ h v, e (fixedQuotient ρ ⊤ h v) = specialLinearNatural 2 (q h) (e v))
    (L : Subgroup H) (hL : L.map q = ⊤) :
    (movedSubrepresentation ρ q hk L hL).toRepresentation.ker = ρ.ker := by
  ext h
  rw [← fixes_moved_iff_of_natural_quotient ρ q hk e he L hL h]
  constructor
  · intro hh v hv
    exact congrArg Subtype.val (LinearMap.congr_fun hh ⟨v, hv⟩)
  · intro hh
    apply LinearMap.ext
    intro v
    exact Subtype.ext (hh v v.property)


/-- The quadratic Sylow recognition theorem discharges all coordinate premises
in the fixed-index and moved-kernel consequences used in Niles 7.4 and 7.6. -/
theorem natural_consequences_of_sylow [Finite H] [FiniteDimensional (ZMod 2) M]
    (ρ : Representation (ZMod 2) H M) (q : H →* SL)
    (hs : Function.Surjective q) (hk : q.ker ≤ ρ.ker)
    (hn : ρ ≠ 1) (S : Sylow 2 H)
    (hq : IsQuadratic ρ (S : Subgroup H))
    (hd : fixedCodim ρ (S : Subgroup H) ≤ 2) :
    (∀ A : Subgroup H, A.map q ≠ ⊥ →
      2 ≤ fixedCodim ρ A ∧ 4 ≤ Nat.card (M ⧸ fixedSpace ρ A)) ∧
    ∀ (L : Subgroup H) (hL : L.map q = ⊤),
      fixedSpace ρ L = fixedSpace ρ ⊤ ∧ fixedCodim ρ L = 4 ∧
      Nat.card (M ⧸ fixedSpace ρ L) = 16 ∧
      (movedSubrepresentation ρ q hk L hL).toRepresentation.ker = ρ.ker ∧
      ∀ h : H, (∀ v ∈ subspaceCommutator ρ ⊤ L, ρ h v = v) ↔ h ∈ ρ.ker := by
  obtain ⟨e, he⟩ := natural_fixed_quotient_of_sylow ρ q hs hk hn S hq hd
  constructor
  · intro A hA
    exact ⟨fixedCodim_lower_of_natural_quotient ρ q e he A hA,
      fixedIndex_lower_of_natural_quotient ρ q e he A hA⟩
  · intro L hL
    exact ⟨fixedSpace_eq_of_surjective_image ρ q hk L hL,
      fixedCodim_eq_four_of_natural_quotient ρ q hk e L hL,
      fixedIndex_eq_sixteen_of_natural_quotient ρ q hk e L hL,
      movedSubrepresentation_ker_eq ρ q hk e he L hL,
      fixes_moved_iff_of_natural_quotient ρ q hk e he L hL⟩

end Representation.SL2FourQuadraticRecognition
