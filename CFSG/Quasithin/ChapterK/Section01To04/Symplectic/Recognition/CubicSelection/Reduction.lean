module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.Catalogue
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.ActorBounds
public import Theory.Representation.SchurDisplacement

/-!
# Cubic support selection: degree gap and the Schur-moving branch

The actual periodic tensor parameters have binary degree below 16r only
for one factor repeated once or twice. An ambient cubic actor moving the
component Schur field displaces at least half of V, so the bound 6r+2 on
its fixed codimension gives degree at most 12r+4, strictly below 16r.
Consequently every unselected support has a genuine cubic actor all of
whose elements commute with the component endomorphism field.

This is a reduction, not the full support-selection theorem. The remaining
inner and outer Schur-linear actors require the parabolic and tensor fixed-
space estimates of GM04. No whole-module bound is inferred directly from
the small fixed-codimension actor, and no graph-descent premise is used.

Sources: Aschbacher--Smith, combined manuscript of 1 March 2004, K.3.4,
printed pp.451,456--457; Guralnick--Malle, Classification of 2F-modules II,
Proposition 6.2 and Table 9 (author manuscript pp.38--40,47), especially
§3.5 for the distinction between the Schur-linear and induced actions.
-/

public section

namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition
open Representation
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary

private theorem sixteen_mul_le_power {t b : ℕ} (ht : 0 < t) (hb : 16 ≤ b) :
    16 * t ≤ b ^ t := by
  induction t, ht using Nat.le_induction with
  | base => simpa using hb
  | succ t ht ih =>
    rw [pow_succ]
    have := Nat.mul_le_mul ih hb
    nlinarith

private theorem sixteen_mul_le_four_power {t : ℕ} (ht : 3 ≤ t) :
    16 * t ≤ 4 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; nlinarith

variable {F D V : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} [IsIrreducible ρ]
  {d : D ≃* Derived F} {r : ℕ}

/-- Below the next degree, the actual tensor parameters are precisely the two
possible K.3.4 support shapes. This does not assume a small-degree theorem. -/
theorem TensorParameters.selection_of_degree_lt (P : TensorParameters ρ d r)
    (hsmall : Module.finrank (ZMod 2) V < 16*r) :
    P.factors = 1 ∧ (P.blocks = 1 ∨ P.blocks = 2) := by
  have hd := P.binary_degree
  have hr := P.field_degree
  have ht := P.blocks_pos
  have ha := P.factors_pos
  have hfac : P.factors = 1 := by
    by_contra hne
    have hb : 16 ≤ 4 ^ P.factors := by
      have hh := Nat.pow_le_pow_right (by decide : 0 < 4) (by omega : 2 ≤ P.factors)
      exact hh
    have hh := Nat.mul_le_mul_left (Module.finrank (ZMod 2) (SchurField ρ))
      (sixteen_mul_le_power ht hb)
    nlinarith
  refine ⟨hfac, ?_⟩
  by_contra! hne
  have hh := Nat.mul_le_mul_left (Module.finrank (ZMod 2) (SchurField ρ))
    (sixteen_mul_le_four_power (by omega : 3 ≤ P.blocks))
  rw [hfac, pow_one] at hd
  nlinarith


section Ambient
open Representation.BinaryOffender

variable {G : Type*} [Group G] [Finite G]
  {ρG : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The Schur-moving branch for an actual ambient actor. Both numerical inputs
are fixed-codimension/rank bounds on A, not a whole-module degree assumption. -/
theorem selection_of_schur_moving_actor {K : GroupClass}
    (h : SourceHypothesis K ρG L) (hr : 1 < r)
    (d : L ≃* Derived F)
    (P : @TensorParameters F L V _ _ _ _ _ _ _ (ρG.comp L.subtype) h.irreducible d r)
    (A : Subgroup G) (hrank : rank A ≤ 3*r+1)
    (hcodim : fixedCodim ρG A ≤ 2 * rank A)
    (hmoving : ∃ a ∈ A, ¬ IsSchurLinear ρG L a) :
    letI := h.irreducible
    P.factors = 1 ∧ (P.blocks = 1 ∨ P.blocks = 2) := by
  let : IsIrreducible (ρG.comp L.subtype) := h.irreducible
  let : L.Normal := h.fitting ▸ inferInstance
  obtain ⟨a, ha, hnot⟩ := hmoving
  have hn : a ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    trivial
  have hhalf := finrank_le_twice_displacement_of_not_isSchurLinear ρG L a hn hnot
  have hdisp := displacement_finrank_le_fixedSpace_codim ρG A ha
  apply P.selection_of_degree_lt
  change Module.finrank (ZMod 2) (LinearMap.range (ρG a - 1)) ≤ fixedCodim ρG A at hdisp
  omega

/-- Failure of the two support alternatives leaves an actual ambient cubic
actor linear over the component Schur field. Its original rank and fixed-space
inequalities are retained for the remaining inner and outer calculations. -/
theorem source_schurLinear_actor_of_unselected {K : GroupClass}
    (h : SourceHypothesis K ρG L) (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : L ⧸ Subgroup.center L ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    (P : @TensorParameters F L V _ _ _ _ _ _ _ (ρG.comp L.subtype) h.irreducible
      (sourceDerivedEquiv h hr hF e) r)
    (hnot : letI := h.irreducible
      ¬ (P.factors = 1 ∧ (P.blocks = 1 ∨ P.blocks = 2))) :
    ∃ A : Subgroup G, IsElementaryTwo A ∧ IsCubic ρG A ∧
      rank A ≤ 3*r+1 ∧ fixedCodim ρG A ≤ 2 * rank A ∧
      (∀ a ∈ A, IsSchurLinear ρG L a) := by
  let : IsIrreducible (ρG.comp L.subtype) := h.irreducible
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  obtain ⟨A, hA, hc, hrank, hcodim, _⟩ := source_small_cubic_actor h hr hF e
  refine ⟨A, hA, hc, hrank, hcodim, ?_⟩
  intro a ha
  by_contra hn
  exact hnot (selection_of_schur_moving_actor h hr _ P A hrank hcodim ⟨a, ha, hn⟩)

end Ambient
end CFSG.Quasithin.ChapterK.Symplectic.Recognition
