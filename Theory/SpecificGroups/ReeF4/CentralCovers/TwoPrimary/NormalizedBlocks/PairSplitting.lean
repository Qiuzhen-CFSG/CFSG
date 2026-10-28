module

public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.RootBlocks
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.NormalizedBlocks.PairSplitting.ScalarActors
public import Theory.GroupTheory.Commutator.CentralExtensionPairing
public import Theory.GroupTheory.Commutator.ScalarInvariantRoot
public import Theory.GroupTheory.PerfectCentralCover

/-!
# Additive sections of the four paired Ree root groups

The paired positive-root factors are additive copies of the coefficient field.
Their full scalar action is realized by the literal fixed coroot torus, so the
central-extension commutator argument makes their full preimages abelian.
For a scalar `c ≠ 0, 1`, a lift `v` of its actor, and arbitrary lifts `w(t)`
of the root curve, the section is `x ↦ [v, w((c-1)⁻¹*x)]`. Centrality of
the kernel makes the commutator independent of the chosen lifts, and the
abelian preimage proves additivity. Coordinate uniqueness then transports
this lift to each actual subgroup, retaining its projection triangle.

Source: Aschbacher–Smith I.1.1–4, printed pp.407–408; GLS3 §6.1 and
§§2.3–2.4.
-/

public section
noncomputable section
namespace ReeF4.CentralCovers.TwoPrimary.PairSplitting

open scoped BigOperators commutatorElement
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open ReeF4
open ReeF4.CentralCovers.TwoPrimary
open ReeF4.Parabolics
open ReeF4.Parabolics.RadicalCoordinates
open ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates
open ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open ReeF4.LocalBlockInput.PairRigidity.BlockParameters
open ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open ReeF4.NormalizedRootCentralizers.CenterExponent
open ReeF4.ElementaryTwoBound ReeF4.ElementaryTwoBound.RootCalculations
open RootPairing.IntegralGeckConstruction

private theorem root_zero (m : ℕ) (r : F4Chevalley.Root) :
    rootGeneratorInGroup m r 0 = 1 := Subtype.ext (F4Chevalley.rootCurve_zero r)

private theorem pairWord_injective (m : ℕ) (B : RootBlocks .positive) (j : Fin 4) :
    Function.Injective (pairWord m (fun k => (B.roots (.inl (j,k))).val)) := by
  classical
  let pack (t : Fin 2 → CoefficientField m) : BlockParameters m .positive :=
    (fun i : Fin 4 => if i = j then t else fun _ => 0, fun _ _ => 0)
  have hw (t : Fin 2 → CoefficientField m) :
      B.blockWord m (pack t) = pairWord m (fun k => (B.roots (.inl (j,k))).val) t := by
    fin_cases j <;> simp [RootBlocks.blockWord, pack, pairCount, quartetCount,
      List.ofFn_succ, pairWord, quartetWord, root_zero]
  intro t u h
  have hp := B.blockWord_injective m (wordInSubgroup_bijective m B.order)
    ((hw t).trans (h.trans (hw u).symm))
  have hh := congrArg (fun p => p.1 j) hp
  simpa [pack] using hh

private theorem pairHom_injective (m : ℕ) (j : Fin 4) :
    Function.Injective (pairHom m (rootIndex (.inl j))
      (positiveRootWordLayout.pair_odd j)) := by
  intro a b hab
  have he := congrArg (toSplitGroup m) hab
  change toSplitGroup m (mainElement m (rootIndex (.inl j)) a.toAdd) =
      toSplitGroup m (mainElement m (rootIndex (.inl j)) b.toAdd) at he
  rw [mainElement_coe, mainElement_coe] at he
  change rootWord m (positiveRootWordLayout.pairIndex j) a.toAdd =
      rootWord m (positiveRootWordLayout.pairIndex j) b.toAdd at he
  rw [positiveRootWordLayout.pair_rootWord m j,
    positiveRootWordLayout.pair_rootWord m j] at he
  have hp := pairWord_injective m positiveRootWordLayout.blocks j he
  exact Multiplicative.toAdd.injective (congrFun hp 0)

private theorem pairHom_section (m : ℕ) (hm : 1 ≤ m) (j : Fin 4)
    {E : Type*} [Group E] (f : E →* Model m)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hscalar : ∀ c : CoefficientField m, c ≠ 0 → ∃ z : Model m, ∀ x,
      z * pairHom m (rootIndex (.inl j)) (positiveRootWordLayout.pair_odd j)
          (.ofAdd x) * z⁻¹ =
        pairHom m (rootIndex (.inl j)) (positiveRootWordLayout.pair_odd j)
          (.ofAdd (c*x))) :
    ∃ s : X m (rootIndex (.inl j)) →* E,
      f.comp s = (X m (rootIndex (.inl j))).subtype := by
  classical
  let u : Multiplicative (CoefficientField m) →* Model m :=
    pairHom m (rootIndex (.inl j)) (positiveRootWordLayout.pair_odd j)
  have hu : ∀ c : CoefficientField m, c ≠ 0 → ∃ t : Model m, ∀ x,
      t * u (.ofAdd x) * t⁻¹ = u (.ofAdd (c*x)) := hscalar
  have hcard : 4 < Nat.card (CoefficientField m) := by
    rw [field_card]
    have hh : 2 < 2*m + 1 := by omega
    have hp := Nat.pow_lt_pow_right (a := 2) (by omega) hh
    simpa using hp
  obtain ⟨c, hc, hc1⟩ : ∃ c : CoefficientField m, c ≠ 0 ∧ c ≠ 1 := by
    have hcu : 1 < Nat.card (CoefficientField m)ˣ := by
      rw [Nat.card_units]
      omega
    let : Nontrivial (CoefficientField m)ˣ :=
      Finite.one_lt_card_iff_nontrivial.mp hcu
    obtain ⟨c, hc⟩ := exists_ne (1 : (CoefficientField m)ˣ)
    exact ⟨c, c.ne_zero, fun h => hc (Units.ext h)⟩
  have hcom : ∀ v w : E, f v ∈ u.range → f w ∈ u.range → Commute v w := by
    intro v w hv hw
    exact CentralExtension.commute_lifts_of_full_scalar_action hcard f hf hk u hu hv hw
  have hs0_exists : ∃ s₀ : Multiplicative (CoefficientField m) →* E,
      f.comp s₀ = u := by
    -- The commutator construction below is the standard additive lift.
    obtain ⟨z, hz⟩ := hu c hc
    obtain ⟨v, hv⟩ := hf z
    choose w hw using fun x : CoefficientField m => hf (u (.ofAdd x))
    let q : CoefficientField m → E := fun x =>
      ⁅v, w ((c-1)⁻¹*x)⁆
    have hd : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
    have hq (x : CoefficientField m) : f (q x) = u (.ofAdd x) := by
      dsimp [q]
      rw [map_commutatorElement, commutatorElement_def, hv, hw, hz,
        ← map_inv, ← map_mul]
      change u (.ofAdd (c*((c-1)⁻¹*x) + -((c-1)⁻¹*x))) = u (.ofAdd x)
      congr 1
      change c*((c-1)⁻¹*x) + -((c-1)⁻¹*x) = x
      calc
        _ = (c-1)*((c-1)⁻¹*x) := by ring
        _ = x := mul_inv_cancel_left₀ hd x
    have hq0 : q 0 = 1 := by
      dsimp [q]
      rw [mul_zero]
      have h0 : f (w 0) = f 1 := by rw [hw]; exact u.map_one.trans f.map_one.symm
      rw [CentralExtension.commutator_eq_of_image_eq f hk rfl h0]
      simp
    have hqadd (x y : CoefficientField m) : q (x+y) = q x * q y := by
      have hsum : f (w ((c-1)⁻¹*(x+y))) =
          f (w ((c-1)⁻¹*x) * w ((c-1)⁻¹*y)) := by
        rw [map_mul, hw, hw, hw, ← map_mul, mul_add]
        rfl
      have hcw : Commute (w ((c-1)⁻¹*x)) (q y) := hcom _ _
        (by rw [hw]; exact ⟨.ofAdd _, rfl⟩) (by rw [hq]; exact ⟨.ofAdd _, rfl⟩)
      change ⁅v, w ((c-1)⁻¹*(x+y))⁆ = _
      rw [CentralExtension.commutator_eq_of_image_eq f hk rfl hsum,
        commutatorElement_mul_right_eq_mul_conj]
      change q x * w ((c-1)⁻¹*x) * q y * (w ((c-1)⁻¹*x))⁻¹ = _
      rw [mul_assoc (q x), hcw.eq, ← mul_assoc, mul_assoc (q x * q y),
        mul_inv_cancel, mul_one]
    let s₀ : Multiplicative (CoefficientField m) →* E := {
      toFun := fun x => q x.toAdd
      map_one' := hq0
      map_mul' := fun x y => hqadd x.toAdd y.toAdd }
    exact ⟨s₀, MonoidHom.ext (fun x => hq x.toAdd)⟩
  obtain ⟨s₀, hs₀⟩ := hs0_exists
  let uh : Multiplicative (CoefficientField m) →* X m (rootIndex (.inl j)) :=
    u.codRestrict _ (fun x => mainElement_mem_X m (rootIndex (.inl j)) x.toAdd)
  have hub : Function.Bijective uh := by
    constructor
    · intro a b hab
      apply pairHom_injective m j
      exact congrArg Subtype.val hab
    · intro x
      obtain ⟨a, ha⟩ := (mem_X_iff m (rootIndex (.inl j))
        (positiveRootWordLayout.pair_odd j) x).mp x.property
      exact ⟨.ofAdd a, Subtype.ext ha⟩
  let e : Multiplicative (CoefficientField m) ≃* X m (rootIndex (.inl j)) :=
    MulEquiv.ofBijective uh hub
  refine ⟨s₀.comp e.symm.toMonoidHom, ?_⟩
  apply MonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := e.surjective x
  change f (s₀ (e.symm (e a))) = (e a).val
  rw [e.symm_apply_apply]
  exact DFunLike.congr_fun hs₀ a

/-- The four additive root groups split in every central extension. The lift
is constructed from commutators with a scalar actor and retains its projection. -/
theorem exists_pair_sections_of_central_extension (m : ℕ) (hm : 1 ≤ m)
    {E : Type*} [Group E] (f : E →* Model m)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    ∀ j : Fin 4, ∃ s : X m (rootIndex (.inl j)) →* E,
      f.comp s = (X m (rootIndex (.inl j))).subtype := by
  intro j
  exact pairHom_section m hm j f hf hk (exists_scalar_actor m j)

/-- The requested family for finite perfect degree-two covers, on precisely
blocks `[7, 1, 5, 3]` in zero-based root indexing. -/
theorem exists_pair_sections (m : ℕ) (hm : 1 ≤ m)
    {E : Type*} [Group E] [Finite E] (d : PerfectCentralCovering.Cover E (Model m))
    (_hd : Nat.card d.toMonoidHom.ker = 2) :
    ∀ j : Fin 4, ∃ s : X m (rootIndex (.inl j)) →* E,
      d.toMonoidHom.comp s = (X m (rootIndex (.inl j))).subtype :=
  exists_pair_sections_of_central_extension m hm d.toMonoidHom d.surjective d.ker_le_center

end ReeF4.CentralCovers.TwoPrimary.PairSplitting
