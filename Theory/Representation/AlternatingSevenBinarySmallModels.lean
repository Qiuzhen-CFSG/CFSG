module

public import Theory.Representation.AbsolutelyIrreducible
public import Theory.Representation.AlternatingSevenConjugatePair.Model.Structure
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
public import Theory.Representation.BinaryPermutationNaturalStructure

/-!
# Absolutely irreducible binary four- and six-spaces for A₇

The two four-spaces are the actual restricted A₈ natural action and its odd
conjugate from `AlternatingSevenConjugatePair.Model`. An order-seven actor has
nonzero displacement divisible by three, hence a fixed line in dimension four.
For the augmentation core on seven letters, the point stabilizer fixes exactly
the line supported on the other six letters. Three explicit three-cycles give
the coordinate equalities, and augmentation forces the remaining coordinate
to vanish.

An endomorphism preserves each fixed line. Subtract its scalar on that line;
Schur's lemma makes the resulting endomorphism zero. The scalar-endomorphism
criterion therefore proves absolute irreducibility. The six-space is transported
through the established core-to-natural equivalence and a basis to `Fin 6 → ZMod 2`.
No recognition or classification assumption enters these constructions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, K.1.2,
printed p.452/PDF p.463 (citing Guralnick–Malle 2002, Theorem 6.2/Table 6.3),
and B.3.1 for the deleted permutation module. The fixed-line Schur argument also
appears in `MathieuCodeRestriction.M22.SourceModules.Irreducibility`.
-/

@[expose] public section

open Representation Representation.BinaryOffender
namespace Representation.AlternatingSevenBinarySmallModels

private theorem absolutelyIrreducible_of_fixed_line {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    [ρ.IsIrreducible] (D : Subgroup G)
    (hd : Module.finrank (ZMod 2) (fixedSpace ρ D) = 1) :
    ρ.IsAbsolutelyIrreducible := by
  apply (isAbsolutelyIrreducible_iff_surjective ρ).mpr
  intro f
  have hne : fixedSpace ρ D ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hd
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hfv : f v ∈ fixedSpace ρ D := by
    intro g
    change ρ g.val (f v) = f v
    rw [← f.isIntertwining, show ρ g.val v = v from hv g]
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hd hv hv0
  rw [hspan] at hfv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hfv
  refine ⟨c, ?_⟩
  have hz : f - algebraMap (ZMod 2) (End ρ) c = 0 := by
    rcases IsIrreducible.injective_or_eq_zero (f - algebraMap (ZMod 2) (End ρ) c) with hi | hz
    · exfalso
      apply hv0
      apply hi
      change f v - c • v = f 0 - c • (0 : V)
      rw [← hc, map_zero, smul_zero, sub_self, sub_self]
    · exact hz
  exact (sub_eq_zero.mp hz).symm


theorem four_fixed_line
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    (hf : Function.Injective ρ) (g : alternatingGroup (Fin 7)) (hg : orderOf g = 7) :
    Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers g)) = 1 := by
  have hlo := prime_order_le_fixedCodim ρ hf (by decide : Nat.Prime 7) (by decide) g hg
  rw [BinaryPrimeDegree.orderOf_two_mod_seven] at hlo
  have hd := orderOf_two_dvd_fixedCodim_of_isPGroup ρ (by decide : Nat.Prime 7)
    (by decide) (Subgroup.zpowers g) (IsPGroup.of_card (p := 7) (n := 1) (by
      simpa only [Nat.card_zpowers, pow_one] using hg))
  rw [BinaryPrimeDegree.orderOf_two_mod_seven] at hd
  have he := fixedCodim_add_finrank ρ (Subgroup.zpowers g)
  simp only [Module.finrank_pi, Fintype.card_fin] at he
  omega

private theorem faithful_four_absolute
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    [ρ.IsIrreducible] (hf : Function.Injective ρ) : ρ.IsAbsolutelyIrreducible := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 7)) 7 (by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial])
  exact absolutelyIrreducible_of_fixed_line ρ (Subgroup.zpowers g) (four_fixed_line ρ hf g hg)


private theorem absolutelyIrreducible_of_equiv {F G V W : Type*}
    [Field F] [Monoid G] [AddCommGroup V] [AddCommGroup W] [Module F V] [Module F W]
    {ρ : Representation F G V} {σ : Representation F G W}
    (e : ρ ≃ₗ σ) (h : IsAbsolutelyIrreducible ρ) : IsAbsolutelyIrreducible σ := by
  let E := AlgebraicClosure F
  let eE : extendScalars E ρ ≃ₗ extendScalars E σ :=
    .mk (e.toLinearEquiv.baseChange F E V W) (by
      intro g
      simpa only [LinearEquiv.coe_baseChange, extendScalars_apply,
        ← LinearMap.baseChange_comp] using
        congrArg (LinearMap.baseChange E) (e.isIntertwining' g))
  exact ⟨eE.irreducible_euqiv.mp h.irreducible_of_closure⟩

open BinaryPermutation
noncomputable section

abbrev Core := core (Fin 7)
abbrev coreAction := alternatingCoreRepresentation (Fin 7)

/-- The literal A₆ point stabilizer fixing letter zero. -/
def pointStabilizer : Subgroup (alternatingGroup (Fin 7)) :=
  MulAction.stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7)

/-- The augmentation-core vector supported on the six nonzero letters. -/
def pointLine : Core :=
  ⟨fun i => if i = 0 then 0 else 1, by rw [mem_core]; decide⟩

private theorem pointLine_ne_zero : pointLine ≠ 0 := by
  intro h
  have := congrArg (fun v : Core => v.val 1) h
  exact one_ne_zero this

private theorem pointLine_fixed : pointLine ∈ fixedSpace coreAction pointStabilizer := by
  intro g
  apply Subtype.ext
  funext i
  have hg : (g.val : Equiv.Perm (Fin 7)) 0 = 0 := g.property
  change (if (g.val : Equiv.Perm (Fin 7)).symm i = 0 then (0 : ZMod 2) else 1) =
    (if i = 0 then 0 else 1)
  simp only [Equiv.symm_apply_eq, hg]

private theorem point_fixed_coordinates (v : Core)
    (hv : v ∈ fixedSpace coreAction pointStabilizer) :
    v = (v.val 1) • pointLine := by
  have move (g : alternatingGroup (Fin 7)) (hg : g.val 0 = 0) (i : Fin 7) :
      v.val (g.val i) = v.val i := by
    have he := congrArg (fun w : Core => w.val (g.val i)) (hv ⟨g, hg⟩)
    change v.val (g.val.symm (g.val i)) = v.val (g.val i) at he
    simpa using he.symm
  let a : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap 1 2 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  let b : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap 3 4 * Equiv.swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  let c : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap 4 5 * Equiv.swap 5 6, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  have h2 : v.val 2 = v.val 1 := move a (by decide) 1
  have h3 : v.val 3 = v.val 2 := move a (by decide) 2
  have h4 : v.val 4 = v.val 3 := move b (by decide) 3
  have h5 : v.val 5 = v.val 4 := move b (by decide) 4
  have h6 : v.val 6 = v.val 5 := move c (by decide) 5
  have h0 : v.val 0 = 0 := by
    have hs := v.property
    rw [mem_core] at hs
    simpa [Fin.sum_univ_succ, h6, h5, h4, h3, h2, CharTwo.add_self_eq_zero] using hs
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [pointLine, h0, h2, h3, h4, h5, h6]

/-- The point stabilizer has a one-dimensional fixed space on the augmentation core. -/
theorem core_fixed_line :
    Module.finrank (ZMod 2) (fixedSpace coreAction pointStabilizer) = 1 := by
  have he : fixedSpace coreAction pointStabilizer =
      Submodule.span (ZMod 2) {pointLine} := by
    apply le_antisymm
    · intro v hv
      exact Submodule.mem_span_singleton.mpr ⟨v.val 1, (point_fixed_coordinates v hv).symm⟩
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr pointLine_fixed)
  rw [he]
  exact finrank_span_singleton pointLine_ne_zero

/-- The odd-degree core-to-natural identification intertwines the actual A₇ actions. -/
def coreNaturalEquiv : coreAction ≃ₗ alternatingNaturalRepresentation (Fin 7) :=
  .mk (coreEquivNatural (Fin 7) (by decide)) (by
    intro g
    apply LinearMap.ext
    intro v
    exact coreEquivNatural_equivariant (Fin 7) (by decide) g.val v)

/-- The augmentation core inherits irreducibility from the natural section. -/
theorem core_irreducible : coreAction.IsIrreducible :=
  coreNaturalEquiv.irreducible_of_euqiv (alternatingNatural_isIrreducible (by decide))

/-- The binary augmentation core on seven letters is absolutely irreducible. -/
theorem core_absolute : coreAction.IsAbsolutelyIrreducible := by
  let : coreAction.IsIrreducible := core_irreducible
  exact absolutelyIrreducible_of_fixed_line coreAction pointStabilizer core_fixed_line

/-- The actual six-dimensional deleted permutation module is absolutely irreducible. -/
theorem naturalSix_absolute :
    IsAbsolutelyIrreducible (alternatingNaturalRepresentation (Fin 7)) :=
  absolutelyIrreducible_of_equiv coreNaturalEquiv core_absolute

/-- A basis identification of the actual natural module with binary six-space. -/
def sixCoordinates : natural (Fin 7) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  (Module.finBasisOfFinrankEq (ZMod 2) (natural (Fin 7)) (by
    simpa using finrank_natural_odd (Fin 7) (by decide))).equivFun

/-- The natural A₇ action in six binary coordinates. -/
def six : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 6 → ZMod 2) :=
  sixCoordinates.conjRingEquiv.toMonoidHom.comp (alternatingNaturalRepresentation (Fin 7))

/-- The coordinate action is equivalent to the actual natural module. -/
def naturalSixEquiv : alternatingNaturalRepresentation (Fin 7) ≃ₗ six :=
  .mk sixCoordinates (by
    intro g
    ext v
    simp [six, LinearEquiv.conjRingEquiv])

/-- The constructed binary coordinate six-space is absolutely irreducible. -/
theorem six_absolute : six.IsAbsolutelyIrreducible :=
  absolutelyIrreducible_of_equiv naturalSixEquiv naturalSix_absolute

/-- The restricted A₈ natural four-space is absolutely irreducible for A₇. -/
theorem four_absolute : AlternatingSevenConjugatePair.Model.natural.IsAbsolutelyIrreducible := by
  let : AlternatingSevenConjugatePair.Model.natural.IsIrreducible :=
    AlternatingSevenConjugatePair.Model.natural_isIrreducible
  exact faithful_four_absolute _ AlternatingSevenConjugatePair.Model.natural_faithful

/-- The odd conjugate four-space is absolutely irreducible for A₇. -/
theorem outerFour_absolute :
    AlternatingSevenConjugatePair.Model.outerNatural.IsAbsolutelyIrreducible := by
  let : AlternatingSevenConjugatePair.Model.outerNatural.IsIrreducible :=
    AlternatingSevenConjugatePair.Model.outerNatural_isIrreducible
  exact faithful_four_absolute _ AlternatingSevenConjugatePair.Model.outerNatural_faithful

end
end Representation.AlternatingSevenBinarySmallModels
