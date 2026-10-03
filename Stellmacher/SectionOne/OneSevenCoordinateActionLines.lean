module
public import Stellmacher.SectionOne.OneSevenSylowOffender
public import Stellmacher.SectionOne.SL2FamilySylowCoordinates

/-!
# Natural commutator lines for the Sylow coordinates

For a normal internal product of one-seven factors acting faithfully on a
finite elementary abelian two-group, assume that distinct factor supports
are disjoint. Each coordinate of an ambient Sylow two-subgroup has an
order-two action commutator. Acting with the entire Sylow intersection on
one factor support gives precisely that coordinate's full commutator.

Distinct factors commute, so they preserve each other's supports.
Disjointness then forces their actions on those supports to be trivial.
The Sylow-coordinate generation theorem reduces the upper containment to
individual factors. Conversely, the coprime derived subgroup splits the
module into its four-element support and its fixed complement; the full
factor fixes that complement. Thus every coordinate commutator comes from
its own support. The faithful involution commutator theorem gives order two.

This intrinsic action result preserves the supplied raw family and action.
Its native conjugation transport supplies the commutator-line permutation
argument in Stellmacher (4.6), Journal of Algebra 190 (1997), p26, following
refs/latex/stellmacher-n-group.tex.
-/

open scoped IsMulCommutative
namespace Stellmacher.SectionOne
universe u

private theorem support_fixed_of_commute_disjoint
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (D E : Subgroup G)
    (hcomm : D ≤ Subgroup.centralizer (E : Set G))
    (hdisj : Disjoint (commutatorAction D V) (commutatorAction E V)) :
    commutatorAction E V ≤ FixedPoints.subgroup D V := by
  let hinv := commutatorAction_isInvariant_of_normalizing_actor (V := V) D E
    (hcomm.trans (Subgroup.centralizer_le_normalizer _))
  intro v hv d
  have hdv : d • v ∈ commutatorAction E V := (hinv.invariant d v).mp hv
  have hdeltaE := (commutatorAction E V).mul_mem ((commutatorAction E V).inv_mem hv) hdv
  have hdeltaD : v⁻¹ * (d • v) ∈ commutatorAction D V := by
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨d, v, rfl⟩
  have hone : v⁻¹ * (d • v) = 1 := hdisj.le_bot ⟨hdeltaD, hdeltaE⟩
  exact (inv_mul_eq_one.mp hone).symm

/-- The full Sylow intersection acts on each support through its order-two coordinate. -/
public theorem oneSevenFactor_sylow_coordinate_action_lines
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (T : Sylow 2 G) (E : Subgroup G) (hEnormal : E.Normal)
    {n : ℕ} (D : Fin n → Subgroup G)
    (hprod : IsInternalDirectProductFamily E D)
    (hD : ∀ i, IsOneSevenFactor (V := V) (D i))
    (hdisj : Pairwise fun i j =>
      Disjoint (commutatorAction (D i) V) (commutatorAction (D j) V)) :
    ∀ i, commutatorSubgroup (↥((T : Subgroup G) ⊓ E)) V (commutatorAction (D i) V) =
        commutatorAction (↥((T : Subgroup G) ⊓ D i)) V ∧
      Nat.card (commutatorAction (↥((T : Subgroup G) ⊓ D i)) V) = 2 := by
  classical
  let Q : Fin n → Subgroup G := fun i => (T : Subgroup G) ⊓ D i
  let R : Subgroup G := (T : Subgroup G) ⊓ E
  let U : Fin n → Subgroup V := fun i => commutatorAction (D i) V
  obtain ⟨hgen, hcard⟩ := sl2_family_sylow_coordinates T E hEnormal D hprod (fun i => (hD i).1)
  have hQiR (i : Fin n) : Q i ≤ R := by
    rw [show R = ⨆ j, Q j from hgen]
    exact le_iSup Q i
  have hcross (i j : Fin n) (hij : i ≠ j) : U i ≤ FixedPoints.subgroup (D j) V := by
    apply support_fixed_of_commute_disjoint (D j) (D i) ?_ (hdisj (Ne.symm hij))
    rw [Subgroup.le_centralizer_iff]
    intro x hx y hy
    exact (hprod.2.2 i j hij x hx y hy).symm
  intro i
  let K := commutatorAction (Q i) V
  let C := FixedPoints.subgroup ((commutator (D i)).map (D i).subtype) V
  have hcop : Nat.Coprime (Nat.card ((commutator (D i)).map (D i).subtype)) (Nat.card V) := by
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [(hD i).2.1.2.1, hk]
    exact (show Nat.Coprime 3 2 by decide).pow_right k
  have hcompl : IsCompl C (U i) := by
    dsimp only [C, U]
    rw [oneSevenFactor_full_commutator_eq_derived (D i) (hD i)]
    exact isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := ((commutator (D i)).map (D i).subtype))
      (Group.isSolvable_of_comm fun x y => (IsMulCommutative.is_comm (M := V)).comm x y)
      hcop (inferInstance : IsMulCommutative V)
  have hCfix (q : Q i) (v : V) (hv : v ∈ C) : q • v = v :=
    oneSevenFactor_fixes_derived_fixedPoints (D i) (hD i) q q.property.2 v hv
  have hupper : commutatorSubgroup R V (U i) ≤ K := by
    rw [commutatorSubgroup]
    apply (Subgroup.closure_le _).mpr
    rintro z ⟨r, u, hu, rfl⟩
    have hr : (r : G) ∈ ⨆ j, Q j := by rw [← hgen]; exact r.property
    have hact : ∀ u : V, u ∈ U i → (r : G) • u ∈ U i ∧ u⁻¹ * ((r : G) • u) ∈ K := by
      apply Subgroup.iSup_induction Q
        (C := fun r => ∀ u : V, u ∈ U i → r • u ∈ U i ∧ u⁻¹ * (r • u) ∈ K) hr
      · intro j q hq u hu
        by_cases hji : j = i
        · subst j
          have hinv := commutatorAction_isInvariant_of_normalizing_actor (V := V) (Q i) (D i)
            (inf_le_right.trans (D i).le_normalizer)
          refine ⟨(hinv.invariant ⟨q, hq⟩ u).mp hu, ?_⟩
          change u⁻¹ * (q • u) ∈ commutatorAction (Q i) V
          rw [commutatorAction_eq_closure]
          exact Subgroup.subset_closure ⟨⟨q, hq⟩, u, rfl⟩
        · have hfix : q • u = u := hcross i j (Ne.symm hji) hu ⟨q, hq.2⟩
          rw [hfix, inv_mul_cancel]
          exact ⟨hu, K.one_mem⟩
      · intro u hu
        simp only [one_smul, inv_mul_cancel]
        exact ⟨hu, K.one_mem⟩
      · intro x y hx hy u hu
        have hyu := hy u hu
        have hxyu := hx (y • u) hyu.1
        refine ⟨by simpa only [mul_smul] using hxyu.1, ?_⟩
        have hk := K.mul_mem hyu.2 hxyu.2
        simpa only [mul_smul, mul_assoc, mul_inv_cancel_left] using hk
    exact (hact u hu).2
  have hlower : K ≤ commutatorSubgroup R V (U i) := by
    change commutatorAction (Q i) V ≤ _
    rw [commutatorAction_eq_closure]
    apply (Subgroup.closure_le _).mpr
    rintro z ⟨q, v, rfl⟩
    have hv : v ∈ C ⊔ U i := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨c, hc, u, hu, rfl⟩ := Subgroup.mem_sup.mp hv
    have hdelta : (c * u)⁻¹ * (q • (c * u)) = u⁻¹ * (q • u) := by
      rw [mul_inv_rev, smul_mul', hCfix q c hc]
      group
    rw [hdelta]
    exact Subgroup.subset_closure ⟨⟨q, hQiR i q.property⟩, u, hu, rfl⟩
  exact ⟨le_antisymm hupper hlower,
    oneSevenFactor_involution_commutator_card_two hfaith (D i) (Q i) (hD i)
      inf_le_right (hcard i)⟩

end Stellmacher.SectionOne

