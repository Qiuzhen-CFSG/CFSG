module

public import Stellmacher.SectionOne.OneSevenCoordinateActionLines

/-!
# The commutator plane of an involution exchanging two factors

Explicit swapped-factor coordinates identify the full involution commutator
with the image of the injective displacement map on one four-element support.
The fixed subgroup of the base in that image corresponds to the fixed line in
the support. The whole image is fixed by the involution, so the base-fixed line
is fixed by the join of the base and the involution subgroup.

For an actor `d` in the first factor, the diagonal actor `d * (y * d * y⁻¹)`
centralizes the involution subgroup and transports displacement vectors by
the original first-factor action. Thus first-factor transitivity gives
transitivity of the actual actor centralizer on the commutator plane.

This module proves only the coordinate-level calculation. Its coordinate
record must still be produced from the canonical Section One hypotheses;
it is not a replacement for that extraction or the original theorem.
The source application is Stellmacher (9.3), printed p50/PDF40 of
`refs/files/stellmacher-n-group.pdf`.
-/

open scoped IsMulCommutative

namespace Stellmacher.SectionOne

universe u

public structure SwappedFactorActionCoordinates
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (B Y : Subgroup K) where
  swap : Y
  swap_ne_one : swap ≠ 1
  support : Subgroup V
  factor : Subgroup K
  support_card : Nat.card support = 4
  support_disjoint : Disjoint support
    (support.map (MulDistribMulAction.toMulAut K V (swap : K)).toMonoidHom)
  support_span : support ⊔
    support.map (MulDistribMulAction.toMulAut K V (swap : K)).toMonoidHom = ⊤
  factor_cross_fixed : ∀ actor ∈ factor, ∀ vector ∈ support,
    actor • ((swap : K) • vector) = (swap : K) • vector
  factor_conjugate_commute : ∀ actor ∈ factor,
    actor * ((swap : K) * actor * (swap : K)⁻¹) =
      ((swap : K) * actor * (swap : K)⁻¹) * actor
  factor_transitive : ∀ vector ∈ support, vector ≠ 1 →
    ∀ target ∈ support, target ≠ 1 → ∃ actor ∈ factor, actor • vector = target
  base_preserves : ∀ actor ∈ B, ∀ vector ∈ support, actor • vector ∈ support
  swap_normalizes_base : ∀ actor ∈ B, (swap : K)⁻¹ * actor * (swap : K) ∈ B
  base_fixed_card : Nat.card (support ⊓ FixedPoints.subgroup B V : Subgroup V) = 2

private def displacement
    {K V : Type u} [Group K] [Group V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction K V] (actor : K) : V →* V where
  toFun vector := vector⁻¹ * (actor • vector)
  map_one' := by simp
  map_mul' vector target := by
    simp only [mul_inv_rev, smul_mul']
    ac_rfl

private theorem swapped_displacement_injective
    {K V : Type u} [Group K] [Group V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction K V] (actor : K) (support : Subgroup V)
    (hdisjoint : Disjoint support
      (support.map (MulDistribMulAction.toMulAut K V actor).toMonoidHom)) :
    Function.Injective ((displacement actor).comp support.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_bot_iff.mp
  intro vector hvector
  apply Subtype.ext
  have hfixed : actor • (vector : V) = vector :=
    (inv_mul_eq_one.mp (show (vector : V)⁻¹ * (actor • (vector : V)) = 1 from hvector)).symm
  apply hdisjoint.le_bot
  refine ⟨vector.property, ?_⟩
  exact ⟨vector, vector.property, hfixed⟩

private theorem swapped_displacement_range
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (Y : Subgroup K) (hcard : Nat.card Y = 2) (actor : Y) (hne : actor ≠ 1)
    (support : Subgroup V)
    (hspan : support ⊔
      support.map (MulDistribMulAction.toMulAut K V (actor : K)).toMonoidHom = ⊤) :
    ((displacement (actor : K)).comp support.subtype).range = commutatorAction Y V := by
  have hsquare : (actor : K) * (actor : K) = 1 := by
    have hh : actor ^ 2 = 1 := hcard ▸ pow_card_eq_one' (x := actor)
    exact congrArg Subtype.val (show actor * actor = 1 by simpa [pow_two] using hh)
  let delta := (displacement (actor : K)).comp support.subtype
  apply le_antisymm
  · rintro vector ⟨source, rfl⟩
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨actor, (source : V), rfl⟩
  · rw [commutatorAction_eq_closure]
    apply (Subgroup.closure_le _).mpr
    rintro vector ⟨other, source, rfl⟩
    by_cases hother : other = 1
    · simp only [hother, one_smul, inv_mul_cancel]
      exact delta.range.one_mem
    · obtain ⟨unique, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : Y)).mp hcard
      have heq : other = actor := (hunique other hother).trans (hunique actor hne).symm
      subst other
      have hsource : source ∈ support ⊔
          support.map (MulDistribMulAction.toMulAut K V (actor : K)).toMonoidHom := by
        rw [hspan]
        trivial
      obtain ⟨left, hleft, right, hright, rfl⟩ := Subgroup.mem_sup.mp hsource
      obtain ⟨right, hright, rfl⟩ := hright
      refine ⟨⟨left * right⁻¹, support.mul_mem hleft (support.inv_mem hright)⟩, ?_⟩
      change (left * right⁻¹)⁻¹ * ((actor : K) • (left * right⁻¹)) =
        (left * ((actor : K) • right))⁻¹ *
          ((actor : K) • (left * ((actor : K) • right)))
      simp only [mul_inv_rev, inv_inv, smul_mul', smul_inv', ← mul_smul, hsquare, one_smul]
      ac_rfl

private theorem swapped_displacement_fixed_iff
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    {B Y : Subgroup K} (coordinates : SwappedFactorActionCoordinates (V := V) B Y)
    (vector : V) (hvector : vector ∈ coordinates.support) :
    displacement (coordinates.swap : K) vector ∈ FixedPoints.subgroup B V ↔
      vector ∈ FixedPoints.subgroup B V := by
  let support := coordinates.support
  let swap : K := coordinates.swap
  let moved := support.map (MulDistribMulAction.toMulAut K V swap).toMonoidHom
  have hmoved : swap • vector ∈ moved := ⟨vector, hvector, rfl⟩
  have hconjugate (actor : B) : swap⁻¹ * (actor : K) * swap ∈ B :=
    coordinates.swap_normalizes_base actor actor.property
  have haction (actor : B) : (actor : K) • (swap • vector) =
      swap • ((swap⁻¹ * (actor : K) * swap) • vector) := by
    simp only [← mul_smul]
    congr 1
    group
  constructor
  · intro hfixed actor
    have hfirst : (actor : K) • vector ∈ support :=
      coordinates.base_preserves actor actor.property vector hvector
    have hsecond : (actor : K) • (swap • vector) ∈ moved := by
      refine ⟨(swap⁻¹ * (actor : K) * swap) • vector,
        coordinates.base_preserves _ (hconjugate actor) vector hvector, ?_⟩
      exact (haction actor).symm
    have heq : (((actor : K) • vector)⁻¹ * ((actor : K) • (swap • vector))) =
        vector⁻¹ * (swap • vector) := by
      have hh := hfixed actor
      change (actor : K) • (vector⁻¹ * (swap • vector)) = vector⁻¹ * (swap • vector) at hh
      simpa only [smul_mul', smul_inv'] using hh
    have hpair :
        ((⟨((actor : K) • vector)⁻¹, support.inv_mem hfirst⟩ : support),
          (⟨(actor : K) • (swap • vector), hsecond⟩ : moved)) =
        ((⟨vector⁻¹, support.inv_mem hvector⟩ : support),
          (⟨swap • vector, hmoved⟩ : moved)) :=
      Subgroup.mul_injective_of_disjoint coordinates.support_disjoint heq
    apply inv_injective
    exact congrArg (fun pair : support × moved => (pair.1 : V)) hpair
  · intro hfixed actor
    change (actor : K) • (vector⁻¹ * (swap • vector)) = vector⁻¹ * (swap • vector)
    rw [smul_mul', smul_inv', show (actor : K) • vector = vector from hfixed actor,
      haction actor]
    rw [show (swap⁻¹ * (actor : K) * swap) • vector = vector from
      hfixed ⟨_, hconjugate actor⟩]

private theorem swapped_diagonal_actor
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    {B Y : Subgroup K} (coordinates : SwappedFactorActionCoordinates (V := V) B Y)
    (hcard : Nat.card Y = 2) (actor : K) (hactor : actor ∈ coordinates.factor) :
    let diagonal := actor * ((coordinates.swap : K) * actor * (coordinates.swap : K)⁻¹)
    diagonal ∈ Subgroup.centralizer (Y : Set K) ∧
      ∀ vector ∈ coordinates.support,
        diagonal • displacement (coordinates.swap : K) vector =
          displacement (coordinates.swap : K) (actor • vector) := by
  let swap : K := coordinates.swap
  have hsquare : swap * swap = 1 := by
    have hh : coordinates.swap ^ 2 = 1 := hcard ▸ pow_card_eq_one' (x := coordinates.swap)
    exact congrArg Subtype.val (show coordinates.swap * coordinates.swap = 1 by
      simpa [pow_two] using hh)
  have hinverse : swap⁻¹ = swap := (eq_inv_of_mul_eq_one_left hsquare).symm
  let conjugate := swap * actor * swap⁻¹
  have hcommute : actor * conjugate = conjugate * actor :=
    coordinates.factor_conjugate_commute actor hactor
  have hcross (vector : V) (hvector : vector ∈ coordinates.support) :
      actor • (swap • vector) = swap • vector :=
    coordinates.factor_cross_fixed actor hactor vector hvector
  change actor * conjugate ∈ Subgroup.centralizer (Y : Set K) ∧ _
  constructor
  · intro other hother
    by_cases hone : other = 1
    · simp [hone]
    · obtain ⟨unique, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : Y)).mp hcard
      have hne : (⟨other, hother⟩ : Y) ≠ 1 := fun he => hone (congrArg Subtype.val he)
      have heq : other = swap := congrArg Subtype.val
        ((hunique ⟨other, hother⟩ hne).trans
          (hunique coordinates.swap coordinates.swap_ne_one).symm)
      rw [heq]
      calc
        swap * (actor * conjugate) = conjugate * actor * swap := by
          dsimp only [conjugate]
          rw [hinverse]
          simp only [mul_assoc]
        _ = actor * conjugate * swap := by rw [← hcommute]
  · intro vector hvector
    have hfirst : conjugate • vector = vector := by
      dsimp only [conjugate]
      rw [mul_smul, mul_smul, hinverse, hcross vector hvector, ← mul_smul, hsquare, one_smul]
    have hsecond : conjugate • (swap • vector) = swap • (actor • vector) := by
      dsimp only [conjugate]
      simp only [mul_smul, inv_smul_smul]
    change (actor * conjugate) • (vector⁻¹ * (swap • vector)) =
      (actor • vector)⁻¹ * (swap • (actor • vector))
    rw [smul_mul', smul_inv', mul_smul, hfirst]
    have hswapimage : (actor * conjugate) • (swap • vector) =
        swap • (actor • vector) := by
      rw [hcommute, mul_smul, hcross vector hvector, hsecond]
    rw [hswapimage]

/-- The literal displacement plane and centralizer action from swapped coordinates. -/
public theorem swappedFactorActionCoordinates_involution_plane
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (S B Y : Subgroup K) (hSY : S = B ⊔ Y) (hcard : Nat.card Y = 2)
    (coordinates : SwappedFactorActionCoordinates (V := V) B Y) :
    let W := commutatorAction Y V
    Nat.card W = 4 ∧
      Nat.card (W ⊓ FixedPoints.subgroup B V : Subgroup V) = 2 ∧
      (W ⊓ FixedPoints.subgroup S V ≠ ⊥) ∧
      (∀ vector ∈ W, vector ≠ 1 → ∀ target ∈ W, target ≠ 1 →
        ∃ actor ∈ Subgroup.centralizer (Y : Set K), actor • vector = target) := by
  let support := coordinates.support
  let swap : K := coordinates.swap
  let delta : support →* V := (displacement swap).comp support.subtype
  let W := commutatorAction Y V
  have hinjective : Function.Injective delta :=
    swapped_displacement_injective swap support coordinates.support_disjoint
  have hrange : delta.range = W := swapped_displacement_range Y hcard
    coordinates.swap coordinates.swap_ne_one support coordinates.support_span
  have hmem (vector : support) : delta vector ∈ W := hrange ▸ ⟨vector, rfl⟩
  have hsurjective (vector : V) (hvector : vector ∈ W) : ∃ source : support, delta source = vector := by
    rw [← hrange] at hvector
    exact hvector
  have hWcard : Nat.card W = 4 := by
    rw [← hrange]
    exact (Nat.card_congr (Equiv.ofBijective delta.rangeRestrict
      ⟨fun left right heq => hinjective (congrArg Subtype.val heq),
        delta.rangeRestrict_surjective⟩).symm).trans coordinates.support_card
  have hfixed (vector : support) : delta vector ∈ FixedPoints.subgroup B V ↔
      (vector : V) ∈ FixedPoints.subgroup B V :=
    swapped_displacement_fixed_iff coordinates vector vector.property
  let sourceLine := support ⊓ FixedPoints.subgroup B V
  let targetLine := W ⊓ FixedPoints.subgroup B V
  let lineMap : sourceLine → targetLine := fun vector =>
    ⟨delta ⟨vector, vector.property.1⟩,
      hmem ⟨vector, vector.property.1⟩,
      (hfixed ⟨vector, vector.property.1⟩).mpr vector.property.2⟩
  have hlineBijective : Function.Bijective lineMap := by
    constructor
    · intro left right heq
      apply Subtype.ext
      exact congrArg (fun vector : support => (vector : V))
        (hinjective (congrArg Subtype.val heq))
    · intro vector
      obtain ⟨source, hsource⟩ := hsurjective vector vector.property.1
      have hsourceFixed : (source : V) ∈ FixedPoints.subgroup B V :=
        (hfixed source).mp (hsource ▸ vector.property.2)
      exact ⟨⟨source, source.property, hsourceFixed⟩, Subtype.ext hsource⟩
  have hlineCard : Nat.card targetLine = 2 :=
    (Nat.card_congr (Equiv.ofBijective lineMap hlineBijective).symm).trans
      coordinates.base_fixed_card
  have hVnontrivial : 1 < Nat.card V := by
    have hle := Nat.card_le_card_of_injective support.subtype support.subtype_injective
    rw [coordinates.support_card] at hle
    omega
  let _ : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp hVnontrivial
  have hswapSquare : coordinates.swap ^ 2 = 1 := hcard ▸ pow_card_eq_one' (x := coordinates.swap)
  have hWfixed : W ≤ FixedPoints.subgroup Y V :=
    (card_two_action_fixed_commutator_card_data (U := V) coordinates.swap
      ⟨coordinates.swap_ne_one, hswapSquare⟩ hcard).2
  have hlineLe : targetLine ≤ W ⊓ FixedPoints.subgroup S V := by
    intro vector hvector
    refine ⟨hvector.1, ?_⟩
    have hfixer : S ≤ fixingSubgroup K ({vector} : Set V) := by
      rw [hSY]
      apply sup_le
      · intro actor hactor
        rw [mem_fixingSubgroup_iff]
        intro target htarget
        obtain rfl := Set.mem_singleton_iff.mp htarget
        exact hvector.2 ⟨actor, hactor⟩
      · intro actor hactor
        rw [mem_fixingSubgroup_iff]
        intro target htarget
        obtain rfl := Set.mem_singleton_iff.mp htarget
        exact hWfixed hvector.1 ⟨actor, hactor⟩
    intro actor
    exact (mem_fixingSubgroup_iff (M := K)).mp (hfixer actor.property) vector
      (Set.mem_singleton vector)
  refine ⟨hWcard, hlineCard, ?_, ?_⟩
  · intro hbot
    have hlineBot : targetLine = ⊥ := le_bot_iff.mp (hbot ▸ hlineLe)
    have hone : Nat.card targetLine = 1 := Subgroup.card_eq_one.mpr hlineBot
    omega
  · intro vector hvector hvectorNe target htarget htargetNe
    obtain ⟨source, rfl⟩ := hsurjective vector hvector
    obtain ⟨destination, rfl⟩ := hsurjective target htarget
    have hsourceNe : (source : V) ≠ 1 := by
      intro hone
      exact hvectorNe (by rw [show source = 1 from Subtype.ext hone, map_one])
    have hdestinationNe : (destination : V) ≠ 1 := by
      intro hone
      exact htargetNe (by rw [show destination = 1 from Subtype.ext hone, map_one])
    obtain ⟨actor, hactor, haction⟩ := coordinates.factor_transitive source source.property
      hsourceNe destination destination.property hdestinationNe
    obtain ⟨hcentral, hdiagonal⟩ := swapped_diagonal_actor coordinates hcard actor hactor
    refine ⟨actor * (swap * actor * swap⁻¹), hcentral, ?_⟩
    change (actor * (swap * actor * swap⁻¹)) • displacement swap (source : V) =
      displacement swap (destination : V)
    rw [hdiagonal source source.property, haction]

end Stellmacher.SectionOne
