module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic
public import Theory.Representation.SymplecticNatural.CubicFixedSpace
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The binary symplectic four-space exclusion

The source case G.11.2(2) is the actual natural action of
`Sp₄(2) ≃ S₆`.  A type-a2 involution is represented by three disjoint
transpositions.  The three-cycle on the three transposition-blocks commutes
with it and has no nonzero fixed vector on the binary natural module.  The
order-three moved-plane lemma in `Basic` therefore gives transitivity on the
three nonzero vectors of the moved plane.

The source's subgroup analysis is kept as an explicit input: it supplies an
actual subgroup/action equivalence and a nonidentity order-three member
centralizing the type-a2 element.  In particular, the divisibility alternatives
`10 ∣ |H|` and `18 ∣ |H|` are not silently replaced by a subgroup list or used
as an order-only recognition argument.  The caller that proves the G.11.2
alternatives must provide this corresponding centralizer member (or a conjugate
transported by the given model isomorphism).  The exported
`centralizing_order_three_of_factor` supplies that member from the source's
factor-three divisibility for the relevant centralizer.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
G.11.2(2), printed p.364 (PDF p.375), and the proof of 6.2.19, printed
p.691 (PDF p.708).
-/

@[expose] public section

namespace Representation.RankTwo.SpFour

open Theory.SpecificGroups.SymmetricSix
open scoped Matrix

abbrev F := ZMod 2
abbrev S6 := Equiv.Perm (Fin 6)
abbrev W := NaturalModule
abbrev Sp4 := Theory.SpecificGroups.SymplecticFour.Sp F

/-- The actual six-letter action on the binary symplectic module. -/
noncomputable def sixNatural : Representation F S6 W where
  toFun g := polarLinearMap g
  map_one' := by
    apply LinearMap.ext
    intro v
    exact polarAction_one v
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    exact polarAction_mul g h v

/-- The natural matrix representation of the actual group `Sp₄(2)`. -/
noncomputable def actualNatural : Representation F Sp4 W :=
  Representation.symplecticNatural 2

theorem actualNatural_equivariant (g : Sp4) (z : W) :
    actualNatural g z = sixNatural
      (Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm g) z := by
  change g.val *ᵥ z = polarAction
    (Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm g) z
  rw [← polarRepresentation_apply]
  rw [← Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv_apply]
  exact congrArg (fun x : Sp4 => x.val *ᵥ z)
    (Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.apply_symm_apply g).symm

/-- The explicit equivalence from the matrix group to the top six-letter
subgroup, retaining the concrete polar representation. -/
noncomputable def eTop : Sp4 ≃* (⊤ : Subgroup S6) where
  toFun g := ⟨Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm g, by simp⟩
  invFun h := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv h
  left_inv g := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.apply_symm_apply g
  right_inv h := by apply Subtype.ext; simp
  map_mul' g h := by apply Subtype.ext; simp

/-- An invariant quadratic form makes the actual a₂ moved plane singular.

This is the precise quadratic input used in the orthogonal subgroup branch:
the conclusion is only for the moved plane, and follows from its actual
symplectic polar form and invariance under the involution.
-/
theorem actual_movedSpace_quadratic_singular
    (v : Sp4) (horth : ∀ z : W,
      Theory.SpecificGroups.SymplecticFour.form F z (v • z) = 0)
    (q : QuadraticForm F W) (hqpolar : q.polarBilin =
      Theory.SpecificGroups.SymplecticFour.form F)
    (hq : ∀ z, q (v • z) = q z) :
    ∀ z ∈ movedSpace actualNatural v, q z = 0 := by
  rintro _ ⟨z, rfl⟩
  change q (v • z - z) = 0
  have hp : q.polarBilin z (v • z) = 0 := by
    rw [hqpolar]
    exact horth z
  have he : v • z - z = z + v • z := by
    ext i
    simp [sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  rw [he]
  simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hq,
    sub_sub, CharTwo.add_self_eq_zero, sub_zero] using hp

/-- A type-a2 representative in the six-letter model. -/
def a2 : S6 := Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5

/-- The rotation of the three transposition-blocks. -/
def cubic : S6 :=
  (Equiv.swap 0 2 * Equiv.swap 2 4) * (Equiv.swap 1 3 * Equiv.swap 3 5)

@[simp] theorem a2_sq : a2 ^ 2 = 1 := by
  decide +kernel

@[simp] theorem cubic_cube : cubic ^ 3 = 1 := by
  decide +kernel

/-- The block rotation centralizes the type-a2 representative. -/
theorem cubic_commutes_a2 : Commute cubic a2 := by
  change cubic * a2 = a2 * cubic
  decide +kernel

private def pairedMap (i j k : Fin 6) : Fin 6 → Fin 6 :=
  ![i, a2 i, j, a2 j, k, a2 k]

private theorem pairedMap_test : ∀ i j k : Fin 6,
    (∀ x, pairedMap i j k (pairedMap i j k (pairedMap i j k x)) = x) →
    (∃ x, pairedMap i j k x ≠ x) →
    ∀ d : Duad, (duadSet d).image (pairedMap i j k) ≠ duadSet d := by
  decide +kernel

private theorem pairedMap_eq (c : S6) (hc : Commute c a2) :
    (c : Fin 6 → Fin 6) = pairedMap (c 0) (c 2) (c 4) := by
  have h (i : Fin 6) := congrArg (fun g : S6 => g i) hc.eq
  funext i
  fin_cases i
  · rfl
  · exact h 0
  · rfl
  · exact h 2
  · rfl
  · exact h 4

private theorem centralizing_order_three_fixed_free {c : S6}
    (hc : c ^ 3 = 1) (hc1 : c ≠ 1) (hcomm : Commute c a2) :
    ∀ z : W, sixNatural c z = z → z = 0 := by
  intro z hz
  by_cases hz0 : z = 0
  · exact hz0
  obtain ⟨d, hd⟩ := polarVector_bijective.2 ⟨z, hz0⟩
  have hpoint : polarVector (c • d) = polarVector d := by
    apply Subtype.ext
    rw [← polarAction_vector, hd]
    exact hz
  have hduad : c • d = d := polarVector_injective hpoint
  have hs := congrArg duadSet hduad
  rw [duadSet_smul] at hs
  have ht : ∀ x, c (c (c x)) = x := by
    intro x
    exact congrArg (fun g : S6 => g x) hc
  have hn : ∃ x, c x ≠ x := by
    by_contra! hn
    apply hc1
    apply (_root_.Equiv.ext (α := Fin 6) (β := Fin 6))
    intro x
    exact hn x
  rw [pairedMap_eq c hcomm] at ht hn hs
  exact (pairedMap_test (c 0) (c 2) (c 4) ht hn d hs).elim

/-- The actual cubic has no nonzero fixed vector on the natural module. -/
theorem cubic_fixed_free : ∀ z : W, sixNatural cubic z = z → z = 0 := by
  exact centralizing_order_three_fixed_free (c := cubic) cubic_cube (by decide)
    cubic_commutes_a2

/-- The exact subgroup output needed from the G.11.2(2) analysis.

`order_divisibility` records the source alternatives (10 or 18), while
`centralizing_order_three` is the concrete subgroup-analysis output used to
rotate the three nonzero vectors of the moved plane.  Keeping both fields
prevents an order divisibility hypothesis from being mistaken for the
subgroup-action calculation itself.
-/
structure SubgroupAnalysis (H : Subgroup S6) : Prop where
  order_divisibility : 10 ∣ Nat.card H ∨ 18 ∣ Nat.card H
  a2_mem : a2 ∈ H
  centralizing_order_three : ∃ c : H, c ^ 3 = 1 ∧ c ≠ 1 ∧
    Commute (c : S6) a2

/-- The centralizer in a subgroup of the fixed type-a2 representative. -/
noncomputable def centralizerIn (H : Subgroup S6) (hA : a2 ∈ H) : Subgroup H :=
  Subgroup.centralizer ({(⟨a2, hA⟩ : H)} : Set H)

/-- Cauchy's theorem turns the source factor of three in this centralizer into
the order-three actor used by the moved-plane argument. -/
theorem centralizing_order_three_of_factor {H : Subgroup S6} (hA : a2 ∈ H)
    (hthree : 3 ∣ Nat.card (centralizerIn H hA)) :
    ∃ c : H, c ^ 3 = 1 ∧ c ≠ 1 ∧ Commute (c : S6) a2 := by
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 hthree
  let cH : H := c.1
  have hcpow := congrArg Subtype.val (pow_orderOf_eq_one c)
  change cH ^ orderOf c = 1 at hcpow
  have hc3 : cH ^ 3 = 1 := by
    rw [← hc]
    exact hcpow
  have hc1 : cH ≠ 1 := by
    intro h
    have hc1c : c = 1 := by exact Subtype.ext h
    subst hc1c
    simp at hc
  have hmem := c.property
  have hcomm : Commute cH (⟨a2, hA⟩ : H) := by
    exact ((Subgroup.mem_centralizer_iff.mp hmem) _ (by simp)).symm
  refine ⟨cH, hc3, hc1, ?_⟩
  exact congrArg Subtype.val hcomm.eq

/-- Package the literal order alternatives and the factor-three output. -/
theorem subgroupAnalysis_of_factor {H : Subgroup S6}
    (horder : 10 ∣ Nat.card H ∨ 18 ∣ Nat.card H) (hA : a2 ∈ H)
    (hthree : 3 ∣ Nat.card (centralizerIn H hA)) : SubgroupAnalysis H :=
  ⟨horder, hA, centralizing_order_three_of_factor hA hthree⟩

/-- The full six-letter group supplies the source witness explicitly. -/
theorem topAnalysis : SubgroupAnalysis (⊤ : Subgroup S6) where
  order_divisibility := by
    right
    norm_num [S6, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  a2_mem := by simp
  centralizing_order_three := by
    let c : (⊤ : Subgroup S6) := ⟨cubic, by simp⟩
    refine ⟨c, ?_, ?_, ?_⟩
    · apply Subtype.ext
      exact cubic_cube
    · intro h
      apply (by decide : cubic ≠ 1)
      exact congrArg Subtype.val h
    · exact cubic_commutes_a2

private theorem commute_subtype {H : Subgroup S6} {c v : H}
    (hcomm : Commute (c : S6) (v : S6)) : Commute c v := by
  apply Subtype.ext
  change (c : S6) * (v : S6) = (v : S6) * (c : S6)
  exact hcomm.eq

theorem stabilizerTransitive_of_subgroup_element
    {H : Subgroup S6} (v c : H) (hrank : Module.finrank F
      (movedSpace (sixNatural.comp H.subtype) v) = 2)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hcommA : Commute (c : S6) a2)
    (hcomm : Commute (c : S6) (v : S6)) :
    StabilizerTransitive (sixNatural.comp H.subtype)
      (movedSpace (sixNatural.comp H.subtype) v) := by
  apply stabilizerTransitive_of_order_three
    (sixNatural.comp H.subtype) v c hrank
    (commute_subtype hcomm)
  · exact hc3
  · intro z _ hz
    have hc3' : (c : S6) ^ 3 = 1 := congrArg Subtype.val hc3
    change sixNatural (c : S6) z = z at hz
    exact centralizing_order_three_fixed_free (c := (c : S6)) hc3'
      (fun h => hc1 (Subtype.ext h)) hcommA z hz

/-- The concrete S₆ calculation, after the subgroup analysis has supplied the
actual centralizing order-three member.  The rank-two hypothesis is the
source's type-a2 hypothesis.
-/
theorem stabilizerTransitive_of_subgroup
    {H : Subgroup S6} (analysis : SubgroupAnalysis H)
    (v : H) (hv : (v : S6) = a2)
    (hrank : Module.finrank F
      (movedSpace (sixNatural.comp H.subtype) v) = 2) :
    StabilizerTransitive (sixNatural.comp H.subtype)
      (movedSpace (sixNatural.comp H.subtype) v) := by
  obtain ⟨c, hc3, hc1, hcomm⟩ := analysis.centralizing_order_three
  have hcommv : Commute (c : S6) (v : S6) := by
    rw [hv]
    exact hcomm
  apply stabilizerTransitive_of_subgroup_element v c hrank hc3 hc1 hcomm hcommv

/-- Direct source-facing form when the subgroup analysis has produced the
factor-three centralizer divisibility. -/
theorem stabilizerTransitive_of_subgroup_factor
    {H : Subgroup S6} (horder : 10 ∣ Nat.card H ∨ 18 ∣ Nat.card H)
    (hA : a2 ∈ H) (hthree : 3 ∣ Nat.card (centralizerIn H hA))
    (v : H) (hv : (v : S6) = a2)
    (hrank : Module.finrank F
      (movedSpace (sixNatural.comp H.subtype) v) = 2) :
    StabilizerTransitive (sixNatural.comp H.subtype)
      (movedSpace (sixNatural.comp H.subtype) v) :=
  stabilizerTransitive_of_subgroup (subgroupAnalysis_of_factor horder hA hthree)
    v hv hrank

/-- Transport the concrete S₆ subgroup calculation to an actual group and its
actual binary module.  The intertwining equation is the required symplectic
model equivalence; group-name equality alone is insufficient.
-/
theorem stabilizerTransitive_of_actual_model
    {G V : Type*} [Group G] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (ρ : Representation F G V)
    {H : Subgroup S6} (analysis : SubgroupAnalysis H)
    (e : G ≃* H) (f : V ≃ₗ[F] W)
    (hf : ∀ g z, f (ρ g z) = sixNatural (e g) (f z))
    (v : G) (hv : (e v : S6) = a2)
    (hrank : Module.finrank F (movedSpace ρ v) = 2) :
    StabilizerTransitive ρ (movedSpace ρ v) := by
  let σ : Representation F H W := sixNatural.comp H.subtype
  have hσ (g : G) (z : V) :
      f (ρ g z) = σ (e g) (f z) := by
    change f (ρ g z) = sixNatural (e g) (f z)
    exact hf g z
  have hve : (e v : H) = ⟨a2, analysis.a2_mem⟩ := by
    apply Subtype.ext
    exact hv
  have hrank' : Module.finrank F (movedSpace σ (e v)) = 2 := by
    rw [← finrank_movedSpace_transport ρ σ e f hσ v]
    exact hrank
  have hσtrans := stabilizerTransitive_of_subgroup analysis (e v)
    (congrArg Subtype.val hve) hrank'
  exact stabilizerTransitive_transport ρ σ e f hσ v hσtrans

/-- Source-facing wrapper retaining the literal G.11.2 divisibility alternatives. -/
theorem stabilizerTransitive_of_G112_case
    {G V : Type*} [Group G] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (ρ : Representation F G V)
    {H : Subgroup S6} (analysis : SubgroupAnalysis H)
    (e : G ≃* H) (f : V ≃ₗ[F] W)
    (hf : ∀ g z, f (ρ g z) = sixNatural (e g) (f z))
    (v : G) (hv : (e v : S6) = a2)
    (hrank : Module.finrank F (movedSpace ρ v) = 2) :
    StabilizerTransitive ρ (movedSpace ρ v) :=
  stabilizerTransitive_of_actual_model ρ analysis e f hf v hv hrank

/-- The same conclusion specialized to the actual natural matrix action of
`Sp₄(2)`, with the full six-letter subgroup analysis. -/
theorem stabilizerTransitive_of_actual_sp
    (v : Sp4) (hv : (eTop v : S6) = a2)
    (hrank : Module.finrank F (movedSpace actualNatural v) = 2) :
    StabilizerTransitive actualNatural (movedSpace actualNatural v) := by
  apply stabilizerTransitive_of_actual_model actualNatural topAnalysis eTop
    (LinearEquiv.refl F W) (fun g z => ?_) v hv hrank
  exact actualNatural_equivariant g z

end Representation.RankTwo.SpFour
