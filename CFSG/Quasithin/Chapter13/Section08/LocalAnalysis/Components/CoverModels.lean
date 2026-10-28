module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Models
public import Theory.Alternating.theorem_5_2_3
public import Theory.Mathieu.M22.TripleCover.Recognition
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Mathlib.Algebra.Group.Shrink

/-!
# Comparisons with the component carriers

Trivial center identifies a group with its central quotient. For Â₆ the
proved cyclic multiplier of A₆ gives uniqueness of triple covers, which
identifies the source's intrinsic notation with the actual hexacode group.
The binary matrix core supplies a genuine perfect M₂₂ triple cover. The
proved three-primary kernel bound identifies every source triple cover
with that same carrier, without requiring the full multiplier calculation.
The cyclic-multiplier comparison remains available as a general helper.

The symplectic comparison uses the characteristic-two scalar-center
calculation, including at the small derived endpoint. No exceptional
isomorphism replaces a commutator carrier.

Source: Aschbacher–Smith A.3.5–6, p.43, I.1.3, p.407, F.9.18(4),
pp.325–326, H.12, pp.393–394, and 13.8.17, p.953; GLS3,
Theorem 5.2.3(c).
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.Chapter13.Section08.Components.CoverModels
open Subgroup Theory.GroupTheory
open Chapter1.Section02.LocalModels Models
universe u v

/-- Identification with the actual quotient when the source proves trivial center. -/
def centerQuotientEquiv {G : Type u} [Group G] (hz : center G = ⊥) :
    G ≃* G ⧸ center G :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hz.symm)

/-- A perfect simple component has trivial center. -/
theorem center_eq_bot_of_simple {G : Type u} [Group G]
    [IsSimpleGroup G] [Group.IsPerfect G] : center G = ⊥ := by
  rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact False.elim (Group.IsPerfect.not_isMulCommutative G (center_eq_top_iff.mp h))

/-- All centerless branches of F.9.18 lift to actual component models. -/
theorem lift_centerless {G : Type u} [Group G] (hz : center G = ⊥)
    (h : F918QuotientModel (G ⧸ center G)) : ComponentModelOrSuzuki G := by
  let e := centerQuotientEquiv hz
  cases h with
  | bender iso =>
      cases iso with
      | linear n hn iso => exact Or.inl (.linear_two n hn (iso.of_mulEquiv e))
      | unitary n hn iso => exact Or.inl (.projective_three true n hn (iso.of_mulEquiv e))
      | suzuki m hm iso => exact Or.inr ⟨m, hm, iso.map (e.trans ·)⟩
  | linear_three n hn iso =>
      exact Or.inl (.projective_three false n hn (iso.of_mulEquiv e))
  | symplectic n hn iso => exact Or.inl (.symplectic n hn (iso.of_mulEquiv e))
  | g2 n hn iso => exact Or.inl (.g2 n hn (iso.of_mulEquiv e))
  | linear_four iso => exact Or.inl (.linear_four (iso.of_mulEquiv e))
  | linear_five iso => exact Or.inl (.linear_five (iso.of_mulEquiv e))
  | alternating_seven iso => exact Or.inl (.alternating_seven (iso.map (e.trans ·)))

/-- A genuine A.3.5 cover has center of order three. -/
theorem threeCover_center_card {G : Type u} [Group G] {S : Type} [Group S]
    (h : IsThreeCover G S) : Nat.card (center G) = 3 := by
  obtain ⟨e⟩ := h.2.1
  exact (Nat.card_congr e.toEquiv).trans (Nat.card_zmod 3)

/-- The hexacode carrier satisfies the intrinsic cover notation in A.3.5. -/
theorem a6Triple_isThreeCover : IsAlternatingCover A6Triple 6 := by
  refine ⟨Representation.Hexacode.even_isQuasisimple, ?_,
    ⟨Representation.Hexacode.even_quotient_center_equiv⟩⟩
  exact ⟨mulEquivOfPrimeCardEq Representation.Hexacode.even_center_card (Nat.card_zmod 3)⟩

/-- Its center is the three-element scalar subgroup, not an added direct factor. -/
theorem m22Triple_center_card : Nat.card (center M22Triple) = 3 := by
  rw [Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel.center_derivedGroup_eq_zpowers,
    Nat.card_zpowers]
  exact orderOf_eq_prime_iff.mpr
    ⟨Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel.coreScalar_pow_three,
      Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel.coreScalar_ne_one⟩

/-- The chosen M̂₂₂ carrier is perfect unconditionally. -/
theorem m22Triple_isPerfect : Group.IsPerfect M22Triple := inferInstance

/-- The already proved action comparison for the chosen M̂₂₂ carrier. -/
def m22Triple_quotientCenterEquiv :
    M22Triple ⧸ center M22Triple ≃* Sporadic.Mathieu.M22 :=
  Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel.derivedQuotientEquivM22

/-- Source simplicity is enough to certify quasisimplicity of the fixed carrier. -/
theorem m22Triple_isQuasisimple [IsSimpleGroup Sporadic.Mathieu.M22] :
    IsQuasisimple M22Triple where
  toIsPerfect := m22Triple_isPerfect
  simple := m22Triple_quotientCenterEquiv.isSimpleGroup

/-- The actual matrix carrier realizes the source's intrinsic M̂₂₂ notation. -/
theorem m22Triple_isThreeCover [IsSimpleGroup Sporadic.Mathieu.M22] :
    IsM22Cover M22Triple := by
  refine ⟨m22Triple_isQuasisimple, ?_, ⟨m22Triple_quotientCenterEquiv⟩⟩
  exact ⟨mulEquivOfPrimeCardEq m22Triple_center_card (Nat.card_zmod 3)⟩

/-- Intrinsic A₆ triple covers are isomorphic to the fixed hexacode carrier.
The multiplier and both cover constructions are proved upstream. -/
theorem a6Triple_nonempty_mulEquiv {G : Type u} [Group G] [Finite G]
    (h : IsAlternatingCover G 6) : Nonempty (G ≃* A6Triple) := by
  let : IsQuasisimple G := h.1
  let : IsQuasisimple A6Triple := Representation.Hexacode.even_isQuasisimple
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨e⟩ := h.2.2
  let r : Shrink.{0} G ≃* G := Shrink.mulEquiv
  let : Finite (Shrink.{0} G) := Finite.of_equiv G r.toEquiv.symm
  let : IsQuasisimple (Shrink.{0} G) := IsQuasisimple.of_mulEquiv r.symm
  let f : Covering (Shrink.{0} G) (alternatingGroup (Fin 6)) := {
    toMonoidHom := e.toMonoidHom.comp ((QuotientGroup.mk' (center G)).comp r.toMonoidHom)
    surjective := e.surjective.comp ((QuotientGroup.mk'_surjective _).comp r.surjective) }
  let g : Covering A6Triple (alternatingGroup (Fin 6)) := {
    toMonoidHom := Atlas.Codes.hexEvenCoordinate
    surjective := Atlas.Codes.hexEvenCoordinate_surjective }
  have hf : Nat.card f.toMonoidHom.ker = 3 := by
    rw [f.ker_eq_center_of_isSimple]
    exact (Nat.card_congr (centerCongr r).toEquiv).trans (threeCover_center_card h)
  have hg : Nat.card g.toMonoidHom.ker = 3 := by
    rw [g.ker_eq_center_of_isSimple]
    exact Representation.Hexacode.even_center_card
  obtain ⟨U, hU, hfin, hquasi, c, hc, hcyc, hcard⟩ :=
    GLS3.Chapter5.SchurPresentation.theorem_5_2_3_c_multiplier_a6
  let : Group U := hU
  let : Finite U := hfin
  let : IsQuasisimple U := hquasi
  obtain ⟨a, _, _⟩ :=
    GLS3.Chapter5.SchurPresentation.coveringIso_of_cyclic_kernel_card_six_of_kernel_card_three
      c hc hcyc hcard f g hf hg
  exact ⟨r.symm.trans a⟩

private theorem cyclic_subgroups_eq_of_card {C : Type*} [Group C] [Finite C]
    [hC : IsCyclic C] (A B : Subgroup C) (hcard : Nat.card A = Nat.card B) : A = B := by
  let : CommGroup C := hC.commGroup
  have heq (D : Subgroup C) : D = (powMonoidHom (Nat.card D) : C →* C).ker := by
    apply eq_of_le_of_card_ge
    · intro x hx
      exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : D)))
    · rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right D.card_subgroup_dvd_card]
  rw [heq A, heq B, hcard]

/-- Equal-order covers of a common base are identified by their kernels in a
universal cover with cyclic multiplier. Only cyclicity, not its full order, is used. -/
theorem covers_nonempty_mulEquiv_of_cyclic_multiplier
    {U S A B : Type} [Group U] [Finite U] [IsQuasisimple U]
    [Group S] [Finite S] [IsQuasisimple S]
    [Group A] [Finite A] [IsQuasisimple A]
    [Group B] [Finite B] [IsQuasisimple B]
    (c : Covering U S) (hc : Covering.IsUniversal.{0, 0, 0} c)
    (hcyc : IsCyclic c.toMonoidHom.ker)
    (a : Covering A S) (b : Covering B S)
    (hcard : Nat.card a.toMonoidHom.ker = Nat.card b.toMonoidHom.ker) :
    Nonempty (A ≃* B) := by
  let f := hc.lift a
  let g := hc.lift b
  have hf : a.toMonoidHom.comp f.toMonoidHom = c.toMonoidHom :=
    congrArg Covering.toMonoidHom (hc.lift_fac a)
  have hg : b.toMonoidHom.comp g.toMonoidHom = c.toMonoidHom :=
    congrArg Covering.toMonoidHom (hc.lift_fac b)
  have hfc : a.toMonoidHom.ker.comap f.toMonoidHom = c.toMonoidHom.ker := by
    rw [MonoidHom.comap_ker, hf]
  have hgc : b.toMonoidHom.ker.comap g.toMonoidHom = c.toMonoidHom.ker := by
    rw [MonoidHom.comap_ker, hg]
  have hf_le : f.toMonoidHom.ker ≤ c.toMonoidHom.ker := by
    rw [← hfc]
    exact MonoidHom.ker_le_comap _ _
  have hg_le : g.toMonoidHom.ker ≤ c.toMonoidHom.ker := by
    rw [← hgc]
    exact MonoidHom.ker_le_comap _ _
  have hfg : Nat.card f.toMonoidHom.ker = Nat.card g.toMonoidHom.ker := by
    have h1 := GLS3.Chapter5.SchurPresentation.card_comap_mul
      f.toMonoidHom f.surjective a.toMonoidHom.ker
    have h2 := GLS3.Chapter5.SchurPresentation.card_comap_mul
      g.toMonoidHom g.surjective b.toMonoidHom.ker
    rw [hfc, hcard] at h1
    rw [hgc] at h2
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := b.toMonoidHom.ker))
      (h1.symm.trans h2)
  let : IsCyclic c.toMonoidHom.ker := hcyc
  have he : f.toMonoidHom.ker.subgroupOf c.toMonoidHom.ker =
      g.toMonoidHom.ker.subgroupOf c.toMonoidHom.ker := by
    apply cyclic_subgroups_eq_of_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hf_le).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hg_le).toEquiv, hfg]
  have hk : f.toMonoidHom.ker = g.toMonoidHom.ker := by
    have hh := congrArg (Subgroup.map c.toMonoidHom.ker.subtype) he
    simpa only [map_subgroupOf_eq_of_le hf_le, map_subgroupOf_eq_of_le hg_le] using hh
  obtain ⟨e, _, _⟩ := GLS3.Chapter5.Covering.coveringIso_of_liftKernel_eq c hc hc a b hk
  exact ⟨e⟩

/-- The cyclicity input retained by the original comparison API.
The direct source triple-cover recognition below does not require it. -/
def M22CyclicMultiplierInput : Prop :=
  ∀ [IsQuasisimple Sporadic.Mathieu.M22],
    IsCyclic (PerfectCentralCovering.universalQuasisimpleCover
      Sporadic.Mathieu.M22).toMonoidHom.ker

/-- Every source M₂₂ triple cover is the fixed matrix carrier, by the proved
three-primary cover recognition. The original central-quotient marking is used. -/
theorem m22Triple_nonempty_mulEquiv_of_source {G : Type u} [Group G] [Finite G]
    (h : IsM22Cover G) : Nonempty (G ≃* M22Triple) := by
  let : IsQuasisimple G := h.1
  exact Sporadic.Mathieu.M22TripleCover.nonempty_mulEquiv
    (threeCover_center_card h) h.2.2

/-- Compatibility with the original cyclic-multiplier comparison API. -/
theorem m22Triple_nonempty_mulEquiv {G : Type u} [Group G] [Finite G]
    (h : IsM22Cover G) (hI : M22CyclicMultiplierInput) :
    Nonempty (G ≃* M22Triple) := by
  have _ : M22CyclicMultiplierInput := @hI
  exact m22Triple_nonempty_mulEquiv_of_source h

/-- The remaining comparison between the A.3.6 classical cover parameters
and the F.9.18 quotient list. This is an explicit unfinished input, not a
classification theorem. In particular it must exclude odd-prime parameters. -/
def ClassicalCoverParameters (G : Type u) [Group G] : Prop :=
  ∀ (unitary : Bool) (q : ℕ), CoverParameter unitary q →
    Nonempty (center G ≃* Multiplicative (ZMod 3)) → IsSLSign G unitary 3 q →
    F918QuotientModel (G ⧸ center G) →
    ∃ n : ℕ, ThreeParameter unitary n ∧ q = 2 ^ n ∧
      (2 ^ n) % 3 = if unitary then 2 else 1

/-- Assembly from the genuine earlier classification clauses.
Triple-cover recognition is discharged; the classical parameter comparison
and F.9.18 remain explicit. This is not an assertion of all of 13.8.17. -/
theorem lift_classified_of_source {G : Type u} [Group G] [Finite G] [IsQuasisimple G]
    (hF : F918Models G)
    (hA : IsSimpleGroup G ∨
      (Nonempty (center G ≃* Multiplicative (ZMod 3)) ∧ ThreeCoverModel G))
    (hparameters : ClassicalCoverParameters G) :
    ComponentModelOrSuzuki G := by
  rcases hF with ⟨hquot, hno7⟩ | hmathieu | hcover
  · rcases hA with hs | ⟨hz, hcover⟩
    · let : IsSimpleGroup G := hs
      exact lift_centerless center_eq_bot_of_simple hquot
    · cases hcover with
      | classical unitary q hq iso =>
          obtain ⟨n, hn, rfl, hm⟩ := hparameters unitary q hq hz iso hquot
          exact Or.inl (.special_three unitary n hn hm iso)
      | alternating_six iso =>
          exact Or.inl (.alternating_six_cover (a6Triple_nonempty_mulEquiv iso))
      | alternating_seven iso => exact False.elim (hno7 iso)
      | mathieu iso => exact Or.inl (.mathieu_cover (m22Triple_nonempty_mulEquiv_of_source iso))
  · exact Or.inl (.mathieu hmathieu)
  · exact Or.inl (.mathieu_cover (m22Triple_nonempty_mulEquiv_of_source hcover))

/-- Compatibility with the original assembly API, retaining every source
hypothesis and the original cyclic-multiplier parameter. -/
theorem lift_classified {G : Type u} [Group G] [Finite G] [IsQuasisimple G]
    (hF : F918Models G)
    (hA : IsSimpleGroup G ∨
      (Nonempty (center G ≃* Multiplicative (ZMod 3)) ∧ ThreeCoverModel G))
    (hI : M22CyclicMultiplierInput) (hparameters : ClassicalCoverParameters G) :
    ComponentModelOrSuzuki G := by
  have _ : M22CyclicMultiplierInput := @hI
  exact lift_classified_of_source hF hA hparameters

/-- The characteristic-two quotient comparison also identifies the two derived carriers. -/
def symplecticDerivedEquiv (F : Type) [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) :
    commutator (Matrix.symplecticGroup (Fin 2) F) ≃*
      commutator (ClassicalGroup.PSp 2 F) := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let e : Matrix.symplecticGroup (Fin 2) F ≃* ClassicalGroup.PSp 2 F :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  rfl

end CFSG.Quasithin.Chapter13.Section08.Components.CoverModels
