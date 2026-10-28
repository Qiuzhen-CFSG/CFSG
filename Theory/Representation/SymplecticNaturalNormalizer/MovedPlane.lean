module
public import Theory.Representation.SymplecticNaturalNormalizer.FixedLineInner
public import Theory.Representation.SymplecticConjugatePair.Ambient.Semilinear
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry

/-!
# Moved-plane transitivity for nonbinary natural symplectic four-space

The actual binary normalizer is semilinear over the coefficient field.
A nontrivial field involution moves half the binary space, so a rank-two
involution is field-linear. Its moved plane is then a coefficient-field line.
The normal symplectic component carries any nonzero vector of that line to
any other and consequently preserves the line. Thus its stabilizer acts
transitively on the original binary moved plane.

The Chapter G consumer applies this after genuine natural-module recognition.
Source: Aschbacher--Smith G.11.7 and 6.2.19, printed pp.367,691;
the coefficient-field normalizer argument is H.7, pp.388--389.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair.Ambient
namespace SymplecticNaturalNormalizer
variable {F G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group G]

/-- A rank-two involution on a nonbinary natural four-space is field-linear;
its moved plane is a field line, whose component stabilizer is transitive. -/
theorem stabilizerTransitive_of_rank_two
    (ρ : Representation (ZMod 2) G (Vector F))
    (L : Subgroup G) [L.Normal] (e : L ≃* Sp F)
    (hL : ∀ l : L, ∀ w, ρ (l:G) w = symplecticNatural 2 (e l) w)
    {n : ℕ} (hn : 2≤n) (hF : Nat.card F=2^n)
    (a : G) (ha : a^2=1)
    (hr : finrank (ZMod 2) (RankTwo.movedSpace ρ a)=2) :
    RankTwo.StabilizerTransitive ρ (RankTwo.movedSpace ρ a) := by
  have hcard : 2<Nat.card F := by
    rw [hF]
    have hh := Nat.pow_le_pow_right (by decide : 0<2) hn
    omega
  have hfd : finrank (ZMod 2) F=n :=
    Nat.pow_right_injective (by decide : 1<2)
      ((FiniteField.pow_finrank_eq_natCard 2 F).trans hF)
  have hdim : finrank (ZMod 2) (Vector F)=n*4 := by
    rw [←Module.finrank_mul_finrank (ZMod 2) F,hfd]
    simp [Theory.SpecificGroups.SymplecticFour.Vector]
  obtain ⟨σ,hσ⟩ := exists_field_twist
    ⟨linearAction ρ a,operator_mem_naturalNormalizer L hcard e ρ hL a⟩
  change ∀ (c:F) w, ρ a (c • w)=σ c • ρ a w at hσ
  have haa (w : Vector F) : ρ a (ρ a w)=w := by
    rw [←Module.End.mul_apply,←map_mul,←pow_two,ha,map_one,Module.End.one_apply]
  have hσ2 : Function.Involutive σ := by
    obtain ⟨w,hw⟩ := exists_ne (0 : Vector F)
    intro c
    apply smul_left_injective F hw
    have hh := haa (c • w)
    rwa [hσ,hσ,haa] at hh
  have hσ1 : σ=RingEquiv.refl F := by
    by_contra hne
    have hh := semilinear_involution_twice_codim ρ a ha σ hσ2 hne hσ
    rw [fixedCodim_zpowers_eq_displacement_rank] at hh
    change 2*finrank (ZMod 2) (RankTwo.movedSpace ρ a)=_ at hh
    rw [hr,hdim] at hh
    omega
  have hlin (c:F) (w:Vector F) : ρ a (c • w)=c • ρ a w := by
    simpa only [hσ1,RingEquiv.refl_apply] using hσ c w
  let T : Module.End F (Vector F) :=
    { toFun := ρ a, map_add' := (ρ a).map_add, map_smul' := hlin }
  let P := (T-1).range
  have hP : P.restrictScalars (ZMod 2)=RankTwo.movedSpace ρ a := by
    ext w
    rfl
  have hPd : finrank F P=1 := by
    have hh : finrank (ZMod 2) P=2 := by
      have hh := ((P.restrictScalarsEquiv (ZMod 2)).restrictScalars (ZMod 2)).finrank_eq.symm
      rw [hP] at hh
      exact hh.trans hr
    rw [←Module.finrank_mul_finrank (ZMod 2) F,hfd] at hh
    nlinarith
  intro u hu hu0 w hw hw0
  have huP : u∈P := by
    change u∈P.restrictScalars (ZMod 2)
    rwa [hP]
  have hwP : w∈P := by
    change w∈P.restrictScalars (ZMod 2)
    rwa [hP]
  have hspan (z : Vector F) (hz : z∈P) (hz0 : z≠0) : P=Submodule.span F {z} := by
    apply (Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (by simpa using hz)) ?_).symm
    rw [finrank_span_singleton hz0,hPd]
  obtain ⟨g,hg⟩ := TwoLocalCover.nonzero_vector_transitive hu0 hw0
  let l := e.symm g
  have hlu : ρ (l:G) u=w := by
    rw [hL,e.apply_symm_apply]
    exact hg
  have hll (c:F) (z:Vector F) : ρ (l:G) (c • z)=c • ρ (l:G) z := by
    rw [hL,hL,map_smul]
  have hpres : ∀ z∈P,ρ (l:G) z∈P := by
    intro z hz
    rw [hspan u huP hu0,Submodule.mem_span_singleton] at hz
    obtain ⟨c,rfl⟩ := hz
    rw [hll,hlu]
    exact P.smul_mem c hwP
  have hpre (z : Vector F) (hz : ρ (l:G) z∈P) : z∈P := by
    rw [hspan w hwP hw0,Submodule.mem_span_singleton] at hz
    obtain ⟨c,hc⟩ := hz
    have hz : z=c • u := (ρ.apply_bijective (l:G)).1 (by rw [hll,hlu];exact hc.symm)
    rw [hz]
    exact P.smul_mem c huP
  exact ⟨l,fun z => by
    change z∈P.restrictScalars (ZMod 2) ↔ _
    constructor
    · exact hpres z
    · exact hpre z,hlu⟩
end SymplecticNaturalNormalizer

