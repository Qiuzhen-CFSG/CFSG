module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.QuadraticBound
public import CFSG.Quasithin.ChapterF.Section09.CriticalEndpoints

/-!
# The same critical endpoint and its moving denominator

The Chapter 13 critical path and the F.9 normalized endpoint use the same
coset graph. Comparing their first kernels turns the original terminal-edge
conjugator into an endpoint without changing any labels. A separate rank-nullity
argument shows that strict fixed codimension forces the critical denominator
to move the entire opposite central line.

Source: Aschbacher--Smith, F.9.10--13, printed pp.321--322, and the argument
following 14.6.24(b), printed p.1039, used in 14.6.24(4), p.1041.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open CriticalGeometry
variable {G : Type*} [Group G] [Finite G]

/-- A path-normalized critical pair is an F.9 endpoint with exactly its
original terminal-edge conjugator. No endpoint is independently chosen. -/
theorem f9_criticalPair_endpoint (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (c : CriticalPair D.L (D.T : Subgroup G) D.H D.V) (hb : 1 ≤ c.path.length) :
    ∃ i : h.CriticalEndpoint, i.representative = (c.gb : G) := by
  have hf : cosetFamily D.L (D.T : Subgroup G) D.H =
      ChapterF.Section07.Geometry.family D.LT D.H := by
    funext i
    cases i <;> rfl
  have hd := c.distance_eq.trans (c.length_eq.trans (f9_criticalDistance_eq D h))
  have he := SimpleGraph.length_eq_dist_of_subwalk c.distance_eq.symm
    (c.path.isSubwalk_drop 1)
  rw [SimpleGraph.Walk.drop_length, c.first] at he
  have hd' : (graph D.L (D.T : Subgroup G) D.H).dist
      (base _ _ _ true) c.gamma + 1 = h.b := by
    rw [← f9_criticalDistance_eq D h, ← c.length_eq]
    omega
  have hc : ¬ D.V.subgroupOf (G0 D.L (D.T : Subgroup G) D.H) ≤
      CosetGeometry.RankTwo.ballKernel (cosetFamily D.L (D.T : Subgroup G) D.H) c.gamma 1 := by
    intro hc
    exact c.critical ((le_firstKernel_iff _ _ _ _ (h.V_le_LT.trans le_sup_left) _).mpr hc)
  rw [← c.gb_one] at hd hd' hc
  change (CosetGeometry.RankTwo.graph (cosetFamily D.L (D.T : Subgroup G) D.H)).dist
    (CosetGeometry.base _ false) (c.gb • CosetGeometry.base _ true) = h.b at hd
  change (CosetGeometry.RankTwo.graph (cosetFamily D.L (D.T : Subgroup G) D.H)).dist
    (CosetGeometry.base _ true) (c.gb • CosetGeometry.base _ true) + 1 = h.b at hd'
  let g : (D.LT ⊔ D.H : Subgroup G) := ⟨c.gb.val,c.gb.property⟩
  let P (F : Bool → Subgroup (D.LT ⊔ D.H : Subgroup G)) : Prop :=
    (CosetGeometry.RankTwo.graph F).dist (CosetGeometry.base F false)
      (g • CosetGeometry.base F true) = h.b ∧
    (CosetGeometry.RankTwo.graph F).dist (CosetGeometry.base F true)
      (g • CosetGeometry.base F true) + 1 = h.b ∧
    ¬ D.V.subgroupOf (D.LT ⊔ D.H) ≤ CosetGeometry.RankTwo.ballKernel F
      (g • CosetGeometry.base F true) 1
  have hp : P (ChapterF.Section07.Geometry.family D.LT D.H) :=
    (congrArg P hf).mp ⟨hd,hd',hc⟩
  refine ⟨⟨g, hp.1, hp.2.1, ?_⟩, rfl⟩
  rw [h.f7Seed_eq]
  exact hp.2.2
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion


open Subgroup Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]

/-- Strict fixed codimension forces the denominator commutator to fill
the original order-two endpoint line. This is the movement step following
inequality (b) in 14.6.24. -/
theorem f9_denominator_commutator_eq_point {H U Z A C : Subgroup G}
    {ρ : Representation (ZMod 2) (Source.Hstar H) E}
    (s : ConjugationSection H U Z ρ) (hA : A ≤ H)
    (hUC : U ≤ normalizer (C : Set G)) (hC : Nat.card C = 2)
    (hstrict : Nat.log 2 ((Source.DH U A C).relIndex U) <
      fixedCodim ρ (Source.starImage H A)) :
    ⁅Source.DH U A C, A⁆ = C := by
  let D := Source.DH U A C
  have hc : ⁅D,A⁆ ≤ C := commutator_commutatorPreimage_le U A C hUC
  have hn : ¬ ⁅D,A⁆ ≤ Z := by
    intro hz
    have hfix : s.image D ≤ fixedSpace ρ (Source.starImage H A) := by
      intro v hv a
      obtain ⟨x,hx,rfl⟩ := (s.mem_image D v).mp hv
      obtain ⟨y,hy,he⟩ := a.property
      change ρ (a : Source.Hstar H) (s.quotient x).toAdd = (s.quotient x).toAdd
      rw [←he,←sub_eq_zero, s.displacement]
      apply (s.quotient_eq_zero_iff _).mpr
      exact (commutator_comm D A ▸ hz) (commutator_mem_commutator hy hx)
    have hdim := Submodule.finrank_mono hfix
    have hsum := fixedCodim_add_finrank ρ (Source.starImage H A)
    have hquot := (s.image D).finrank_quotient_add_finrank
    rw [s.quotient_finrank D (s.line_le_DH A C hA)] at hquot
    change Nat.log 2 (D.relIndex U) < fixedCodim ρ (Source.starImage H A) at hstrict
    omega
  have hdvd : Nat.card (⁅D,A⁆ : Subgroup G) ∣ 2 := hC ▸ card_dvd_of_le hc
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact (hn ((card_eq_one.mp h1).le.trans bot_le)).elim
  · exact eq_of_le_of_card_ge hc (by rw [hC,h2])
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
