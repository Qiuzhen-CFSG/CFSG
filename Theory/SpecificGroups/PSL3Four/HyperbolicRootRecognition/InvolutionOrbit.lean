module

public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.SourceConsumer

/-!
# Three explicit reflection words on the original involutions

In either surviving UT₃(F₄) word law, a singular quotient vector lies
in the first factor plane after one of the three words 1, β, βα. This
small square-map calculation transports through the actual marked normal
forms. The source application retains the original conjugators 1,b,ba;
no external fusion or unspecified orbit representative is assumed.
Source: Aschbacher, *Sporadic Groups* (1994), 45.3(4), printed p.243.
-/

public section
open Subgroup
namespace Theory.GroupTheory.HyperbolicRecognition

private theorem model_singular_orbit : ∀ (i : Fin 2) (v : Vector),
    quadratic (modelMatrix i) v = 0 →
      v.2 = 0 ∨ (reflectB (modelFrame i) v).2 = 0 ∨
        (reflectB (modelFrame i) (reflectA (modelFrame i) v)).2 = 0 := by
  decide +kernel

private theorem singular_orbit (M : Cross) (S T : Frame)
    (hS : FirstReflection M S) (hT : SecondReflection M T) (hM : TwoCases M)
    (v : Vector) (hv : quadratic M v = 0) :
    v.2 = 0 ∨ (reflectB T v).2 = 0 ∨ (reflectB T (reflectA S v)).2 = 0 := by
  rcases hM with rfl | rfl
  · obtain rfl := aligned_first_frame S hS
    obtain rfl := aligned_second_frame T hT
    exact model_singular_orbit 0 v hv
  · obtain rfl := crossed_first_frame S hS
    obtain rfl := crossed_second_frame T hT
    exact model_singular_orbit 1 v hv

/-- One of the literal three words 1, β, βα sends every element of square
one into the first original hyperbolic factor. -/
theorem involution_first_factor_orbit {K : Type*} [Group K]
    (F : HyperbolicFactors K) (P : HyperbolicFrame F.A F.z)
    (Q : HyperbolicFrame F.B F.u) (a : F.FirstActor) (b : F.SecondActor)
    (x : K) (hx : x^2=1) :
    x ∈ F.A ∨ b.aut x ∈ F.A ∨ b.aut (a.aut x) ∈ F.A := by
  let : Finite K := Nat.finite_of_card_ne_zero (by rw [F.card]; decide)
  obtain ⟨C⟩ := nonempty_markedCoordinates F P Q
  obtain ⟨S,hS,ha⟩ := C.first_reflection a
  obtain ⟨T,hT,hb⟩ := C.second_reflection b
  have hq : quadratic C.matrix (C.equiv x).vector = 0 := by
    apply (centralWord_eq_one C.matrix _).mp
    rw [←square_word,←map_pow,hx,map_one]
  have ho := singular_orbit C.matrix S T hS hT (C.twoCases a b) (C.equiv x).vector hq
  rw [C.first_mem,C.first_mem,C.first_mem,hb,hb,ha]
  exact ho

end Theory.GroupTheory.HyperbolicRecognition

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
open Theory.GroupTheory.HyperbolicRecognition
variable {G : Type*} [Group G] [Finite G] {z : G} (P : RootPair z)

/-- The source factor orbit uses actual core elements, with precisely the
ambient conjugators 1,b,ba. -/
theorem exists_involution_first_factor_words (h : IsType z) :
    ∃ a ∈ core z, ∃ b ∈ P.conjugateCore, ∀ x ∈ P.R, x^2=1 →
      x ∈ P.leftCore ∨ b*x*b⁻¹ ∈ P.leftCore ∨
        (b*a)*x*(b*a)⁻¹ ∈ P.leftCore := by
  obtain ⟨F₁,F₂⟩ := P.exists_hyperbolic_frames h
  obtain ⟨a,ha,b,hb,α,β,hα,hβ⟩ := P.exists_hyperbolic_actors_marked h
  refine ⟨a,ha,b,hb,?_⟩
  intro x hx hx2
  let xR : P.R := ⟨x,hx⟩
  have hxR : xR^2=1 := Subtype.ext hx2
  have ho := involution_first_factor_orbit (P.hyperbolicFactors h) F₁ F₂ α β xR hxR
  change (xR:G)∈P.leftCore ∨ (β.aut xR:G)∈P.leftCore ∨
    (β.aut (α.aut xR):G)∈P.leftCore at ho
  rw [hβ,hβ,hα] at ho
  have he : b*(a*x*a⁻¹)*b⁻¹=(b*a)*x*(b*a)⁻¹ := by group
  simpa only [xR,he] using ho

end Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
