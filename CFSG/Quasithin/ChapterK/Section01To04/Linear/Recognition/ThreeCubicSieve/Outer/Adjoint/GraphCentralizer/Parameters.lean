module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.Forms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Recovering the elementary actor parameter from its operators

The root shears and the graph operator obey the additive law on `F × ZMod 2`.
Their values on coordinate vectors determine both parameters, including over
F₂. Thus pointwise simultaneous operator forms yield a homomorphism; faithfulness
of the original action makes it injective. A marked graph actor has parameter
`(0,1)`. This constructs every field of `GraphForm` once matrix root placement
has supplied the pointwise identities.

Source: the graph-centralizer calculation in Guralnick–Malle, Classification
of 2F-modules II, Proposition 4.8, step 3A, author manuscript p.27.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer
variable (F : Type*) [Field F] [CharP F 2]

def operator (p : F × ZMod 2) (v : Eight F) : Eight F :=
  shearCoordinates F p.1 (if p.2 = 0 then v else graphCoordinates F v)

lemma shear_add (a b : F) (v : Eight F) :
    shearCoordinates F (a + b) v = shearCoordinates F a (shearCoordinates F b v) := by
  funext i
  fin_cases i <;> simp [shearCoordinates, CharTwo.add_sq] <;> ring_nf
  all_goals simp [CharTwo.two_eq_zero]

omit [CharP F 2] in
lemma graph_shear (a : F) (v : Eight F) :
    graphCoordinates F (shearCoordinates F a v) =
      shearCoordinates F a (graphCoordinates F v) := by
  funext i
  fin_cases i <;> simp [shearCoordinates, graphCoordinates, add_comm]

omit [Field F] [CharP F 2] in
lemma graph_graph (v : Eight F) : graphCoordinates F (graphCoordinates F v) = v := by
  funext i
  fin_cases i <;> rfl

omit [CharP F 2] in
lemma operator_zero (v : Eight F) : operator F 0 v = v := by simp [operator]

omit [CharP F 2] in
lemma operator_graph (v : Eight F) : operator F (0,1) v = graphCoordinates F v := by
  simp [operator]

lemma operator_add (p q : F × ZMod 2) (v : Eight F) :
    operator F (p + q) v = operator F p (operator F q v) := by
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  have bits (b : ZMod 2) : b = 0 ∨ b = 1 := by
    fin_cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases bits b with rfl | rfl <;> rcases bits d with rfl | rfl <;>
    simp [operator, shear_add, graph_shear, graph_graph, CharTwo.add_self_eq_zero]

omit [CharP F 2] in
/-- The literal simultaneous operator determines both the root parameter and
the graph bit, even over the smallest binary field. -/
theorem operator_injective : Function.Injective (operator F) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have hb := congrFun (congrFun h (Pi.single 4 1)) 3
  have h0 := congrFun (congrFun h (Pi.single 4 1)) 5
  have h1 := congrFun (congrFun h (Pi.single 4 1)) 1
  have bits (b : ZMod 2) : b = 0 ∨ b = 1 := by
    fin_cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases bits b with rfl | rfl <;> rcases bits d with rfl | rfl <;>
    simp [operator, shearCoordinates, graphCoordinates] at hb h0 h1 ⊢ <;>
    assumption

variable (B : BinaryField) {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (A : Subgroup G)

/-- Pointwise root/graph coordinates automatically give the homomorphic and
injective parameterization required by the common-fixed-space estimate. -/
theorem form_of_pointwise (hρ : Function.Injective ρ)
    (E : V ≃ₗ[ZMod 2] Eight B.Carrier)
    (hpoint : ∀ t : A, ∃ p : B.Carrier × ZMod 2,
      ∀ v : V, E (ρ t.val v) = operator B.Carrier p (E v))
    (hgraph : ∃ t : A, ∀ v : V, E (ρ t.val v) = graphCoordinates B.Carrier (E v)) :
    Nonempty (GraphForm B ρ A) := by
  choose p hp using hpoint
  have hp1 : p 1 = 0 := by
    apply operator_injective B.Carrier
    funext w
    obtain ⟨v, rfl⟩ := E.surjective w
    rw [← hp, operator_zero]
    simp
  have hpm (t u : A) : p (t * u) = p t + p u := by
    apply operator_injective B.Carrier
    funext w
    obtain ⟨v, rfl⟩ := E.surjective w
    rw [operator_add, ← hp, ← hp, ← hp]
    simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  let φ : A →* Multiplicative (B.Carrier × ZMod 2) := {
    toFun t := Multiplicative.ofAdd (p t)
    map_one' := hp1
    map_mul' t u := hpm t u }
  have hi : Function.Injective φ := by
    intro t u htu
    have he : p t = p u := congrArg Multiplicative.toAdd htu
    apply Subtype.ext
    apply hρ
    apply LinearMap.ext
    intro v
    apply E.injective
    rw [hp, hp, he]
  have hg : ∃ t : A, (φ t).toAdd = (0,1) := by
    obtain ⟨t, ht⟩ := hgraph
    refine ⟨t, ?_⟩
    apply operator_injective B.Carrier
    funext w
    obtain ⟨v, rfl⟩ := E.surjective w
    change operator B.Carrier (p t) (E v) = operator B.Carrier (0,1) (E v)
    rw [operator_graph, ← hp, ht]
  exact ⟨⟨E, φ, hi, hg, hp⟩⟩

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer
