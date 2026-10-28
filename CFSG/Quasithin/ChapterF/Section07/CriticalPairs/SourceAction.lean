module

public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Quadratic
public import Theory.Representation.ElementaryAbelianAction
public import Theory.Representation.BinaryOffender.Defs

/-!
# The faithful source action of a critical pair

Conjugation on the intrinsic elementary abelian subgroup V descends to the
literal quotient G₁/C_G₁(V); its kernel computation proves faithfulness.
The nested group commutator identities then give quadratic action of the
actual endpoint image, with no hypothesis on the action of the rest of G₁.
`even_critical_pair` assembles every clause of F.7.11(2).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.7.11(2),
printed pp.313–314 (PDF pp.324–325).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative commutatorElement
open Subgroup.CosetGeometry.RankTwo
open CFSG.Quasithin.ChapterF.Section07.Track
open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterF.Section07.CriticalPairs.SourceAction
variable {G : Type*} [Group G] {F : Bool → Subgroup G} (D : SourceSetup F)
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : IsElementaryAbelian 2 D.V := D.reduced.elementary
local instance : D.V.Normal := D.reduced.normal

/-- Conjugation on the intrinsic elementary abelian group V over F₂. -/
noncomputable def conjugationRepresentation :
    Representation (ZMod 2) (F false) (Additive D.V) where
  toFun g := (MulAut.conjNormal (H := D.V) g).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro x
    change Additive.ofMul (MulAut.conjNormal (H := D.V) 1 x.toMul) = x
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    change Additive.ofMul (MulAut.conjNormal (H := D.V) (a * b) x.toMul) = _
    rw [map_mul]
    rfl

/-- Evaluation preserves the original subgroup embedding. -/
theorem conjugationRepresentation_apply (g : F false) (x : Additive D.V) :
    ((conjugationRepresentation D g x).toMul : F false) =
      g * (x.toMul : F false) * g⁻¹ := rfl

/-- The action kernel is exactly the source centralizer, in G₁. -/
theorem conjugationRepresentation_ker :
    (conjugationRepresentation D).ker = centralizer (D.V : Set (F false)) := by
  ext a
  rw [MonoidHom.mem_ker, mem_centralizer_iff]
  constructor
  · intro h x hx
    have he := congrArg (fun f : Module.End (ZMod 2) (Additive D.V) =>
      (f (Additive.ofMul ⟨x, hx⟩)).toMul.val) h
    change a * x * a⁻¹ = x at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro h
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change a * (x.toMul : F false) * a⁻¹ = (x.toMul : F false)
    rw [← h x.toMul x.toMul.property, mul_inv_cancel_right]

/-- The actual faithful quotient G₁ / C_G₁(V), with its literal quotient map. -/
noncomputable def faithfulRepresentation :
    Representation (ZMod 2) ((F false) ⧸ centralizer (D.V : Set (F false)))
      (Additive D.V) :=
  QuotientGroup.lift _ (conjugationRepresentation D)
    (conjugationRepresentation_ker D).ge

/-- The quotient representation is faithful without an additional premise. -/
theorem faithfulRepresentation_injective : Function.Injective (faithfulRepresentation D) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (conjugationRepresentation_ker D).symm

/-- Compatibility with the exact quotient map used by F.7.11. -/
theorem faithfulRepresentation_mk (g : F false) :
    faithfulRepresentation D (QuotientGroup.mk' (centralizer (D.V : Set (F false))) g) =
      conjugationRepresentation D g := rfl

/-- A vanishing nested ambient commutator gives quadratic action of the
literal quotient image of A on the intrinsic V. -/
theorem quadratic_quotient_image (A : Subgroup G) (_hA : A ≤ F false)
    (hc : ⁅⁅D.seed, A⁆, A⁆ = ⊥) :
    IsQuadratic (faithfulRepresentation D)
      ((A.subgroupOf (F false)).map
        (QuotientGroup.mk' (centralizer (D.V : Set (F false))))) := by
  intro a ha b hb x
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  rw [faithfulRepresentation_mk, faithfulRepresentation_mk, map_sub]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  have hx : ((x.toMul : F false) : G) ∈ D.seed :=
    mem_map_of_mem (F false).subtype x.toMul.property
  have hinner : ⁅(b : G), ((x.toMul : F false) : G)⁆ ∈ ⁅D.seed, A⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hb hx
  have houter : ⁅(a : G), ⁅(b : G), ((x.toMul : F false) : G)⁆⁆ = 1 := by
    apply mem_bot.mp
    rw [← hc, commutator_comm]
    exact commutator_mem_commutator ha hinner
  have hcomm := commutatorElement_eq_one_iff_mul_comm.mp houter
  have he := congrArg (fun z : G => z * (a : G)⁻¹) hcomm
  simpa [conjugationRepresentation, commutatorElement_def, div_eq_mul_inv, mul_assoc] using he

/-- F.7.11(2), including nontrivial quadratic action on the actual quotient. -/
theorem even_critical_pair (hne : D.V ≠ ⊥) {v : Vertex F}
    (hd : (graph F).dist (base F false) v = D.track hne)
    (hb : Even (D.track hne)) (hcritical : ¬ D.seed ≤ ballKernel F v 1) :
    ⁅D.seed, vertexModule F D.seed v⁆ ≠ ⊥ ∧
      ⁅D.seed, vertexModule F D.seed v⁆ ≤ D.seed ⊓ vertexModule F D.seed v ∧
      vertexModule F D.seed v ≤ F false ∧
      ((vertexModule F D.seed v).subgroupOf (F false)).map
        (QuotientGroup.mk' (centralizer (D.V : Set (F false)))) ≠ ⊥ ∧
      IsQuadratic (faithfulRepresentation D)
        (((vertexModule F D.seed v).subgroupOf (F false)).map
          (QuotientGroup.mk' (centralizer (D.V : Set (F false))))) := by
  have hcont := even_pair_containments F D hne hd hb
  exact ⟨even_pair_commutator_ne_bot F D hne hd hb hcritical, hcont.2, hcont.1,
    even_pair_quotient_image_ne_bot F D hne hd hb hcritical,
    quadratic_quotient_image D _ hcont.1 (even_pair_nested_commutators F D hne hd hb).1⟩

/-- The source FF predicate for the canonical faithful centralizer quotient. -/
def IsFF : Prop := IsFFModule (faithfulRepresentation D)

end CFSG.Quasithin.ChapterF.Section07.CriticalPairs.SourceAction
