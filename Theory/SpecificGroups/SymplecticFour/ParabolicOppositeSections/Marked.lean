module
public import Theory.Representation.BinarySquareInverseWeights.Sections
public import Theory.SpecificGroups.SymplecticFour.ParabolicOppositeSections
public import Mathlib.GroupTheory.Index

/-!
# The opposite-section comparison with a retained group marking

Let a finite group map onto Sp₄(F), with its entire kernel marked as the
natural module. An abelian subgroup projecting onto the standard long root,
normalized by the point-parabolic preimage, supplies the other section.
Its intersection with the kernel has index q. The root action forces that
intersection into the natural cofixed hyperplane, and the index makes the
two kernels equal. Thus the original root and natural maps give coordinates
on the quotient of the span by the intersection, with square and inverse
weights under the same actor.

The quotient transport and distinct-simple-pair theorem show that a
point-parabolic invariant subgroup above the intersection with relative
order q is one of the two original factors when q ≠ 4. All identifications
are constructed from the original group quotient and whole natural kernel;
no marking of the final critical quotient is assumed.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*,
(3.7), printed pp.876–877. A source application must supply the compatible
whole-core natural marking and earlier incidence hypotheses.
-/

public noncomputable section
open Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.ParabolicOppositeSections
open Representation.BinarySquareInverseWeights
variable {F G : Type*} [Field F] [Group G]

/-- Concrete earlier data for the two sections. The natural map is on the
whole kernel, and the root map is the restriction of the same quotient.
No isomorphism of the critical quotient or inequivalence is assumed. -/
structure MarkedPair (κ : G →* Sp F) (A B : Subgroup G) where
  onto : Function.Surjective κ
  kernel : κ.ker = A
  natural : A ≃* Multiplicative (Vector F)
  natural_conjugation : ∀ (g : G) (x y : A),
    (y : G) = g*x*g⁻¹ → (natural y).toAdd = κ g • (natural x).toAdd
  root_image : B.map κ = RootSubgroup.group 0
  opposite_commutative : IsMulCommutative B
  opposite_normalized : (stabilizer (point F)).comap κ ≤ normalizer (B : Set G)
  intersection_index : B.relIndex A = Nat.card F

namespace MarkedPair
variable {κ : G →* Sp F} {A B : Subgroup G} (s : MarkedPair κ A B)

@[expose] def naturalLine : A →* Multiplicative F :=
  coordinate.toAddMonoidHom.toMultiplicative.comp s.natural.toMonoidHom

theorem naturalLine_onto : Function.Surjective s.naturalLine := by
  intro x
  obtain ⟨v,hv⟩ := coordinate_surjective x.toAdd
  exact ⟨s.natural.symm (Multiplicative.ofAdd v), by
    change Multiplicative.ofAdd (coordinate ((s.natural (s.natural.symm _)).toAdd)) = x
    rw [s.natural.apply_symm_apply]
    exact congrArg Multiplicative.ofAdd hv⟩

@[expose] def rootLine : B →* Multiplicative F :=
  rootParameter.symm.toMonoidHom.comp ((κ.comp B.subtype).codRestrict
    (RootSubgroup.group 0) (by intro b; exact s.root_image ▸ mem_map_of_mem κ b.property))

@[simp] theorem rootLine_parameter (b : B) :
    rootElement 0 (s.rootLine b).toAdd = κ b := by
  have hh := rootParameter.apply_symm_apply
    (⟨κ b,s.root_image ▸ mem_map_of_mem κ b.property⟩ : RootSubgroup.group (F := F) 0)
  exact congrArg Subtype.val hh

theorem rootLine_onto : Function.Surjective s.rootLine := by
  intro x
  have hx : (rootParameter x : Sp F) ∈ B.map κ := s.root_image.symm ▸ (rootParameter x).property
  obtain ⟨b,hb,he⟩ := hx
  refine ⟨⟨b,hb⟩,?_⟩
  apply rootParameter.injective
  apply Subtype.ext
  exact (s.rootLine_parameter ⟨b,hb⟩).trans he

theorem rootLine_kernel : s.rootLine.ker = A.subgroupOf B := by
  ext b
  change s.rootLine b = 1 ↔ b.val ∈ A
  constructor
  · intro he
    have hh := s.rootLine_parameter b
    rw [he] at hh
    apply s.kernel.le
    change κ b = 1
    change rootElement 0 (0 : F) = κ b at hh
    rw [RootSubgroup.element_zero] at hh
    exact hh.symm
  · intro he
    apply rootParameter.injective
    apply Subtype.ext
    have he' : b.val ∈ κ.ker := s.kernel.symm ▸ he
    change rootElement 0 (s.rootLine b).toAdd = rootElement 0 (0 : F)
    rw [RootSubgroup.element_zero]
    exact (s.rootLine_parameter b).trans he'

theorem naturalLine_kernel [Finite G] : s.naturalLine.ker = B.subgroupOf A := by
  let : IsMulCommutative B := s.opposite_commutative
  have hi : B.subgroupOf A ≤ s.naturalLine.ker := by
    intro x hx
    obtain ⟨b,hb⟩ := s.rootLine_onto (Multiplicative.ofAdd (1 : F))
    have hκ : κ b = rootElement 0 (1 : F) := by rw [←s.rootLine_parameter,hb]; rfl
    have hconj : (x : G) = b*x*(b : G)⁻¹ := by
      have hh := (IsMulCommutative.is_comm (M := B)).comm b ⟨x,hx⟩
      have hh' : (b : G)*x = x*b := congrArg Subtype.val hh
      rw [hh',mul_inv_cancel_right]
    have hh := s.natural_conjugation b x x hconj
    rw [hκ,root_natural] at hh
    have hcoord := congrArg (fun v : Vector F => v (.inl 0)) hh
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,one_mul,e,Pi.single_eq_same,mul_one] at hcoord
    have hz : coordinate (s.natural x).toAdd = 0 := (add_eq_left.mp hcoord.symm)
    exact hz
  have hindex : s.naturalLine.ker.index = (B.subgroupOf A).index := by
    rw [index_ker,MonoidHom.range_eq_top.mpr s.naturalLine_onto,
      Nat.card_congr (topEquiv : (⊤ : Subgroup (Multiplicative F)) ≃* _).toEquiv]
    exact s.intersection_index.symm
  exact le_antisymm (by
    by_contra hn
    have hlt := Subgroup.index_strictAnti (lt_of_le_not_ge hi hn)
    exact (ne_of_lt hlt) hindex) hi
include s

theorem span_le_parabolic : A ⊔ B ≤ (stabilizer (point F)).comap κ := by
  apply sup_le
  · intro x hx
    have he : x ∈ κ.ker := s.kernel.symm ▸ hx
    change κ x = 1 at he
    change κ x ∈ stabilizer (point F)
    rw [he]
    exact one_mem _
  · intro x hx
    have hr : κ x ∈ RootSubgroup.group (F := F) 0 := s.root_image ▸ mem_map_of_mem κ hx
    obtain ⟨r,hr⟩ := (RootSubgroup.mem_group_iff 0 (κ x)).mp hr
    change κ x ∈ pointParabolic
    rw [←hr,mem_pointParabolic_iff]
    simp [rootElement,rootMatrix,Matrix.single]

theorem naturalLine_conjugation (g : G) (hg : κ g ∈ stabilizer (point F))
    (x y : A) (hy : (y : G) = g*x*g⁻¹) :
    (s.naturalLine y).toAdd = (determinantCharacter (point F) ⟨κ g,hg⟩ : F)⁻¹ *
      (s.naturalLine x).toAdd := by
  change coordinate (s.natural y).toAdd = _
  rw [s.natural_conjugation g x y hy,coordinate_parabolic ⟨κ g,hg⟩]
  rfl

theorem rootLine_conjugation (g : G) (hg : κ g ∈ stabilizer (point F))
    (x y : B) (hy : (y : G) = g*x*g⁻¹) :
    (s.rootLine y).toAdd = (determinantCharacter (point F) ⟨κ g,hg⟩ : F)^2 *
      (s.rootLine x).toAdd := by
  apply RootSubgroup.element_injective 0
  rw [s.rootLine_parameter,hy,map_mul,map_mul,map_inv,←s.rootLine_parameter x,
    root_parabolic ⟨κ g,hg⟩]

/-- Coordinates constructed from the natural kernel and the literal root
restriction. They respect the original point-parabolic conjugation. -/
theorem coordinates [Finite G] :
    ∃ c : PairCoordinates (F := F) (A.subgroupOf (A ⊔ B)) (B.subgroupOf (A ⊔ B)),
      (∀ x : A, (c.map ⟨x,(show A ≤ A ⊔ B from le_sup_left) x.property⟩).toAdd =
        (0,(s.naturalLine x).toAdd)) ∧
      (∀ x : B, (c.map ⟨x,(show B ≤ A ⊔ B from le_sup_right) x.property⟩).toAdd =
        ((s.rootLine x).toAdd,0)) ∧
      ∀ (g : G) (hg : κ g ∈ stabilizer (point F)) (x y : (A ⊔ B : Subgroup G)),
        (y : G) = g*x*g⁻¹ →
        (c.map y).toAdd =
          ((determinantCharacter (point F) ⟨κ g,hg⟩ : F)^2*(c.map x).toAdd.1,
           (determinantCharacter (point F) ⟨κ g,hg⟩ : F)⁻¹*(c.map x).toAdd.2) := by
  let : A.Normal := s.kernel ▸ inferInstance
  let C := A ⊔ B
  have hAC : A ≤ C := le_sup_left
  have hBC : B ≤ C := le_sup_right
  let A₀ := A.subgroupOf C
  let B₀ := B.subgroupOf C
  let : B₀.Normal := normal_subgroupOf_of_le_normalizer
    (s.span_le_parabolic.trans s.opposite_normalized)
  let eA : A₀ ≃* A := subgroupOfEquivOfLe le_sup_left
  let eB : B₀ ≃* B := subgroupOfEquivOfLe le_sup_right
  let fA := s.naturalLine.comp eA.toMonoidHom
  let fB := s.rootLine.comp eB.toMonoidHom
  have kA : fA.ker = B₀.subgroupOf A₀ := by
    ext x
    change eA x ∈ s.naturalLine.ker ↔ _
    rw [s.naturalLine_kernel]
    rfl
  have kB : fB.ker = A₀.subgroupOf B₀ := by
    ext x
    change eB x ∈ s.rootLine.ker ↔ _
    rw [s.rootLine_kernel]
    rfl
  obtain ⟨c,ea,eb⟩ := pairCoordinates A₀ B₀
    (codisjoint_subgroupOf_sup A B).eq_top fA fB
    (s.naturalLine_onto.comp eA.surjective) (s.rootLine_onto.comp eB.surjective) kA kB
  have ha (a : A) : (c.map ⟨a,hAC a.property⟩).toAdd =
      (0,(s.naturalLine a).toAdd) := ea (eA.symm a)
  have hb (b : B) : (c.map ⟨b,hBC b.property⟩).toAdd =
      ((s.rootLine b).toAdd,0) := eb (eB.symm b)
  refine ⟨c,ha,hb,?_⟩
  intro g hg x y hy
  have hx := x.property
  rw [← SetLike.mem_coe,coe_mul_of_left_le_normalizer_right A B
    (le_sup_left.trans (s.span_le_parabolic.trans s.opposite_normalized))] at hx
  obtain ⟨a,haA,b,hbB,hab⟩ := hx
  let a₀ : A := ⟨a,haA⟩
  let b₀ : B := ⟨b,hbB⟩
  let a₁ : A := ⟨g*a*g⁻¹,(inferInstance : A.Normal).conj_mem a haA g⟩
  let b₁ : B := ⟨g*b*g⁻¹,(mem_normalizer_iff.mp (s.opposite_normalized hg) b).mp hbB⟩
  have hx' : x = (⟨a,hAC haA⟩ : C)*⟨b,hBC hbB⟩ := Subtype.ext hab.symm
  have hy' : y = (⟨a₁,hAC a₁.property⟩ : C)*⟨b₁,hBC b₁.property⟩ := by
    apply Subtype.ext
    change (y:G) = (g*a*g⁻¹)*(g*b*g⁻¹)
    rw [hy,←hab]
    group
  rw [hx',hy']
  simp only [map_mul,toAdd_mul]
  rw [ha a₁,hb b₁,ha a₀,hb b₀]
  change (0,(s.naturalLine a₁).toAdd) + ((s.rootLine b₁).toAdd,0) = _
  rw [s.naturalLine_conjugation g hg a₀ a₁ rfl,
    s.rootLine_conjugation g hg b₀ b₁ rfl]
  simp

/-- On the original group, invariant subgroups above the intersection with
relative order q are exactly the two source factors, for q different from four. -/
theorem invariant_order_q [Finite G] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (h4 : Nat.card F ≠ 4) (W : Subgroup G)
    (hWC : W ≤ A ⊔ B) (hIW : A ⊓ B ≤ W)
    (hcard : (A ⊓ B).relIndex W = Nat.card F)
    (hW : (stabilizer (point F)).comap κ ≤ normalizer (W : Set G)) :
    W = A ∨ W = B := by
  obtain ⟨c,_,_,hc⟩ := s.coordinates
  let C := A ⊔ B
  let W₀ := W.subgroupOf C
  have hk : A.subgroupOf C ⊓ B.subgroupOf C ≤ W₀ := fun x hx => hIW hx
  have hwcard : Nat.card (W₀.map c.map) = Nat.card F := by
    rw [←relIndex_ker,c.kernel]
    change ((A ⊓ B).subgroupOf C).relIndex (W.subgroupOf C) = _
    rw [relIndex_subgroupOf hWC]
    exact hcard
  have hstable : ∀ a : Fˣ, ∀ x ∈ W₀, ∃ y ∈ W₀,
      (c.map y).toAdd = ((a:F)^2*(c.map x).toAdd.1,(a:F)⁻¹*(c.map x).toAdd.2) := by
    intro a x hx
    obtain ⟨g,hg⟩ := s.onto (diagonalTorus a 1)
    have hgP : κ g ∈ stabilizer (point F) := hg ▸ (diagonalTorus_mem_borel a 1).1
    have hyW : g*(x:G)*g⁻¹ ∈ W := (mem_normalizer_iff.mp (hW hgP) x).mp hx
    let y : C := ⟨g*(x:G)*g⁻¹,hWC hyW⟩
    refine ⟨y,hyW,?_⟩
    have hh := hc g hgP x y rfl
    simpa only [hg,diagonalTorus_point_character] using hh
  rcases c.invariant_order_q hq h4 W₀ hk hwcard hstable with ha | hb
  · left
    have he := congrArg (Subgroup.map C.subtype) ha
    change (W.subgroupOf C).map C.subtype = (A.subgroupOf C).map C.subtype at he
    rwa [map_subgroupOf_eq_of_le hWC,map_subgroupOf_eq_of_le (show A ≤ C from le_sup_left)] at he
  · right
    have he := congrArg (Subgroup.map C.subtype) hb
    change (W.subgroupOf C).map C.subtype = (B.subgroupOf C).map C.subtype at he
    rwa [map_subgroupOf_eq_of_le hWC,map_subgroupOf_eq_of_le (show B ≤ C from le_sup_right)] at he
end MarkedPair
end Theory.SpecificGroups.SymplecticFour.ParabolicOppositeSections
