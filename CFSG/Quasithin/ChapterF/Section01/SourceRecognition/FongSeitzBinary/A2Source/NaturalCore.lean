module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneNatural

/-!
# One field on a centerfree source core

The genuine natural-core map of DGS 10.5 has kernel the full actor center.
In the centerfree branch it is an equivalence. Its unchanged conjugation
formula gives transitivity on nonidentity core elements. The adjacent-core
intersection is exactly the marked Sylow's fixed locus; its source index
computes its order q. Scalar multiplication and this count identify that
locus with one full line over the original field, including q=2 and q=4.

These are consequences of the earlier marked natural action, not an
assumption of compatible root relations or recognition of the unknown group.
Source: DGS, Groups and Graphs, 10.5(b,c), printed p.156.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
open DGS85 DGS85.NoncommutingProfile Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local instance : Algebra (ZMod 2) k := ZMod.algebra k 2
variable {v w : Vertex (family P)} (c : BOneActionData (family P) v w k W)
  (h : LocallyRankOneTriple P B)
  (hcore : Q (family P) v = Z (family P) v)
  (hcenter : centerIn c.actor = ⊥)
  (E : W ≃ₗ[ZMod 2] (Fin 2 → k))

include c h hcore hcenter E

/-- The centerfree natural core has one faithful coordinate system, with the original actors. -/
theorem exists_coreCoordinates :
    ∃ φ : Q (family P) v ≃* Multiplicative (Fin 2 → k),
      ∀ (a : c.actor) (x : Q (family P) v), ∃ y : Q (family P) v,
        (y : G) = (a : G) * (x : G) * (a : G)⁻¹ ∧
        (φ y).toAdd = Matrix.mulVec (c.quotient a).val (φ x).toAdd := by
  obtain ⟨φ, honto, hker, heq⟩ := natural_core_coordinates c h hcore E
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp (by
    rw [hker, hcenter]
    ext x
    exact ⟨fun hx => Subtype.ext hx, fun hx => congrArg Subtype.val hx⟩)
  exact ⟨MulEquiv.ofBijective φ ⟨hinj,honto⟩,heq⟩

/-- Choose the coordinates once, rather than parametrizing individual roots independently. -/
def coreCoordinates : Q (family P) v ≃* Multiplicative (Fin 2 → k) :=
  (exists_coreCoordinates c h hcore hcenter E).choose

theorem coreCoordinates_conjugate (a : c.actor) (x : Q (family P) v) :
    ∃ y : Q (family P) v,
      (y : G) = (a : G) * (x : G) * (a : G)⁻¹ ∧
      (coreCoordinates c h hcore hcenter E y).toAdd =
        Matrix.mulVec (c.quotient a).val (coreCoordinates c h hcore hcenter E x).toAdd :=
  (exists_coreCoordinates c h hcore hcenter E).choose_spec a x

/-- All nonidentity core elements are conjugate by this same original local actor. -/
theorem core_nonidentity_conjugate (x y : Q (family P) v) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ a : c.actor, (a : G) * (x : G) * (a : G)⁻¹ = (y : G) := by
  let φ := coreCoordinates c h hcore hcenter E
  have hnonzero (z : Q (family P) v) (hz : z ≠ 1) : (φ z).toAdd ≠ 0 := by
    intro he
    apply hz
    apply φ.injective
    exact (show φ z = 1 from he).trans φ.map_one.symm
  obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq k (φ x).toAdd (φ y).toAdd
    (hnonzero x hx) (hnonzero y hy)
  obtain ⟨a,rfl⟩ := c.onto g
  obtain ⟨z,hz,hφ⟩ := coreCoordinates_conjugate c h hcore hcenter E a x
  have hzy : z = y := φ.injective (show φ z = φ y from hφ.trans hg)
  exact ⟨a,hz.symm.trans (congrArg Subtype.val hzy)⟩

/-- The actual adjacent-core intersection has order equal to the chosen field. -/
theorem core_intersection_card :
    Nat.card (Q (family P) v ⊓ Q (family P) w : Subgroup G) = Nat.card k := by
  have hq := core_card_of_natural c h hcore E
  rw [hcenter, Subgroup.card_bot, mul_one] at hq
  have hi := opposite_core_index_of_natural c E
  rw [← hcore, ← inf_relIndex_left (Q (family P) v) (Q (family P) w)] at hi
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G)
    (Q (family P) v ⊓ Q (family P) w) (Q (family P) v) bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, hi, hq, pow_two] at hc
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card k) hc

/-- Intersection with the neighbor core is precisely the fixed locus of its marked Sylow. -/
theorem coreCoordinates_mem_neighbor_iff (x : Q (family P) v) :
    (x : G) ∈ Q (family P) w ↔
      ∀ s ∈ (c.imageSylow : Subgroup SL(2,k)),
        Matrix.mulVec s.val (coreCoordinates c h hcore hcenter E x).toAdd =
          (coreCoordinates c h hcore hcenter E x).toAdd := by
  let φ := coreCoordinates c h hcore hcenter E
  have hcentral : (x : G) ∈ Q (family P) w ↔
      (x : G) ∈ centralizer (Z (family P) w : Set G) := by
    have hxZ : (x : G) ∈ Z (family P) v := hcore ▸ x.property
    have he := congrArg (fun A : Subgroup G => (x : G) ∈ A) c.centralizer_intersection
    simpa only [mem_inf, hxZ, true_and] using (Iff.of_eq he).symm
  rw [hcentral]
  constructor
  · intro hx s hs
    rw [← c.neighbor_image] at hs
    obtain ⟨a,ha,rfl⟩ := hs
    obtain ⟨y,hy,hφ⟩ := coreCoordinates_conjugate c h hcore hcenter E a x
    have hyx : y = x := by
      apply Subtype.ext
      rw [hy, (mem_centralizer_iff.mp hx) (a : G) ha, mul_inv_cancel_right]
    exact hφ.symm.trans (congrArg (fun z => (φ z).toAdd) hyx)
  · intro hx
    apply mem_centralizer_iff.mpr
    intro a ha
    have haL : a ∈ c.actor := c.neighbor_core_le
      (((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h w).1 ha)).1)
    let aL : c.actor := ⟨a,haL⟩
    have hs : c.quotient aL ∈ (c.imageSylow : Subgroup SL(2,k)) := by
      rw [← c.neighbor_image]
      exact mem_map_of_mem _ ha
    obtain ⟨y,hy,hφ⟩ := coreCoordinates_conjugate c h hcore hcenter E aL x
    have hyx : y = x := φ.injective (show φ y = φ x from hφ.trans (hx _ hs))
    have hc : a * (x : G) * a⁻¹ = (x : G) := hy.symm.trans (congrArg Subtype.val hyx)
    have := congrArg (· * a) hc
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using this

/-- The fixed vectors of the marked neighbor Sylow are exactly one full line
over the chosen field, not merely an additive subgroup of the right order. -/
theorem exists_neighbor_fixed_line :
    ∃ v₀ : Fin 2 → k, v₀ ≠ 0 ∧ ∀ t : Fin 2 → k,
      (∀ s ∈ (c.imageSylow : Subgroup SL(2,k)), Matrix.mulVec s.val t = t) ↔
        ∃ a : k, t = a • v₀ := by
  classical
  let φ := coreCoordinates c h hcore hcenter E
  let I := Q (family P) v ⊓ Q (family P) w
  let V := {t : Fin 2 → k // ∀ s ∈ (c.imageSylow : Subgroup SL(2,k)), Matrix.mulVec s.val t = t}
  let e : I ≃ V :=
    { toFun := fun x => ⟨(φ ⟨x,x.property.1⟩).toAdd,
        (coreCoordinates_mem_neighbor_iff c h hcore hcenter E _).mp x.property.2⟩
      invFun := fun t => ⟨φ.symm (.ofAdd t.val), (φ.symm (.ofAdd t.val)).property,
        (coreCoordinates_mem_neighbor_iff c h hcore hcenter E _).mpr (by
          simpa only [φ, MulEquiv.apply_symm_apply, toAdd_ofAdd] using t.property)⟩
      left_inv := fun x => by apply Subtype.ext; simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply]
      right_inv := fun t => by
        apply Subtype.ext
        change (φ (φ.symm (.ofAdd t.val))).toAdd = t.val
        rw [MulEquiv.apply_symm_apply, toAdd_ofAdd] }
  have hV : Nat.card V = Nat.card k := (Nat.card_congr e).symm.trans
    (core_intersection_card c h hcore hcenter E)
  have hI : I ≠ ⊥ := by
    intro he
    have hh := core_intersection_card c h hcore hcenter E
    change Nat.card I = Nat.card k at hh
    rw [he,Subgroup.card_bot] at hh
    exact Finite.one_lt_card.ne hh
  obtain ⟨z,hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hI
  let v₀ : V := e z
  have hv₀ : v₀.val ≠ 0 := by
    intro he
    apply hz
    apply Subtype.ext
    have hh : φ (⟨z,z.property.1⟩ : Q (family P) v) = 1 := he
    exact congrArg (fun x : Q (family P) v => (x : G))
      (φ.injective (hh.trans φ.map_one.symm))
  let f : k → V := fun a => ⟨a • v₀.val, fun s hs => by
    rw [Matrix.mulVec_smul, v₀.property s hs]⟩
  have hf : Function.Injective f := fun a b he =>
    smul_left_injective k hv₀ (congrArg Subtype.val he)
  have honto := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,hV.symm⟩).2
  refine ⟨v₀,hv₀,fun t => ⟨?_,?_⟩⟩
  · intro ht
    obtain ⟨a,ha⟩ := honto ⟨t,ht⟩
    exact ⟨a,(congrArg Subtype.val ha).symm⟩
  · rintro ⟨a,rfl⟩
    exact (f a).property

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
