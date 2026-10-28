module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneNatural
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneSource

/-!
# The b=1 natural cores on the original F.1.11 parabolics

The marked action constructor discharges the opposite geometry. Its two
core equalities are transported through the literal reduced-completion
inclusion to both original full parabolic cores. These cores are elementary,
the field orders agree, and their orders retain the full local actor centers.
The source D intersections use actual conjugators of the same reduced actor.

A multiplicative coordinate map on each original core has kernel exactly
the full center of the embedded actor. Its conjugation equations use the
original ambient multiplication and the unchanged marked SL₂ matrices.
This constructs the natural quotient on the original core, rather than
asserting an abstract module type or changing the original Sylow subgroup.

These are conditional applications of DGS 10.4--10.5(a,b), printed
pp.155--156, and the reduction on pp.95--96 (AS F.1.9, pp.261--262).
`BOneActionData` and the natural dimensions remain earlier Chapter 6--7
inputs, owned by the setup and noncommuting producers. Source assembly
must discharge them. The center-order/path dichotomy of 10.5(c,d) and
all b=2 alternatives remain with this Chapter 10 owner.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
variable (h : HypothesisF11 L S)
    (c₀ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) false)
      (base (reducedFamily L S) true) k₀ W₀)
    (c₁ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) true)
      (base (reducedFamily L S) false) k₁ W₁)

/-- The reduced inclusion carries the full actor center to the full center
of its original image, not merely to a central subgroup. -/
theorem reduced_actor_center_map (A : Subgroup (G₀ L S)) :
    (centerIn A).map (G₀ L S).subtype = centerIn (A.map (G₀ L S).subtype) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    refine ⟨mem_map_of_mem _ hx.1,?_⟩
    rintro _ ⟨y,hy,rfl⟩
    exact congrArg (G₀ L S).subtype (hx.2 y hy)
  · rintro x ⟨hx,hc⟩
    obtain ⟨y,hy,rfl⟩ := hx
    refine ⟨y,⟨hy,?_⟩,rfl⟩
    intro z hz
    exact (G₀ L S).subtype_injective (hc z (mem_map_of_mem _ hz))

include h c₀ c₁ in
/-- The actual original cores equal the images of the reduced source centers. -/
theorem original_cores_eq_center_spans_of_actions :
    (parabolic L S 0).pCoreIn 2 =
        (Z (reducedFamily L S) (base (reducedFamily L S) false)).map (G₀ L S).subtype ∧
    (parabolic L S 1).pCoreIn 2 =
        (Z (reducedFamily L S) (base (reducedFamily L S) true)).map (G₀ L S).subtype := by
  obtain ⟨u₀,⟨d₀⟩⟩ := exists_oppositeCenterGeometry (reduced_triple h) c₀
  obtain ⟨u₁,⟨d₁⟩⟩ := exists_oppositeCenterGeometry (reduced_triple h) c₁
  exact original_cores_eq_reduced_center_spans h d₀ d₁

include h c₀ c₁ in
/-- Both full original parabolic cores are elementary abelian. -/
theorem original_cores_elementary_of_actions :
    IsElementaryAbelian 2 ((parabolic L S 0).pCoreIn 2) ∧
    IsElementaryAbelian 2 ((parabolic L S 1).pCoreIn 2) := by
  obtain ⟨h₀,h₁⟩ := paired_cores_eq_centers_of_actions (reduced_triple h) c₀ c₁
  have hm₀ := reduced_base_Q_map h false
  have hm₁ := reduced_base_Q_map h true
  simp only [Bool.false_eq_true, ↓reduceIte] at hm₀ hm₁
  constructor
  · rw [←hm₀]
    let : IsElementaryAbelian 2 (Q (reducedFamily L S) (base (reducedFamily L S) false)) :=
      core_elementary (reduced_triple h) h₀
    exact IsElementaryAbelian.map _
  · rw [←hm₁]
    let : IsElementaryAbelian 2 (Q (reducedFamily L S) (base (reducedFamily L S) true)) :=
      core_elementary (reduced_triple h) h₁
    exact IsElementaryAbelian.map _

local instance bOneActionSourceAlgebra {k : Type*} [Field k] [CharP k 2] :
    Algebra (ZMod 2) k := ZMod.algebra k 2

include h c₀ c₁ in
/-- Equal fields and exact original core orders, retaining the actual full central factors. -/
theorem original_core_orders_of_natural_actions
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁)) :
    Nat.card k₀ = Nat.card k₁ ∧
      Nat.card ((parabolic L S 0).pCoreIn 2) =
        Nat.card k₀ ^ 2 * Nat.card (centerIn (c₀.actor.map (G₀ L S).subtype)) ∧
      Nat.card ((parabolic L S 1).pCoreIn 2) =
        Nat.card k₁ ^ 2 * Nat.card (centerIn (c₁.actor.map (G₀ L S).subtype)) := by
  obtain ⟨h₀,h₁⟩ := paired_cores_eq_centers_of_actions (reduced_triple h) c₀ c₁
  have hm₀ := reduced_base_Q_map h false
  have hm₁ := reduced_base_Q_map h true
  simp only [Bool.false_eq_true, ↓reduceIte] at hm₀ hm₁
  refine ⟨paired_field_orders_eq (reduced_triple h) c₀ c₁ E₀,?_,?_⟩
  · rw [←hm₀,card_map_of_injective (G₀ L S).subtype_injective,
      ←reduced_actor_center_map,card_map_of_injective (G₀ L S).subtype_injective]
    exact core_card_of_natural c₀ (reduced_triple h) h₀ E₀
  · rw [←hm₁,card_map_of_injective (G₀ L S).subtype_injective,
      ←reduced_actor_center_map,card_map_of_injective (G₀ L S).subtype_injective]
    exact core_card_of_natural c₁ (reduced_triple h) h₁ E₁

include h c₀ c₁ in
/-- Both source D intersections retain their actual conjugators and map to
the full centers of the original actor images. -/
theorem original_literal_D_centers_of_actions :
    ∃ g₀ : c₀.actor, ∃ g₁ : c₁.actor,
      (D (reducedFamily L S) (base (reducedFamily L S) true)
        ((g₀ : G₀ L S) • base (reducedFamily L S) true)).map (G₀ L S).subtype =
          centerIn (c₀.actor.map (G₀ L S).subtype) ∧
      (D (reducedFamily L S) (base (reducedFamily L S) false)
        ((g₁ : G₀ L S) • base (reducedFamily L S) false)).map (G₀ L S).subtype =
          centerIn (c₁.actor.map (G₀ L S).subtype) := by
  obtain ⟨h₀,h₁⟩ := paired_cores_eq_centers_of_actions (reduced_triple h) c₀ c₁
  obtain ⟨g₀,d₀,hd₀,_⟩ := exists_marked_oppositeCenterGeometry (reduced_triple h) c₀
  obtain ⟨g₁,d₁,hd₁,_⟩ := exists_marked_oppositeCenterGeometry (reduced_triple h) c₁
  exact ⟨g₀,g₁,
    (congrArg (map (G₀ L S).subtype)
      (literal_D_eq_actor_center c₀ (reduced_triple h) h₀ g₀ d₀ hd₀)).trans
        (reduced_actor_center_map c₀.actor),
    (congrArg (map (G₀ L S).subtype)
      (literal_D_eq_actor_center c₁ (reduced_triple h) h₁ g₁ d₁ hd₁)).trans
        (reduced_actor_center_map c₁.actor)⟩

/-- Natural coordinates on an original full parabolic core, with the same
reduced actor embedded by the literal inclusion. The denominator is its
embedded full center, and every conjugation equation holds in original G. -/
def OriginalNaturalCoreCoordinates
    {k W : Type*} [Field k] [Finite k] [CharP k 2]
    [AddCommGroup W] [Module (ZMod 2) W]
    (i : Bool) (c : BOneActionData (reducedFamily L S) (base (reducedFamily L S) i)
      (base (reducedFamily L S) (!i)) k W) : Prop :=
    ∃ φ : (parabolic L S (if i then 1 else 0)).pCoreIn 2 →*
        Multiplicative (Fin 2 → k),
      Function.Surjective φ ∧
      φ.ker = (centerIn (c.actor.map (G₀ L S).subtype)).subgroupOf
        ((parabolic L S (if i then 1 else 0)).pCoreIn 2) ∧
      ∀ (a : c.actor) (x : (parabolic L S (if i then 1 else 0)).pCoreIn 2),
        ∃ y : (parabolic L S (if i then 1 else 0)).pCoreIn 2,
          (y : G) = (G₀ L S).subtype a.val * (x : G) * ((G₀ L S).subtype a.val)⁻¹ ∧
          (φ y).toAdd = Matrix.mulVec (c.quotient a).val (φ x).toAdd

include h in
private theorem original_natural_core_of_core_eq
    {k W : Type*} [Field k] [Finite k] [CharP k 2]
    [AddCommGroup W] [Module (ZMod 2) W]
    (i : Bool) (c : BOneActionData (reducedFamily L S) (base (reducedFamily L S) i)
      (base (reducedFamily L S) (!i)) k W)
    (hcore : Q (reducedFamily L S) (base (reducedFamily L S) i) =
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) : OriginalNaturalCoreCoordinates i c := by
  obtain ⟨φ,hφ,hker,hact⟩ := natural_core_coordinates c (reduced_triple h) hcore E
  let Qr := Q (reducedFamily L S) (base (reducedFamily L S) i)
  let Qo := (parabolic L S (if i then 1 else 0)).pCoreIn 2
  change Qr →* Multiplicative (Fin 2 → k) at φ
  change φ.ker = (centerIn c.actor).subgroupOf Qr at hker
  change ∀ (a : c.actor) (x : Qr), ∃ y : Qr,
    (y : G₀ L S) = (a : G₀ L S) * (x : G₀ L S) * (a : G₀ L S)⁻¹ ∧
    (φ y).toAdd = Matrix.mulVec (c.quotient a).val (φ x).toAdd at hact
  let f := (G₀ L S).subtype
  let e : Qr ≃* Qo := (Qr.equivMapOfInjective f (G₀ L S).subtype_injective).trans
    (MulEquiv.subgroupCongr (reduced_base_Q_map h i))
  have he (x : Qr) : (e x : G) = f x.val := rfl
  have hei (x : Qo) : f (e.symm x).val = (x : G) := by
    rw [←he,e.apply_symm_apply]
  let ψ := φ.comp e.symm.toMonoidHom
  refine ⟨ψ,hφ.comp e.symm.surjective,?_,?_⟩
  · rw [←reduced_actor_center_map]
    ext x
    change φ (e.symm x) = 1 ↔ (x : G) ∈ (centerIn c.actor).map f
    have hkx : φ (e.symm x) = 1 ↔ (e.symm x).val ∈ centerIn c.actor := by
      change e.symm x ∈ φ.ker ↔ _
      rw [hker]
      rfl
    rw [hkx]
    constructor
    · intro hx
      exact ⟨(e.symm x).val,hx,hei x⟩
    · rintro ⟨z,hz,hzx⟩
      have hz' : z = (e.symm x).val := (G₀ L S).subtype_injective (hzx.trans (hei x).symm)
      exact hz' ▸ hz
  · intro a x
    obtain ⟨y,hy,hyφ⟩ := hact a (e.symm x)
    refine ⟨e y,?_,?_⟩
    · rw [he,hy,map_mul,map_mul,map_inv,hei]
    · change (φ (e.symm (e y))).toAdd =
        Matrix.mulVec (c.quotient a).val (φ (e.symm x)).toAdd
      rw [e.symm_apply_apply]
      exact hyφ

include h c₀ c₁ in
/-- Literal F1.11 natural-module application at both endpoints. All opposite
geometry and Q=Z premises are discharged from the earlier marked actions. -/
theorem original_natural_cores_of_actions
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁)) :
    OriginalNaturalCoreCoordinates false c₀ ∧ OriginalNaturalCoreCoordinates true c₁ := by
  obtain ⟨h₀,h₁⟩ := paired_cores_eq_centers_of_actions (reduced_triple h) c₀ c₁
  exact ⟨original_natural_core_of_core_eq h false c₀ h₀ E₀,
    original_natural_core_of_core_eq h true c₁ h₁ E₁⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
