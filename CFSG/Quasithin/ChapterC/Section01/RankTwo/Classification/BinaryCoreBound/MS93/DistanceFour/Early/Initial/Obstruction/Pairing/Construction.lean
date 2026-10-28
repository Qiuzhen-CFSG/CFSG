module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Obstruction.Actor
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Radius commutator forms modulo U

The central containment V' ≤ Z gives a pairing on the literal V/Z with
values in Z/U. The residual fixes its values because U = [Z,Ltilde].
Binary linear functionals separate these quotient values.
This supplies the pairing step of the binary reduction of MS93 (4.6.2),
printed pp.901–902, using the already proved second clause of (4.6.3).
The double quotient lift adapts CentralQuotientCommutatorForms.lean.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial

private def centralBracket {G : Type*} [Group G] (P Z : Subgroup G)
    (hd : ⁅P,P⁆ ≤ Z) (hc : Z ≤ centralizer (P : Set G)) (x : P) : P →* Z where
  toFun y := ⟨⁅(x : G), (y : G)⁆, hd (commutator_mem_commutator x.property y.property)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' y z := by
    apply Subtype.ext
    change ⁅(x : G), (y : G) * z⁆ = ⁅(x : G), (y : G)⁆ * ⁅(x : G), (z : G)⁆
    rw [commutatorElement_mul_right_eq_mul_conj,
      mul_assoc ⁅(x : G), (y : G)⁆ (y : G) ⁅(x : G), (z : G)⁆,
      hc (hd (commutator_mem_commutator x.property z.property)) y y.property]
    simp only [← mul_assoc, mul_inv_cancel_right]

private theorem exists_central_pairing {G : Type*} [Group G] (P Z : Subgroup G)
    [IsMulCommutative Z] [(Z.subgroupOf P).Normal]
    (hd : ⁅P,P⁆ ≤ Z) (hc : Z ≤ centralizer (P : Set G)) :
    ∃ B : (P ⧸ Z.subgroupOf P) →* ((P ⧸ Z.subgroupOf P) →* Z),
      ∀ x y : P, (B (QuotientGroup.mk' (Z.subgroupOf P) x)
        (QuotientGroup.mk' (Z.subgroupOf P) y) : G) = ⁅(x : G), (y : G)⁆ := by
  have hk (x : P) : Z.subgroupOf P ≤ (centralBracket P Z hd hc x).ker := by
    intro z hz
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hc hz x x.property)
  let B : P →* ((P ⧸ Z.subgroupOf P) →* Z) := {
    toFun x := QuotientGroup.lift (Z.subgroupOf P) (centralBracket P Z hd hc x) (hk x)
    map_one' := by
      apply MonoidHom.ext
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf P) q
      apply Subtype.ext
      change ⁅(1 : G), (y : G)⁆ = 1
      simp
    map_mul' x y := by
      apply MonoidHom.ext
      intro q
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf P) q
      apply Subtype.ext
      change ⁅(x : G)*(y : G),(z : G)⁆ = ⁅(x : G),(z : G)⁆ * ⁅(y : G),(z : G)⁆
      rw [commutatorElement_mul_left_eq_conj_mul,
        hc (hd (commutator_mem_commutator y.property z.property)) x x.property]
      simp only [mul_inv_cancel_right]
      exact (hc (hd (commutator_mem_commutator y.property z.property))
        ⁅(x : G),(z : G)⁆ (commutator_mem_commutator x.property z.property |> commutator_le_self P)).symm }
  refine ⟨QuotientGroup.lift (Z.subgroupOf P) B ?_, fun x y => rfl⟩
  intro x hx
  apply MonoidHom.ext
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf P) q
  apply Subtype.ext
  change ⁅(x : G),(y : G)⁆ = 1
  exact commutatorElement_eq_one_iff_mul_comm.mpr (hc hx y y.property).symm

variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The scalar forms of the actual pairing (V/Z) × (V/Z) → Z/U separate
ambient commutators modulo U and are invariant under the local two-residual. -/
theorem radius_commutator_forms [Finite M]
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false) :
    letI := radiusZ_normal common a ha
    letI := radiusQuotient_elementary common hb a ha
    ∃ forms : Set (LinearMap.BilinForm (ZMod 2)
        (Additive ((V R a) ⧸ (Z R a).subgroupOf (V R a)))),
      (∀ B ∈ forms, ∀ g : stabilizer R a, g ∈ pResidual 2 (stabilizer R a) →
        ∀ v w, B (radiusRepresentation common hb a ha g v)
          (radiusRepresentation common hb a ha g w) = B v w) ∧
      (∀ x y : V R a,
        (∀ B ∈ forms, B (Additive.ofMul (QuotientGroup.mk' ((Z R a).subgroupOf (V R a)) x))
          (Additive.ofMul (QuotientGroup.mk' ((Z R a).subgroupOf (V R a)) y)) = 0) ↔
        ⁅(x : FreeAmalgam R), (y : FreeAmalgam R)⁆ ∈ U R a) := by
  let := radiusZ_normal common a ha
  let := radiusQuotient_elementary common hb a ha
  let := geometry.Z_elementary (by omega : 0 < geometry.b R) a ha
  let K := (Z R a).subgroupOf (V R a)
  let T := (U R a).subgroupOf (Z R a)
  let : T.Normal := Subgroup.normal_of_isMulCommutative T
  let : IsElementaryAbelian 2 ((Z R a) ⧸ T) := {
    exponent_dvd_p := MonoidHom.exponent_dvd (f := QuotientGroup.mk' T)
      (QuotientGroup.mk'_surjective _) |>.trans
        (IsElementaryAbelian.exponent_dvd_p 2 (Z R a)) }
  have hc : Z R a ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
    intro z hz v hv
    obtain ⟨z', hz', he⟩ := Z_le_radius_center common a ha hz
    subst z
    exact congrArg Subtype.val ((mem_center_iff.mp hz') ⟨v, hv⟩)
  obtain ⟨pairing, heval⟩ := exists_central_pairing (V R a) (Z R a)
    (radius_derived_le_Z common hb a ha) hc
  let q := QuotientGroup.mk' T
  let scalar (f : Module.Dual (ZMod 2) (Additive ((Z R a) ⧸ T))) :
      LinearMap.BilinForm (ZMod 2) (Additive ((V R a) ⧸ K)) :=
    AddMonoidHom.toZModLinearMap 2 {
      toFun := fun x => AddMonoidHom.toZModLinearMap 2 {
        toFun := fun y => f (Additive.ofMul (q (pairing x.toMul y.toMul)))
        map_zero' := by simp
        map_add' := by intros; simp }
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have heval' (x y : V R a) :
      pairing (QuotientGroup.mk' K x) (QuotientGroup.mk' K y) =
        ⟨⁅(x : FreeAmalgam R),(y : FreeAmalgam R)⁆,
          radius_derived_le_Z common hb a ha (commutator_mem_commutator x.property y.property)⟩ :=
    Subtype.ext (heval x y)
  refine ⟨Set.range scalar, ?_, ?_⟩
  · rintro _ ⟨f, rfl⟩ g hg v w
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective K v.toMul
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective K w.toMul
    change f (Additive.ofMul (q (pairing
      (radiusRepresentation common hb a ha g v).toMul
      (radiusRepresentation common hb a ha g w).toMul))) =
      f (Additive.ofMul (q (pairing v.toMul w.toMul)))
    rw [radiusRepresentation_apply, radiusRepresentation_apply]
    change f (Additive.ofMul (q (pairing
      (radiusQuotientAction common a ha g v.toMul)
      (radiusQuotientAction common a ha g w.toMul)))) = _
    rw [← hx, ← hy, radiusQuotientAction_apply, radiusQuotientAction_apply,
      heval', heval']
    congr 2
    apply QuotientGroup.eq_iff_div_mem.mpr
    change ⁅(g : FreeAmalgam R) * (x : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹,
      (g : FreeAmalgam R) * (y : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹⁆ /
      ⁅(x : FreeAmalgam R),(y : FreeAmalgam R)⁆ ∈ U R a
    have hconj := map_commutatorElement (MulAut.conj (g : FreeAmalgam R))
      (x : FreeAmalgam R) (y : FreeAmalgam R)
    change (g : FreeAmalgam R) * ⁅(x : FreeAmalgam R),(y : FreeAmalgam R)⁆ *
      (g : FreeAmalgam R)⁻¹ =
      ⁅(g : FreeAmalgam R) * (x : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹,
        (g : FreeAmalgam R) * (y : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹⁆ at hconj
    rw [← hconj, div_eq_mul_inv]
    change ⁅(g : FreeAmalgam R), ⁅(x : FreeAmalgam R),(y : FreeAmalgam R)⁆⁆ ∈ U R a
    rw [U, commutator_comm]
    exact commutator_mem_commutator (mem_map_of_mem (stabilizer R a).subtype hg)
      (radius_derived_le_Z common hb a ha (commutator_mem_commutator x.property y.property))
  · intro x y
    let z := pairing (QuotientGroup.mk' K x) (QuotientGroup.mk' K y)
    have hz : (q z = 1) ↔ ⁅(x : FreeAmalgam R),(y : FreeAmalgam R)⁆ ∈ U R a := by
      change (QuotientGroup.mk z = (1 : (Z R a) ⧸ T)) ↔ _
      rw [QuotientGroup.eq_one_iff]
      change (z : FreeAmalgam R) ∈ U R a ↔ _
      rw [heval]
    constructor
    · intro h
      apply hz.mp
      by_contra hn
      obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2)
        (show Additive.ofMul (q z) ≠ 0 from hn)
      exact hf (h (scalar f) ⟨f, rfl⟩)
    · intro h B hB
      obtain ⟨f, rfl⟩ := hB
      change f (Additive.ofMul (q z)) = 0
      rw [hz.mpr h]
      exact map_zero f

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
