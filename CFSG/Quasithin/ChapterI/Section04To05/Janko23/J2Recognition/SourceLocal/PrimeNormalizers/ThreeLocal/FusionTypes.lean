module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Basic
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Remaining source three-class and Sylow contracts

These definitions specify the unproved conclusions of Aschbacher,
*Sporadic Groups* (1994), 47.3(2)–(4), pp.261–262. The two element types
are defined by the actual source involutions, and the Sylow action is
literal normalizer conjugation followed by the intrinsic Frattini quotient.
No existence or source recognition theorem is asserted by these records.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
variable {G : Type*} [Group G] [Finite G]

/-- Source 3A: order-three elements whose subgroup is a source vertex. -/
def ThreeA (D : Seed G) (x : G) : Prop :=
  orderOf x = 3 ∧ zpowers x ∈ MulAction.orbit (ConjAct G) D.X

/-- The vertex definition of 3A agrees with the printed involution-centralizing
condition; it is not an unrelated family label. -/
theorem threeA_iff_centralizes (D : Seed G) (x : G) :
    ThreeA D x ↔ orderOf x = 3 ∧ ∃ t : G, IsConj D.z t ∧ Commute x t := by
  constructor
  · rintro ⟨hx, hX⟩
    obtain ⟨t, ht, hle⟩ := D.vertex_centralizes_conjugate ⟨zpowers x, hX⟩
    exact ⟨hx, t, ht, mem_centralizer_singleton_iff.mp (hle (mem_zpowers x))⟩
  · rintro ⟨hx, t, ht, hxt⟩
    obtain ⟨g, rfl⟩ := isConj_iff.mp ht
    let a := MulAut.conj g
    let y := a.symm x
    have hy : orderOf y = 3 := (a.symm.orderOf_eq x).trans hx
    have hz : y ∈ involutionCentralizer D.z := by
      apply mem_centralizer_singleton_iff.mpr
      apply a.injective
      rw [map_mul, map_mul]
      change a (a.symm x) * a D.z = a D.z * a (a.symm x)
      rw [a.apply_symm_apply]
      exact hxt.eq
    have hY := D.mem_vertex_of_le_centralizer (zpowers y)
      (by rw [Nat.card_zpowers, hy]) (zpowers_le.mpr hz)
    have hg := MulAction.mem_orbit_of_mem_orbit (ConjAct.toConjAct g) hY
    change (zpowers y).map a.toMonoidHom ∈ MulAction.orbit (ConjAct G) D.X at hg
    rw [MonoidHom.map_zpowers] at hg
    change zpowers (a y) ∈ MulAction.orbit (ConjAct G) D.X at hg
    rw [show a y = x from a.apply_symm_apply x] at hg
    exact ⟨hx, hg⟩

/-- The actual inverting involution fuses the two generators of each vertex.
Consequently every source 3A element is conjugate to any chosen generator of X. -/
theorem threeA_isConj (D : Seed G) (H : CentralizerCalculation D)
    (a : D.X) (ha : orderOf a = 3) {x : G} (hx : ThreeA D x) :
    IsConj (a : G) x := by
  classical
  have hgen : zpowers (a : G) = D.X :=
    eq_of_le_of_card_ge (zpowers_le.mpr a.property)
      (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, ha, D.card_X])
  obtain ⟨g, hg⟩ := hx.2
  let e := MulAut.conj (ConjAct.ofConjAct g)
  change D.X.map e.toMonoidHom = zpowers x at hg
  have hm : x ∈ zpowers (e a) := by
    change x ∈ zpowers (e.toMonoidHom (a : G))
    rw [← MonoidHom.map_zpowers, hgen, hg]
    exact mem_zpowers x
  have hea : orderOf (e a) = 3 := by rw [e.orderOf_eq, Subgroup.orderOf_coe, ha]
  rw [mem_zpowers_iff_mem_range_orderOf, hea] at hm
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hm
  have hi' : i < 3 := Finset.mem_range.mp hi
  have hconj (b : G) : IsConj b (e b) := isConj_iff.mpr ⟨ConjAct.ofConjAct g, rfl⟩
  interval_cases i
  · have hx1 : x = 1 := by simpa using hix.symm
    have hc := hx.1
    rw [hx1, orderOf_one] at hc
    omega
  · have he : e a = x := by simpa using hix
    exact he ▸ hconj a
  · have hpow : (a : G) ^ 2 = (a : G)⁻¹ := by
      apply mul_right_cancel (b := (a : G))
      rw [inv_mul_cancel, ← pow_succ]
      have h := congrArg Subtype.val (pow_orderOf_eq_one a)
      simpa only [ha, Subgroup.coe_pow, OneMemClass.coe_one] using h
    have he : e ((a : G)⁻¹) = x := by
      rw [← hpow, map_pow]
      exact hix
    have hai : IsConj (a : G) (a : G)⁻¹ :=
      isConj_iff.mpr ⟨H.inverter, H.inverts_X a⟩
    exact he ▸ hai.trans (hconj (a : G)⁻¹)

/-- Source 3B: order-three elements centralizing an involution of the other class. -/
def ThreeB (D : Seed G) (x : G) : Prop :=
  orderOf x = 3 ∧ ∃ t : G, orderOf t = 2 ∧ ¬ IsConj D.z t ∧ Commute x t

/-- The two genuine conjugacy classes and the second-class normalizers. -/
structure ThreeFusion (D : Seed G) : Prop where
  classes : ∃ a b : G, ThreeA D a ∧ ThreeB D b ∧ ¬ IsConj a b ∧
    (∀ x : G, ThreeA D x ↔ IsConj a x) ∧
    (∀ x : G, ThreeB D x ↔ IsConj b x) ∧
    (∀ x : G, orderOf x = 3 → ThreeA D x ∨ ThreeB D x)
  secondNormalizer : ∀ y : G, ThreeB D y →
    Nonempty (normalizer (zpowers y : Set G) ≃*
      Equiv.Perm (Fin 3) × alternatingGroup (Fin 4))

/-- The actual Sylow normalizer action on the intrinsic Frattini quotient. -/
def sylowFrattiniAction (P : Sylow 3 G) :
    normalizer (P : Set G) →* MulAut (P ⧸ frattini P) :=
  (quotientAut (frattini P)).comp (P : Subgroup G).normalizerMonoidHom

/-- Full marked Sylow output needed by 47.3 and the subsequent suborbit argument. -/
structure SylowThreeStructure (D : Seed G) (P : Sylow 3 G) where
  card : Nat.card P = 27
  extraspecial : IsExtraspecial 3 P
  center_vertex : (center P).map (P : Subgroup G).subtype ∈
    MulAction.orbit (ConjAct G) D.X
  weakly_closed : ∀ g : G,
    ((center P).map (P : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (P : Subgroup G) →
    ((center P).map (P : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom =
      (center P).map (P : Subgroup G).subtype
  complement : Subgroup (normalizer (P : Set G))
  complement_cyclic : IsCyclic complement
  complement_card : Nat.card complement = 8
  split : ((P : Subgroup G).subgroupOf (normalizer (P : Set G))).IsComplement' complement
  faithful : Function.Injective ((sylowFrattiniAction P).comp complement.subtype)
  transitive : ∀ u v : P ⧸ frattini P, u ≠ 1 → v ≠ 1 →
    ∃ b : complement, sylowFrattiniAction P b u = v
  class_in_sylow : ∀ x : P, orderOf x = 3 → (ThreeA D x ↔ x ∈ center P)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
