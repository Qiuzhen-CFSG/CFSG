module

public import Theory.SpecificGroups.SL2.BinaryTetrahedralCentralCover
public import Theory.GroupTheory.Commutator.CentralExtensionPairing


/-!
# Rank-one lifts in central two-extensions

Every central extension of the binary tetrahedral group by a two-group
splits uniquely. First, the order-three generator and its conjugates show
that this group has no nontrivial two-group image. The central commutator
homomorphism therefore makes the inverse image of its center central.
The existing order-three orbit construction then supplies the quaternion
relations and a section. Pullback gives a unique lift of any homomorphism
from this group into the base of a central two-extension.

The group is the concrete Q₈ ⋊ C₃ model, identified with SL₂(3) by
`GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL`. The intended
consumer embeds two orthogonal rank-one groups in Sp₄(3), and uses uniqueness
to lift their commutation and factor-swap relations.

Source: the elementary binary tetrahedral calculation in ABG II.3,
Proposition 2 (article p.22), as implemented in `BinaryTetrahedralCentralCover`;
the symplectic application is Aschbacher–Smith I.1.4(1), printed p.408,
and GLS3 §6.1. This module does not assert the symplectic multiplier result.
-/

public section

open GLS3.Chapter5.SchurPresentation
open Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary

/-- The binary tetrahedral group has no nontrivial two-group image. -/
theorem binary_hom_eq_one {D : Type*} [Group D] (hD : IsPGroup 2 D)
    (g : BinaryTetrahedral →* D) : g = 1 := by
  have ht : g binaryT = 1 := by
    apply (hD.powEquiv (by decide : Nat.Coprime 2 3)).injective
    change g binaryT ^ 3 = (1 : D) ^ 3
    rw [← map_pow, binaryT_cube, map_one, one_pow]
  have hi : g binaryI = 1 := by
    have h := congrArg g binary_commutator_eq_conjugate
    simpa only [map_mul, map_inv, map_pow, ht, one_pow, inv_one,
      mul_one, one_mul, inv_mul_cancel] using h.symm
  have hj : g binaryJ = 1 := by
    have h := congrArg g binary_commutator_pair_eq_conjugate
    simpa only [map_mul, map_inv, map_pow, ht, hi, one_pow, inv_one,
      mul_one, one_mul] using h.symm
  exact binary_hom_ext g 1 hi hj ht

/-- The full inverse image of the rank-one center is central in a two-extension. -/
theorem binary_comap_center_le {E : Type*} [Group E]
    (q : E →* BinaryTetrahedral) (hq : Function.Surjective q)
    (hc : q.ker ≤ center E) (hk : IsPGroup 2 q.ker) :
    (center BinaryTetrahedral).comap q ≤ center E := by
  intro z hz
  have hmem (x : E) : ⁅x,z⁆ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hz (q x))
  let d : E →* q.ker := {
    toFun x := ⟨⁅x,z⁆, hmem x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' x y := by
      apply Subtype.ext
      change ⁅x*y,z⁆ = ⁅x,z⁆ * ⁅y,z⁆
      have hy := mem_center_iff.mp (hc (hmem y)) x
      rw [commutatorElement_mul_left_eq_conj_mul, hy, mul_inv_cancel_right]
      exact mem_center_iff.mp (hc (hmem x)) ⁅y,z⁆ }
  have hd : q.ker ≤ d.ker := by
    intro x hx
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hc hx) z).symm
  let d' : BinaryTetrahedral →* q.ker := q.liftOfSurjective hq ⟨d, hd⟩
  have hd' : d' = 1 := binary_hom_eq_one hk d'
  apply mem_center_iff.mpr
  intro x
  have he : d' (q x) = d x := by
    exact q.liftOfRightInverse_comp_apply _ _ ⟨d, hd⟩ x
  rw [hd'] at he
  exact commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val he.symm)

/-- Every central two-group extension of the actual binary tetrahedral group splits. -/
theorem exists_binary_section {E : Type*} [Group E]
    (q : E →* BinaryTetrahedral) (hq : Function.Surjective q)
    (hc : q.ker ≤ center E) (hk : IsPGroup 2 q.ker) :
    ∃ s : BinaryTetrahedral →* E, q.comp s = MonoidHom.id _ := by
  obtain ⟨t, htq, ht⟩ := q.exists_pow_eq_one_lift_of_central_pgroup_ker hq hc hk
    (by decide : Nat.Coprime 2 3) binaryT binaryT_cube
  obtain ⟨x,hx⟩ := hq binaryI
  let Z := (center BinaryTetrahedral).comap q
  have hZc : Z ≤ center E := binary_comap_center_le q hq hc hk
  have hZtwo : IsPGroup 2 Z :=
    (IsPGroup.of_card (n := 1) (by simpa using binaryTetrahedral_center_card)).comap_of_ker_isPGroup q hk
  let a := x⁻¹*t*x*t⁻¹
  let b := (t*a*t⁻¹)*a⁻¹
  have hqa : q a = binaryI⁻¹*binaryT*binaryI*binaryT⁻¹ := by
    simp only [a, map_mul, map_inv, hx, htq]
  have hs : a^2 ∈ Z := by
    change q (a^2) ∈ center BinaryTetrahedral
    rw [map_pow, hqa]
    exact binary_commutator_square_central
  obtain ⟨ha4,hb2,hba,hta,htb⟩ :=
    QuaternionGroup.relations_of_central_two_orbit Z hZc hZtwo x t ht hs
  obtain ⟨s,hsI,hsJ,hsT⟩ := exists_binaryTetrahedral_hom a b t ha4 hb2 hba ht hta htb
  have hcomp : q.comp s = (MulAut.conj (binaryT^2)).toMonoidHom := by
    apply binary_hom_ext
    · change q (s binaryI) = binaryT^2*binaryI*(binaryT^2)⁻¹
      rw [hsI, hqa, binary_commutator_eq_conjugate]
    · change q (s binaryJ) = binaryT^2*binaryJ*(binaryT^2)⁻¹
      rw [hsJ]
      change q ((t*a*t⁻¹)*a⁻¹) = _
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, htq, hqa]
      exact binary_commutator_pair_eq_conjugate
    · change q (s binaryT) = binaryT^2*binaryT*(binaryT^2)⁻¹
      rw [hsT, htq]
      group
  refine ⟨s.comp (MulAut.conj (binaryT^2)).symm.toMonoidHom, ?_⟩
  rw [← MonoidHom.comp_assoc, hcomp]
  apply MonoidHom.ext
  intro y
  exact (MulAut.conj (binaryT^2)).apply_symm_apply y

/-- Lifts of a binary tetrahedral homomorphism through a central two-kernel are unique. -/
theorem binary_lift_unique {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hc : f.ker ≤ center E) (hk : IsPGroup 2 f.ker)
    (s t : BinaryTetrahedral →* E) (hst : f.comp s = f.comp t) : s = t := by
  have hm (x : BinaryTetrahedral) : s x * (t x)⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    rw [show f (s x) = f (t x) from DFunLike.congr_fun hst x, mul_inv_cancel]
  let d : BinaryTetrahedral →* f.ker := {
    toFun x := ⟨s x * (t x)⁻¹, hm x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' x y := by
      apply Subtype.ext
      change s (x*y) * (t (x*y))⁻¹ = _
      rw [map_mul, map_mul]
      calc
        (s x*s y)*(t x*t y)⁻¹ = s x*(s y*(t y)⁻¹)*(t x)⁻¹ := by group
        _ = (s x*(t x)⁻¹)*(s y*(t y)⁻¹) := by
          rw [mul_assoc, ← mem_center_iff.mp (hc (hm y)) ((t x)⁻¹)]
          group }
  have hd := binary_hom_eq_one hk d
  apply MonoidHom.ext
  intro x
  have hx : s x * (t x)⁻¹ = 1 := congrArg (fun k : BinaryTetrahedral →* f.ker => (k x : E)) hd
  exact mul_inv_eq_one.mp hx

/-- Pulling back the given map constructs its literal rank-one lift. -/
theorem exists_binary_lift {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : IsPGroup 2 f.ker)
    (j : BinaryTetrahedral →* G) :
    ∃ s : BinaryTetrahedral →* E, f.comp s = j := by
  let H : Subgroup (E × BinaryTetrahedral) :=
    (f.comp (MonoidHom.fst E BinaryTetrahedral)).eqLocus
      (j.comp (MonoidHom.snd E BinaryTetrahedral))
  let q : H →* BinaryTetrahedral := (MonoidHom.snd E BinaryTetrahedral).comp H.subtype
  let r : H →* E := (MonoidHom.fst E BinaryTetrahedral).comp H.subtype
  have hH (x : H) : f (r x) = j (q x) := x.property
  have hq : Function.Surjective q := by
    intro b
    obtain ⟨a,ha⟩ := hf (j b)
    exact ⟨⟨(a,b),ha⟩,rfl⟩
  have hrk (x : q.ker) : r x ∈ f.ker := by
    change f (r x) = 1
    rw [hH, show q x = 1 from x.property, map_one]
  let k : q.ker →* f.ker := (r.comp q.ker.subtype).codRestrict f.ker hrk
  have hki : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val h
    · exact x.property.trans y.property.symm
  have hqk : IsPGroup 2 q.ker := hk.of_injective k hki
  have hqc : q.ker ≤ center H := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Prod.ext
    · exact mem_center_iff.mp (hc (hrk ⟨x,hx⟩)) (r y)
    · change q y * q x = q x * q y
      rw [show q x = 1 from hx, mul_one, one_mul]
  obtain ⟨s,hs⟩ := exists_binary_section q hq hqc hqk
  refine ⟨r.comp s, ?_⟩
  apply MonoidHom.ext
  intro b
  change f (r (s b)) = j b
  rw [hH, show q (s b) = b from DFunLike.congr_fun hs b]

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary
