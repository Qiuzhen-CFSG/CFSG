module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.QuaternionFixed.Numerics
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers.Assembly

/-!
# Cyclic-four lifts in the cubic fixed subgroup

The nonabelian Suzuki moving factor has order 64 and contains V of order
eight. A cubic group acting on its 56 elements outside V fixes one of them.
Every involution in the factor is central: its automorphisms are transitive
on involutions and V supplies a central involution. Since the factor's center
is its derived subgroup, contained in V, each element outside V has order four.
Thus the fixed element is an actual cyclic-four lift in C_Q(B).

Source: Aschbacher–Smith, Lemma J.2.3(5),(7), printed p.434 (PDF p.445),
combined manuscript of 1 March 2004.
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterJ.SpecialCore
variable {G : Type*} [Group G] [Finite G]

/-- The moving factor in the internal product has order 64. -/
theorem SingerChoice.movingCore_card (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) (hB : Nat.card (cubicSubgroup d B) = 3)
    (hfull : ∀ t : d.S, (t : G) ∉ d.V → ⁅zpowers (t : G),d.S⁆ = d.V)
    (s : G) (hs : s ∈ fixedCore d c.B7) (hs1 : s ≠ 1) :
    Nat.card (movingCore d c.B7 s) = 64 := by
  obtain ⟨e,_⟩ := c.coreCentralizer_internalProduct d B hB hfull s hs hs1
  have hc := Nat.card_congr e.toEquiv
  rw [Nat.card_prod, c.fixedCore_card d B,
    (c.coreCentralizer_order_exponent_from_restriction d B hfull s hs hs1).1] at hc
  omega

/-- All elements of the nonabelian Suzuki factor outside V have order four.
No cyclic-four lift or noncommutativity premise is assumed. -/
theorem SingerChoice.movingCore_order_four (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) (hB : Nat.card (cubicSubgroup d B) = 3)
    (hfull : ∀ t : d.S, (t : G) ∉ d.V → ⁅zpowers (t : G),d.S⁆ = d.V)
    (s : G) (hs : s ∈ fixedCore d c.B7) (hs1 : s ≠ 1)
    (x : movingCore d c.B7 s) (hxV : (x : G) ∉ d.V) : orderOf x = 4 := by
  let M := movingCore d c.B7 s
  have hMS : M ≤ d.S := by
    calc
      M ≤ d.S ⊓ centralizer ({s} : Set G) := by
        rw [c.coreCentralizer_eq_sup_from_restriction d B s hs]
        exact le_sup_right
      _ ≤ d.S := inf_le_left
  have hVM := c.V_le_movingCore_from_restriction d B s hs.1
  obtain ⟨_,_,hder,A,_,htrans⟩ := c.movingCore_suzuki d B hB hfull s hs hs1
  have hx2 : x ^ 2 ≠ 1 := by
    intro hsq
    have hx1 : x ≠ 1 := fun h => hxV (by rw [h]; exact d.V.one_mem)
    have hox : orderOf x = 2 := orderOf_eq_prime hsq hx1
    obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' 2 (show 2 ∣ Nat.card d.V by rw [d.ru1.card_V]; decide)
    let zM : M := ⟨z,hVM z.property⟩
    have hoz : orderOf zM = 2 := (orderOf_coe zM).symm.trans ((orderOf_coe z).trans hz)
    obtain ⟨a,_,ha⟩ := htrans zM x hoz hox
    have hxc : x ∈ center M := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨w,rfl⟩ := a.surjective y
      rw [← ha, ← map_mul, ← map_mul]
      apply congrArg a
      exact Subtype.ext (d.ru1.central_V z.property w (hMS w.property))
    have hxder : x ∈ _root_.commutator M := hder ▸ hxc
    have hderV : (_root_.commutator M).map M.subtype ≤ d.V := by
      rw [map_subtype_commutator, ← d.ru1.derived_eq, map_subtype_commutator]
      exact commutator_mono hMS hMS
    exact hxV (hderV (mem_map_of_mem M.subtype hxder))
  have hx4 : x ^ 4 = 1 := Subtype.ext
    (congrArg (fun y : d.S => (y : G)) (d.ru1.pow_four ⟨x,hMS x.property⟩))
  exact orderOf_eq_prime_pow (p := 2) (n := 1) hx2 hx4

/-- A genuine element of order four in the literal C_Q(B), obtained by
cubic orbit counting in the nonabelian Suzuki factor. -/
theorem SingerChoice.exists_cubicFixed_order_four (d : LocalSetup G)
    (B : Sylow 3 d.toTypeRuSetup.L₁) (c : SingerChoice d.toTypeRuSetup B)
    (hQK : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.K)
    (hfull : ∀ t : d.toTypeRuSetup.S, (t : G) ∉ d.V →
      ⁅zpowers (t : G),d.toTypeRuSetup.S⁆ = d.V)
    (s : G) (hs : s ∈ fixedCore d.toTypeRuSetup c.B7) (hs1 : s ≠ 1) :
    ∃ t : cubicFixedQ d.toTypeRuSetup B,
      orderOf t = 4 ∧ (t : G) ∈ movingCore d.toTypeRuSetup c.B7 s ∧ (t : G) ∉ d.V := by
  classical
  let D := d.toTypeRuSetup
  let M := movingCore D c.B7 s
  let A := cubicSubgroup D B
  have hB := cubicSubgroup_card D B d.card_Z (d.center_eq.le.trans inf_le_left)
  have hn := (c.centralizer_normalization D B hB hfull s hs hs1).2.2
  have hMV := c.V_le_movingCore_from_restriction D B s hs.1
  have hMS : M ≤ D.S := by
    calc
      M ≤ D.S ⊓ centralizer ({s} : Set G) := by
        rw [c.coreCentralizer_eq_sup_from_restriction D B s hs]
        exact le_sup_right
      _ ≤ D.S := inf_le_left
  let _ : MulDistribMulAction A M := conjMulDistribMulActionOfLeNormalizer A M hn
  let F := {x : M // (x : G) ∉ d.V}
  let _ : MulAction A F := {
    smul a x := ⟨a • x.val, fun h => x.property
      ((mem_normalizer_iff.mp (D.ru1.natural.normalized
        (cubicSubgroup_le_L D B a.property)) x.val).mpr h)⟩
    one_smul x := Subtype.ext (one_smul A x.val)
    mul_smul a b x := Subtype.ext (mul_smul a b x.val) }
  have hF : Nat.card F = 56 := by
    let _ := Fintype.ofFinite M
    have hV : Nat.card {x : M // (x : G) ∈ d.V} = 8 := by
      calc
        _ = Nat.card d.V := Nat.card_congr {
          toFun x := ⟨x.val,x.property⟩
          invFun z := ⟨⟨z,hMV z.property⟩,z.property⟩
          left_inv _ := rfl
          right_inv _ := rfl }
        _ = 8 := D.ru1.card_V
    have hc := Fintype.card_subtype_compl (fun x : M => (x : G) ∈ d.V)
    simp only [← Nat.card_eq_fintype_card] at hc
    change Nat.card {x : M // (x : G) ∉ d.V} = 56
    rw [hc,hV,c.movingCore_card D B hB hfull s hs hs1]
  have hA : IsPGroup 3 A := B.isPGroup'.map D.L₁.subtype
  obtain ⟨x,hx⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card
    F (by rw [hF]; decide)
  have hfix : (x.val : G) ∈ centralizer (A : Set G) := by
    intro a ha
    exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun y : F => (y.val : G)) (hx ⟨a,ha⟩))
  have hxQ : (x.val : G) ∈ cubicFixedQ D B := by
    rw [cubicFixedQ_eq_cubicFixedS d B hQK]
    exact ⟨hMS x.val.property,hfix⟩
  refine ⟨⟨x.val,hxQ⟩,?_,x.val.property,x.property⟩
  exact (orderOf_coe (⟨x.val,hxQ⟩ : cubicFixedQ D B)).symm.trans
    ((orderOf_coe x.val).trans (c.movingCore_order_four D B hB hfull s hs hs1 x.val x.property))

end CFSG.Quasithin.ChapterJ.SpecialCore
