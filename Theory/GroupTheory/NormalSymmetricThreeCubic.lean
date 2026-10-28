module
public import Theory.GroupTheory.NormalSymmetricThreeFactor

/-!
# A marked symmetric-three factor in a quotient of order eighteen

A normal subgroup isomorphic to S₃ splits off its actual centralizer because
S₃ is complete. At total order eighteen that centralizer has prime order
three. The resulting product equivalence sends each element of the specified
normal subgroup to its given S₃ coordinate and the identity cubic coordinate.
The second theorem applies this to the actual quotient by the two-core.

Source application: Delgado–Goldschmidt–Stellmacher, *Groups and Graphs*
(1985), (10.9), printed pp.162–163, the full alpha quotient in the J₂ branch.
-/
public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory.NormalSymmetricThreeFactor
local notation "S3" => Equiv.Perm (Fin 3)
local notation "C3" => Multiplicative (ZMod 3)
variable {A : Type*} [Group A]

/-- The actual normal S₃ factor and its cubic centralizer give marked coordinates. -/
theorem exists_marked_cubic_product (I : Subgroup A) [I.Normal]
    (eI : I ≃* S3) (hA : Nat.card A = 18) :
    ∃ e : A ≃* S3 × C3, ∀ i : I, e i = (eI i,1) := by
  obtain ⟨e,he⟩ := exists_product I eI
  have hc : Nat.card (centralizer (I : Set A)) = 3 := by
    have hh := Nat.card_congr e.toEquiv
    rw [Nat.card_prod,hA] at hh
    have h3 : Nat.card S3 = 6 := by
      simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    rw [h3] at hh
    omega
  let a : centralizer (I : Set A) ≃* C3 := mulEquivOfPrimeCardEq hc (by simp)
  let d : A ≃* S3 × C3 := e.symm.trans
    ((a.prodCongr (MulEquiv.refl S3)).trans MulEquiv.prodComm)
  refine ⟨d,fun i => ?_⟩
  have hi : e (1,eI i) = (i : A) := by
    rw [he,OneMemClass.coe_one,one_mul,eI.symm_apply_apply]
  rw [←hi]
  change ((e.symm (e (1,eI i))).2,a (e.symm (e (1,eI i))).1) = _
  rw [e.symm_apply_apply,map_one]

/-- Preserve the intrinsic normal subgroup quotient on all original representatives. -/
theorem exists_marked_core_cubic_product [Finite A]
    (I : Subgroup A) [I.Normal] (eI : (I ⧸ pCore 2 I) ≃* S3)
    (hA : Nat.card (A ⧸ pCore 2 A) = 18) :
    ∃ e : (A ⧸ pCore 2 A) ≃* S3 × C3,
      ∀ i : I, e (QuotientGroup.mk' (pCore 2 A) i) =
        (eI (QuotientGroup.mk' (pCore 2 I) i),1) := by
  obtain ⟨e,he⟩ := exists_core_product I eI
  let C := centralizer (I.map (QuotientGroup.mk' (pCore 2 A)) : Set (A ⧸ pCore 2 A))
  have hc : Nat.card C = 3 := by
    have hh := Nat.card_congr e.toEquiv
    rw [Nat.card_prod,hA] at hh
    have h3 : Nat.card S3 = 6 := by
      simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    rw [h3] at hh
    change Nat.card C * 6 = 18 at hh
    omega
  let a : C ≃* C3 := mulEquivOfPrimeCardEq hc (by simp)
  let d : (A ⧸ pCore 2 A) ≃* S3 × C3 := e.symm.trans
    ((a.prodCongr (MulEquiv.refl S3)).trans MulEquiv.prodComm)
  refine ⟨d,fun i => ?_⟩
  rw [←he i]
  change ((e.symm (e (1,eI (QuotientGroup.mk' (pCore 2 I) i)))).2,
    a (e.symm (e (1,eI (QuotientGroup.mk' (pCore 2 I) i)))).1) = _
  rw [e.symm_apply_apply,map_one]

/-- A marked product quotient supplies a genuine nontrivial central cubic coset. -/
theorem exists_central_cubic_coset (N : Subgroup A) [N.Normal]
    (d : (A ⧸ N) ≃* S3 × C3) :
    ∃ a : A, a ∉ N ∧ a ^ 3 ∈ N ∧ ∀ x : A, ⁅a,x⁆ ∈ N := by
  let c : C3 := Multiplicative.ofAdd (1 : ZMod 3)
  have hc : c ≠ 1 := by decide
  have hc3 : c ^ 3 = 1 := by decide
  let q := QuotientGroup.mk' N
  obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective N (d.symm (1,c))
  have hd : d (q a) = (1,c) := by rw [ha,d.apply_symm_apply]
  refine ⟨a,?_,?_,?_⟩
  · intro hN
    have hz : q a = 1 := (QuotientGroup.eq_one_iff a).mpr hN
    have hh := congrArg Prod.snd (hd.symm.trans (by rw [hz,d.map_one]))
    exact hc hh
  · apply (QuotientGroup.eq_one_iff (a ^ 3)).mp
    apply d.injective
    change d (q (a ^ 3)) = d 1
    rw [map_pow,map_pow,hd,d.map_one]
    ext <;> simp [hc3]
  · intro x
    apply (QuotientGroup.eq_one_iff ⁅a,x⁆).mp
    apply d.injective
    change d (q ⁅a,x⁆) = d 1
    simp only [map_commutatorElement,hd,d.map_one]
    apply Prod.ext
    · simp [commutatorElement_def]
    · exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

end Theory.GroupTheory.NormalSymmetricThreeFactor
