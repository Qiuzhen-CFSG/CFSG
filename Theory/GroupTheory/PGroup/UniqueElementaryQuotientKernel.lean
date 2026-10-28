module
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Theory.GroupAction.OddTwoGroupFiltration
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.Lemmas
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizedSupCard

/-!
# An automorphism kernel controlled by elementary subgroups

Let Q be a finite two-group whose center equals its Frattini subgroup and
has order four. Let C be a characteristic elementary subgroup containing
the center with index four. If every elementary subgroup escaping C has
order at most eight, then the automorphisms acting trivially on Q/C form
a two-group. The action is the actual characteristic quotient action.

The proof excludes odd automorphism subgroups of this kernel. A fixed
nonidentity central point bounds the image on the four-element center by
two; oddness therefore makes the center fixed. Central commutators and
abelian C put the C-displacements in the center, and an odd two-group
filtration argument makes the action trivial. If the center has no such
fixed point, the fixed subgroup of Q is elementary: its squares and
commutators lie in the fixed center. Coprime fixed-point generation writes
Q as C times this fixed subgroup. Joining that subgroup with the center
then produces an elementary subgroup escaping C of order at least sixteen,
contradicting the given bound. Cauchy's theorem applies this exclusion to
the odd prime divisors of the quotient-action kernel.

This supplies the order-64 kernel step in Stellmacher (10.1)(a3), printed
p.61, preceding (7), with the elementary-subgroup obstruction stated
explicitly; source: `refs/files/stellmacher-n-group.pdf`.
-/

namespace Subgroup
open scoped commutatorElement

private theorem middle_displacement_central
    {Q : Type*} [Group Q] (C : Subgroup Q) [IsMulCommutative C]
    (f : MulAut Q) (hC : ∀ c ∈ C, f c ∈ C)
    (hquot : ∀ q : Q, q⁻¹ * f q ∈ C)
    (hfix : ∀ z ∈ center Q, f z = z)
    (hclass : _root_.commutator Q ≤ center Q)
    (c : Q) (hc : c ∈ C) : c⁻¹ * f c ∈ center Q := by
  rw [mem_center_iff]
  intro q
  let d := q⁻¹ * f q
  have hdc : d * f c = f c * d := setLike_mul_comm (s := C) (hquot q) (hC c hc)
  have hfq : f q = q * d := by simp [d]
  have hconj : f (q*c*q⁻¹) = q * f c * q⁻¹ := by
    rw [map_mul, map_mul, map_inv, hfq]
    calc
      q*d*f c*(q*d)⁻¹ = q*(d*f c*d⁻¹)*q⁻¹ := by group
      _ = q*f c*q⁻¹ := by rw [hdc, mul_inv_cancel_right]
  have hzfix : f (q*c*q⁻¹*c⁻¹) = q*c*q⁻¹*c⁻¹ := by
    apply hfix
    exact hclass (commutator_mem_commutator (mem_top q) (mem_top c))
  have hsame : q * f c * q⁻¹ = (q*c*q⁻¹*c⁻¹) * f c := by
    rw [← hconj, ← hzfix, ← map_mul]
    congr 1
    group
  have hdelta : q * (c⁻¹ * f c) * q⁻¹ = c⁻¹ * f c := by
    calc
      q*(c⁻¹*f c)*q⁻¹ = (q*c*q⁻¹)⁻¹ * (q*f c*q⁻¹) := by group
      _ = (q*c*q⁻¹)⁻¹ * ((q*c*q⁻¹*c⁻¹)*f c) := by rw [hsame]
      _ = c⁻¹*f c := by group
  exact mul_inv_eq_iff_eq_mul.mp hdelta

private theorem odd_subgroup_eq_bot_of_center_fixed
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (C : Subgroup Q) [C.Characteristic] [IsElementaryAbelian 2 C]
    (hZC : center Q ≤ C) (hclass : _root_.commutator Q ≤ center Q)
    (A : Subgroup (MulAut Q)) (hA : Odd (Nat.card A))
    (hAC : A ≤ (quotientAut C).ker)
    (hfix : ∀ a : A, ∀ z ∈ center Q, (a : MulAut Q) z = z) : A = ⊥ := by
  have hquot (a : A) (q : Q) : q⁻¹ * ((a : MulAut Q) q) ∈ C := by
    have hh := congrArg (fun f : MulAut (Q ⧸ C) => f (QuotientGroup.mk' C q))
      (MonoidHom.mem_ker.mp (hAC a.property))
    rw [quotientAut_apply_mk] at hh
    exact QuotientGroup.eq.mp hh.symm
  have hmiddle (a : A) (c : Q) (hc : c ∈ C) :
      c⁻¹ * ((a : MulAut Q) c) ∈ center Q := by
    apply middle_displacement_central C a _ (hquot a) (hfix a) hclass c hc
    intro x hx
    exact (MulAut.characteristic C a ⟨x,hx⟩).property
  have ht := MulDistribMulAction.trivial_of_odd_of_two_group_filtration
    hA hQ (center Q) C hZC hfix hmiddle hquot
  apply bot_unique
  intro a ha
  change a = 1
  apply MulEquiv.ext
  intro q
  exact ht ⟨a,ha⟩ q

private theorem odd_subgroup_eq_bot_of_elementary_outside_bound
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (C : Subgroup Q) [C.Characteristic] [IsElementaryAbelian 2 C]
    (hZC : center Q ≤ C) (hPhi : frattini Q = center Q)
    (hZcard : Nat.card (center Q) = 4) (hindex : C.index = 4)
    (hbound : ∀ X : Subgroup Q, IsElementaryAbelian 2 X → ¬ X ≤ C → Nat.card X ≤ 8)
    (A : Subgroup (MulAut Q)) (hA : Odd (Nat.card A))
    (hAC : A ≤ (quotientAut C).ker) : A = ⊥ := by
  classical
  let _ : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  have hclass : _root_.commutator Q ≤ center Q :=
    hPhi ▸ commutator_le_frattini_of_isPGroup (p := 2)
  let F := FixedPoints.subgroup A Q
  by_cases hZF : center Q ⊓ F = ⊥
  · have hcop : Nat.Coprime (Nat.card A) (Nat.card Q) := by
      obtain ⟨n,hn⟩ := hQ.exists_card_eq
      rw [hn]
      exact hA.coprime_two_right.pow_right n
    have hquot (a : A) (q : Q) : q⁻¹ * ((a : MulAut Q) q) ∈ C := by
      have hh := congrArg (fun f : MulAut (Q ⧸ C) => f (QuotientGroup.mk' C q))
        (MonoidHom.mem_ker.mp (hAC a.property))
      rw [quotientAut_apply_mk] at hh
      exact QuotientGroup.eq.mp hh.symm
    have hcommAC : commutatorAction A Q ≤ C := by
      rw [commutatorAction_eq_closure]
      apply (closure_le _).mpr
      rintro _ ⟨a,q,rfl⟩
      exact hquot a q
    have hfull := fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
      (G := Q) (A := A) (@IsNilpotent.to_isSolvable Q inferInstance hQ.isNilpotent) hcop
    have hcover : C ⊔ F = ⊤ := by
      apply top_unique
      rw [← hfull]
      exact sup_le le_sup_right (hcommAC.trans le_sup_left)
    let _ : IsElementaryAbelian 2 (center Q) := {
      toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun z =>
        Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=C) z (hZC z.property))) }
    let _ : IsElementaryAbelian 2 F := {
      toIsMulCommutative := ⟨⟨fun x y => by
        apply Subtype.ext
        apply commutatorElement_eq_one_iff_mul_comm.mp
        exact hZF.le ⟨hclass (commutator_mem_commutator (mem_top x) (mem_top y)),
          F.mul_mem (F.mul_mem (F.mul_mem x.property y.property) (F.inv_mem x.property))
            (F.inv_mem y.property)⟩⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
        apply Subtype.ext
        exact hZF.le ⟨hPhi ▸ pth_power_mem_frattini_of_isPGroup (p:=2) (x:Q),
          F.pow_mem x.property 2⟩) }
    let X := center Q ⊔ F
    let _ : IsElementaryAbelian 2 X :=
      IsElementaryAbelian.sup_of_le_centralizer (by rw [centralizer_center]; exact le_top)
    have hnot : ¬ X ≤ C := by
      intro hx
      have hFC : F ≤ C := le_sup_right.trans hx
      rw [sup_eq_left.mpr hFC] at hcover
      have hh := congrArg Subgroup.index hcover
      rw [hindex,index_top] at hh
      omega
    have hXcard : Nat.card X = 4 * Nat.card F := by
      rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ le_normalizer_of_normal
        (disjoint_iff.mpr hZF), hZcard]
    have hrel : C.relIndex F = 4 := by
      rw [← relIndex_sup_right F C, sup_comm F C, hcover, relIndex_top_right, hindex]
    have hFcard : 4 ≤ Nat.card F := by
      have hh := (C.subgroupOf F).index_mul_card
      change C.relIndex F * Nat.card (C.subgroupOf F) = Nat.card F at hh
      rw [hrel] at hh
      have hpos : 0 < Nat.card (C.subgroupOf F) := Nat.card_pos
      nlinarith
    have hh := hbound X inferInstance hnot
    rw [hXcard] at hh
    omega
  · obtain ⟨z,hz,hzne⟩ := SetLike.not_le_iff_exists.mp
      (show ¬ center Q ⊓ F ≤ ⊥ from fun hh => hZF (bot_unique hh))
    let action : MulAut Q →* MulAut (center Q) := MulAut.characteristic (center Q)
    let B := A.map action
    have hBcard : Nat.card B ≤ 2 := by
      apply card_mulAut_subgroup_le_two_of_fixed_point hZcard ⟨z,hz.1⟩
        (fun hh => hzne (congrArg Subtype.val hh)) B
      rintro f ⟨a,ha,rfl⟩
      apply Subtype.ext
      exact (FixedPoints.mem_subgroup (M:=A) (a:=z)).mp hz.2 ⟨a,ha⟩
    have hBodd : Odd (Nat.card B) := hA.of_dvd_nat (card_map_dvd A action)
    have hBone : Nat.card B = 1 := by
      have hpos : 0 < Nat.card B := Nat.card_pos
      obtain ⟨k,hk⟩ := hBodd
      omega
    have hBbot : B = ⊥ := card_eq_one.mp hBone
    apply odd_subgroup_eq_bot_of_center_fixed hQ C hZC hclass A hA hAC
    intro a z hz
    have ha : action a = 1 := hBbot.le (mem_map_of_mem action a.property)
    exact congrArg Subtype.val (congrArg (fun f : MulAut (center Q) => f ⟨z,hz⟩) ha)

/-- The actual quotient-action kernel is a two-group when an elementary
subgroup of index four has the stated center and outside-subgroup bound. -/
public theorem isPGroup_quotientAut_kernel_of_elementary_outside_bound
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (C : Subgroup Q) [C.Characteristic] [IsElementaryAbelian 2 C]
    (hZC : center Q ≤ C) (hPhi : frattini Q = center Q)
    (hZcard : Nat.card (center Q) = 4) (hindex : C.index = 4)
    (hbound : ∀ X : Subgroup Q, IsElementaryAbelian 2 X → ¬ X ≤ C → Nat.card X ≤ 8) :
    IsPGroup 2 (quotientAut C).ker := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  obtain ⟨hpprime,hpdvd,_⟩ := Nat.mem_primeFactors.mp hp
  have hp2 : p = 2 := by
    by_contra hne
    let _ : Fact p.Prime := ⟨hpprime⟩
    obtain ⟨a,haorder⟩ := exists_prime_orderOf_dvd_card' (G := (quotientAut C).ker) p hpdvd
    let A := (zpowers a).map (quotientAut C).ker.subtype
    have hAodd : Odd (Nat.card A) := by
      rw [card_map_of_injective (quotientAut C).ker.subtype_injective, Nat.card_zpowers, haorder]
      exact hpprime.odd_of_ne_two hne
    have hAbot := odd_subgroup_eq_bot_of_elementary_outside_bound
      hQ C hZC hPhi hZcard hindex hbound A hAodd (map_subtype_le _)
    have ha1 : a = 1 := by
      apply Subtype.ext
      exact hAbot.le (mem_map_of_mem (quotientAut C).ker.subtype (mem_zpowers a))
    rw [ha1,orderOf_one] at haorder
    exact hpprime.ne_one haorder.symm
  simp [hp2, Nat.prime_two]

end Subgroup
