module
public import Theory.Alternating.SevenQuasisimpleExtension
public import Theory.Mathieu.M22.TripleCover.Recognition
public import Theory.Mathieu.M22.TripleCover.ScalarAutomorphisms
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Center-fixing automorphisms of cubic A₇ and M₂₂ covers

Outer automorphisms of the genuine cubic A₇ cover invert its center.
For the genuine M₂₂ cover, fixing the distinguished central scalar
characterizes inner automorphisms. Transport through the actual cover
isomorphisms gives innerness for any automorphism fixing the whole center.
The scalar transport is proved for abstract groups to avoid expanding the
concrete binary matrix carrier in each application.

Sources: GLS3 5.2.7 and Aschbacher--Smith H.12, printed pp.393--394;
the original 12.6.26 application is on printed p.832.
-/

public section
open Subgroup
open Theory.GroupTheory

private theorem inner_of_center_fixed_via_scalar
    {B K : Type*} [Group B] [Group K] (j : B ≃* K)
    (s : K) (hs : s ∈ center K)
    (hi : ∀ t : MulAut K, t s = s → ∃ b : K, t = MulAut.conj b)
    (t : MulAut B) (hfix : ∀ b ∈ center B, t b = b) : t ∈ MulAut.innerSubgroup B := by
  have hst : MulAut.congr j t s = s := by
    change j (t (j.symm s)) = s
    have hh : t (j.symm s) = j.symm s :=
      hfix _ ((centerCongr j.symm ⟨s,hs⟩).property)
    rw [hh,j.apply_symm_apply]
  obtain ⟨b,hb⟩ := (MulAut.congr_inner_iff j t).mp (hi _ hst)
  exact ⟨b,hb.symm⟩

/-- An automorphism of a genuine cubic A₇ cover fixing its center is inner. -/
theorem GLS3.Chapter5.OddCentralCovers.inner_of_fixes_center
    {B : Type*} [Group B] [Finite B] [IsQuasisimple B]
    (e : (B ⧸ center B) ≃* alternatingGroup (Fin 7))
    (hc : Nat.card (center B)=3) (t : MulAut B)
    (hfix : ∀ b ∈ center B, t b = b) : t ∈ MulAut.innerSubgroup B := by
  obtain ⟨j⟩ := GLS3.Chapter5.OddCentralCovers.triple_seven_equiv e hc
  by_contra hi
  have hinv := Theory.AlternatingSevenExtension.center_inverted_of_tripleSeven_model j t
    (fun b hb => hi ⟨b,hb.symm⟩)
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := center B) 3 (by rw [hc])
  have he : (u : B)=(u : B)⁻¹ := (hfix u u.property).symm.trans (hinv u u.property)
  have hu2 : u ^ 2=1 := Subtype.ext (by rw [pow_two]; exact eq_inv_iff_mul_eq_one.mp he)
  have hd := orderOf_dvd_of_pow_eq_one hu2
  rw [hu] at hd
  norm_num at hd

/-- An automorphism of a genuine cubic M₂₂ cover fixing its center is inner. -/
theorem Sporadic.Mathieu.M22TripleCover.inner_of_fixes_center_of_quotient
    {B : Type*} [Group B] [Finite B] [IsQuasisimple B]
    (e : (B ⧸ center B) ≃* Sporadic.Mathieu.M22)
    (hc : Nat.card (center B)=3) (t : MulAut B)
    (hfix : ∀ b ∈ center B, t b = b) : t ∈ MulAut.innerSubgroup B := by
  obtain ⟨j⟩ := Sporadic.Mathieu.M22TripleCover.nonempty_mulEquiv hc ⟨e⟩
  exact inner_of_center_fixed_via_scalar j Sporadic.Mathieu.M22TripleCover.scalar
    Sporadic.Mathieu.M22TripleCover.scalar_mem_center
    Sporadic.Mathieu.M22TripleCover.ScalarAutomorphisms.inner_of_fixes_scalar t hfix
