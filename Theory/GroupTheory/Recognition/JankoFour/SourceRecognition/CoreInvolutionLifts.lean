module
public import Theory.ElementaryAbelian.ExtraspecialPrimeAbelianBound
public import Theory.GroupTheory.PGroup.ExtraspecialInvolution
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.J4Fusion.CoreRepresentatives
public import Theory.GroupTheory.DoubleCoverInvolutionLifting
/-!
# Involution representatives in the original extraspecial core

A maximal elementary subgroup of an extraspecial two-group is
self-centralizing. The unique nontrivial central commutator corrects every
nonsingular representative to a square-one representative in the same coset.
For an extraspecial group of order 8192 mapping normally into a native
sextet stabilizer with elementary kernel, the abelian subgroup bound and
the order-64 two-core force a kernel of order 128 and the whole two-core
as image. Every nonidentity element of that image therefore lifts to an
involution, through the literal map.

This is the core-lifting step in the involution argument of
Aschbacher--Segev, The uniqueness of groups of type J4, Invent. Math. 105
(1991), (4.8), p.599, DOI 10.1007/BF01232280. MarkedCoreInvolutions
applies it to the original core and cocode quotient without a Todd
complement or LocalData assumption.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

/-- Every coset of a maximal elementary subgroup has a square-one representative. -/
theorem extraspecial_square_correction {Q : Type*} [Group Q] [Finite Q]
    [IsExtraspecial 2 Q] (A : Subgroup Q) [IsElementaryAbelian 2 A]
    (hc : (Nat.card A)^2 = 2 * Nat.card Q) (x : Q) :
    ∃ a : A, (x * a.val)^2 = 1 := by
  by_cases hx : x^2=1
  · exact ⟨1,by simpa using hx⟩
  have hC := extraspecial_prime_selfcentralizing_of_card_sq (p := 2) A hc
  have hxC : x ∉ centralizer (A : Set Q) := by
    intro hm
    exact hx (elemPow_eq_one_of_isElementaryAbelian x (hC.le hm))
  obtain ⟨a,ha,hax⟩ : ∃ a ∈ A, a*x ≠ x*a := by
    by_contra! hn
    exact hxC hn
  have hcZ : ⁅a,x⁆ ∈ center Q :=
    (IsExtraspecial.quotient_elementary_abelian 2 Q).commutator_le_center_of_central_quotient
      (commutator_mem_commutator (mem_top a) (mem_top x))
  have hcne : ⁅a,x⁆ ≠ 1 := fun he => hax (commutatorElement_eq_one_iff_mul_comm.mp he)
  obtain ⟨z,_,hz⟩ := (Nat.card_eq_two_iff' (1 : center Q)).mp
    (IsExtraspecial.center_order_p 2 Q)
  have hce : ⁅a,x⁆ = x^2 := congrArg Subtype.val
    ((hz ⟨_,hcZ⟩ (fun he => hcne (congrArg Subtype.val he))).trans
      (hz ⟨_,IsExtraspecial.square_mem_center x⟩ (fun he => hx (congrArg Subtype.val he))).symm)
  have ha2 : a^2=1 := elemPow_eq_one_of_isElementaryAbelian a ha
  have hai : a⁻¹=a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha2)
  have hconj : a*x*a=x⁻¹ := by
    calc
      a*x*a = ⁅a,x⁆ * x := by simp only [commutatorElement_def,hai,mul_assoc,inv_mul_cancel,mul_one]
      _ = x^2*x := by rw [hce]
      _ = x⁻¹ := by
        apply mul_right_cancel (b := x)
        simpa only [pow_succ,pow_zero,one_mul,inv_mul_cancel] using IsExtraspecial.pow_four_eq_one x
  refine ⟨⟨a,ha⟩,?_⟩
  calc
    (x*a)^2 = x*(a*x*a) := by simp only [pow_two,mul_assoc]
    _ = 1 := by rw [hconj,mul_inv_cancel]

/-- Square correction preserves the literal image through an elementary kernel. -/
theorem extraspecial_image_square_lift {Q B : Type*} [Group Q] [Finite Q]
    [IsExtraspecial 2 Q] [Group B] (f : Q →* B) [IsElementaryAbelian 2 f.ker]
    (hc : (Nat.card f.ker)^2 = 2 * Nat.card Q) (u : B) (hu : u ∈ f.range) :
    ∃ x : Q, f x = u ∧ x^2=1 := by
  obtain ⟨x,rfl⟩ := hu
  obtain ⟨a,ha⟩ := extraspecial_square_correction f.ker hc x
  refine ⟨x*a.val,?_,ha⟩
  rw [map_mul,show f a.val=1 from a.property,mul_one]

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
/-- Order bounds identify the entire sextet core and its maximal elementary kernel. -/
theorem extraspecial_sextet_image {Q : Type*} [Group Q] [Finite Q]
    [IsExtraspecial 2 Q] (hQ : Nat.card Q = 8192) (S : Sextet)
    (q : Q →* sextetStabilizer S) [q.range.Normal] [IsElementaryAbelian 2 q.ker] :
    q.range = pCore 2 (sextetStabilizer S) ∧ Nat.card q.ker = 128 := by
  have hle : q.range ≤ pCore 2 (sextetStabilizer S) :=
    le_sSup ⟨inferInstance,(IsExtraspecial.isPGroup 2 Q).of_surjective
      q.rangeRestrict q.rangeRestrict_surjective⟩
  have hbound := card_le_of_le hle
  rw [MathieuCode.J4Fusion.sextet_core_card] at hbound
  have hsq := extraspecial_prime_abelian_card_sq_le_any (p := 2) q.ker
  rw [hQ] at hsq
  have hker : Nat.card q.ker ≤ 128 := by nlinarith
  have hprod := q.ker.card_mul_index
  rw [index_ker,hQ] at hprod
  have hrange : Nat.card q.range = 64 := by nlinarith
  have hk : Nat.card q.ker = 128 := by rw [hrange] at hprod; omega
  exact ⟨eq_of_le_of_card_ge hle (by rw [MathieuCode.J4Fusion.sextet_core_card,hrange]),hk⟩

/-- Every nonidentity element of this image has a genuine involution lift. -/
theorem extraspecial_sextet_involution_lift {Q : Type*} [Group Q] [Finite Q]
    [IsExtraspecial 2 Q] (hQ : Nat.card Q = 8192) (S : Sextet)
    (q : Q →* sextetStabilizer S) [q.range.Normal] [IsElementaryAbelian 2 q.ker]
    (u : sextetStabilizer S) (hu : u ∈ pCore 2 (sextetStabilizer S)) (hne : u ≠ 1) :
    ∃ x : Q, q x = u ∧ orderOf x = 2 := by
  obtain ⟨hr,hk⟩ := extraspecial_sextet_image hQ S q
  obtain ⟨x,hx,hx2⟩ := extraspecial_image_square_lift q
    (by rw [hk,hQ]; decide) u (hr.symm ▸ hu)
  exact ⟨x,hx,orderOf_eq_prime hx2 (fun he => hne (hx.symm.trans (he ▸ q.map_one)))⟩
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
