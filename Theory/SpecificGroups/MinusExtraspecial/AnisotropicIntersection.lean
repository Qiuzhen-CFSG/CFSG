module
public import Theory.SpecificGroups.MinusExtraspecial.InvolutionCentralizerFixer
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.GroupTheory.PGroup.ExtraspecialNormalizedFour

/-!
# The centralizer of an adjacent minus-extraspecial intersection

Suppose Q normalizes a minus-extraspecial group R of order thirty-two,
and Q intersects R in order sixteen. An elementary four-group Z in this
intersection centralizes Q and contains the center of R. If the centralizer
of R in Q lies in R, then the centralizer of the intersection in Q is Z.

A noncentral involution of Z has exactly this intersection as its centralizer
in R. The rigidity of automorphisms fixing that centralizer puts an outside
centralizer element back in R, and the intrinsic double-centralizer calculation
puts it in Z. Self-centralization is required only relative to Q, so the
lemma applies within a parabolic without an ambient normality assumption.

Source application: Delgado--Goldschmidt--Stellmacher, Groups and Graphs
(1985), (10.9), printed p.163; the involution-centralizer rigidity is the
singular-axis calculation in Aschbacher, Sporadic Groups (1994), 8.15(2), p.29.
-/

public noncomputable section
open Subgroup
namespace MinusExtraspecial
variable {G : Type*} [Group G]

/-- The centralizer in Q of its index-two intersection with the actual minus core R. -/
theorem intersection_centralizer_eq
    (Q R Z : Subgroup G) [Finite R] (e : R ≃* Model)
    (hZQ : Z ≤ Q) (hZR : Z ≤ R) (hZC : Z ≤ centralizer (Q : Set G))
    (hZ : Nat.card Z = 4) (hZe : IsElementaryAbelian 2 Z)
    (hcenter : (center R).map R.subtype ≤ Z)
    (hA : Nat.card (Q.subgroupOf R) = 16)
    (hn : Q ≤ normalizer (R : Set G))
    (hself : Q ⊓ centralizer (R : Set G) ≤ R) :
    Q ⊓ centralizer ((Q ⊓ R : Subgroup G) : Set G) = Z := by
  let : IsExtraspecial 2 R := IsExtraspecial.of_mulEquiv e.symm inferInstance
  let : IsElementaryAbelian 2 Z := hZe
  let ZR := Z.subgroupOf R
  have hcZR : Nat.card ZR = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZR).toEquiv,hZ]
  obtain ⟨u,huZ,hu⟩ : ∃ u ∈ ZR, u ∉ center R := by
    by_contra hh
    push Not at hh
    have hh' : ZR ≤ center R := hh
    have hc := Nat.card_le_card_of_injective _ (inclusion_injective hh')
    rw [hcZR,IsExtraspecial.center_order_p 2 R] at hc
    omega
  have huQ : (u : G) ∈ Q := hZQ huZ
  have hu2 : u ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (u : G) huZ)
  have hCcard : Nat.card (centralizer ({u} : Set R)) = 16 :=
    IsExtraspecial.centralizer_card_sixteen_of_card_thirty_two
      ((Nat.card_congr e.toEquiv).trans card_model) u hu
  have hAC : Q.subgroupOf R = centralizer ({u} : Set R) := by
    apply eq_of_le_of_card_ge
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (Subtype.ext (hZC huZ x hx))
    · rw [hA,hCcard]
  apply le_antisymm
  · rintro x ⟨hxQ,hx⟩
    let n : normalizer (R : Set G) := ⟨x,hn hxQ⟩
    have hfix (y : R) (hy : y * u = u * y) : R.normalizerMonoidHom n y = y := by
      have hyQ : y ∈ Q.subgroupOf R := hAC.symm ▸ mem_centralizer_singleton_iff.mpr hy
      apply Subtype.ext
      change x * y * x⁻¹ = y
      rw [←hx y ⟨hyQ,y.property⟩,mul_inv_cancel_right]
    obtain ⟨r,hrQ,hr⟩ : ∃ r : R, (r : G) ∈ Q ∧
        R.normalizerMonoidHom n = MulAut.conj r := by
      rcases eq_one_or_conj_of_fixes_involution_centralizer e hu2 hu
        (R.normalizerMonoidHom n) hfix with hh | hh
      · exact ⟨1,Q.one_mem,by simpa using hh⟩
      · exact ⟨u,huQ,hh⟩
    have hxc : (r : G)⁻¹ * x ∈ centralizer (R : Set G) := by
      intro y hy
      have he := congrArg Subtype.val (DFunLike.congr_fun hr (⟨y,hy⟩ : R))
      change x * y * x⁻¹ = (r : G) * y * (r : G)⁻¹ at he
      have hh := congrArg (fun v : G => (r : G)⁻¹ * v * x) he
      simpa only [mul_assoc,inv_mul_cancel,mul_inv_cancel,inv_mul_cancel_left,
        mul_one,one_mul] using hh.symm
    have hxR : x ∈ R := by
      have hd := hself ⟨Q.mul_mem (Q.inv_mem hrQ) hxQ,hxc⟩
      simpa only [mul_inv_cancel_left] using R.mul_mem r.property hd
    have hxC : (⟨x,hxR⟩ : R) ∈
        centralizer (centralizer ({u} : Set R) : Set R) := by
      intro y hy
      have hyQ : y ∈ Q.subgroupOf R := hAC.symm ▸ hy
      exact Subtype.ext (hx y ⟨hyQ,y.property⟩)
    have hbound : center R ⊔ zpowers u ≤ ZR := by
      apply sup_le
      · intro z hz
        exact hcenter (mem_map_of_mem R.subtype hz)
      · exact zpowers_le.mpr huZ
    exact hbound (centralizer_centralizer_involution_le e u hu2 hu hxC)
  · exact le_inf hZQ (hZC.trans (centralizer_le inf_le_left))
end MinusExtraspecial
