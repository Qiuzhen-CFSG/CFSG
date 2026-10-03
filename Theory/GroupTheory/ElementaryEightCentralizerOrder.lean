module

public import Theory.GroupAction.ElementaryEightCentralLine
public import Theory.GroupAction.NormalizingActor

/-!
# Centralizer order for an elementary eight inside an index-two core

Let V have order32 inside Q of order64, and let U be an elementary subgroup
of order8 with C_V(U)=U. If [Q,U] lies in an order-two subgroup Z of U which
Q centralizes, then C_Q(U) has order16. These are explicit finite subgroup
hypotheses; no characteristic-two or quaternion classification is assumed.

Conjugation gives Q an automorphism image on U which fixes Z and acts
trivially modulo Z. The central-line action bound gives image order at most
four, so its kernel C_Q(U) has order at least16. Conversely V has index two
in Q and intersects that kernel in U of order8. The relative-index formula
therefore gives the matching upper bound16.

This count supplies the terminal normal-eight quotient recognition in
Stellmacher(9.1), Journal of Algebra190 (1997), p.48. The actual application
proves C_V(U)=U from the quaternion factors separately.
-/

namespace Subgroup
open scoped commutatorElement

public theorem card_inf_centralizer_eq_sixteen_of_index_two
    {G : Type*} [Group G] [Finite G] (Q V U Z : Subgroup G)
    [IsElementaryAbelian 2 U] (hVQ : V≤Q)
    (hU : Nat.card U=8) (hV : Nat.card V=32) (hQ : Nat.card Q=64)
    (hZU : Z≤U) (hZ : Nat.card Z=2)
    (hcomm : ⁅Q,U⁆≤Z) (hcentral : Q≤centralizer (Z : Set G))
    (hself : V⊓centralizer (U : Set G)=U) :
    Nat.card (Q⊓centralizer (U : Set G) : Subgroup G)=16 := by
  classical
  let C := Q⊓centralizer (U : Set G)
  have hn : Q≤normalizer (U : Set G) := le_normalizer_iff_commutator_le_right.mpr (hcomm.trans hZU)
  let inclusion : Q→*normalizer (U : Set G) := inclusion hn
  let f : Q→*MulAut U := U.normalizerMonoidHom.comp inclusion
  let ZU := Z.subgroupOf U
  have hZUcard : Nat.card ZU=2 := (Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv).trans hZ
  have hfZ : ∀a∈f.range,∀z∈ZU,a z=z := by
    rintro a ⟨q,rfl⟩ z hz
    apply Subtype.ext
    change (q:G)*(z:G)*(q:G)⁻¹=(z:G)
    have hh := mem_centralizer_iff.mp (hcentral q.property) z hz
    rw [← hh,mul_inv_cancel_right]
  have hfquot : ∀a∈f.range,∀u:U,u⁻¹*a u∈ZU := by
    rintro a ⟨q,rfl⟩ u
    have h := hcomm (commutator_mem_commutator q.property u.property)
    have he : (q:G)*(u:G)*(q:G)⁻¹ = (⁅(q:G),(u:G)⁆)*(u:G) := by
      rw [commutatorElement_def]
      group
    change (u:G)⁻¹*((q:G)*(u:G)*(q:G)⁻¹)∈Z
    rw [he]
    have hh := setLike_mul_comm (s:=U) (hZU h) u.property
    rw [hh,inv_mul_cancel_left]
    exact h
  have himage : Nat.card f.range≤4 := card_le_four_of_fixed_line_and_trivial_quotient_on_eight
    hU ZU hZUcard f.range hfZ hfquot
  have hker : f.ker=C.subgroupOf Q := by
    ext q
    change f q=1 ↔ (q:G)∈C
    constructor
    · intro h
      refine ⟨q.property,mem_centralizer_iff.mpr ?_⟩
      intro u hu
      have hh := congrArg (fun a:MulAut U => (a ⟨u,hu⟩:G)) h
      change (q:G)*u*(q:G)⁻¹=u at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro h
      apply MulEquiv.ext
      intro u
      apply Subtype.ext
      change (q:G)*(u:G)*(q:G)⁻¹=(u:G)
      rw [← mem_centralizer_iff.mp h.2 u u.property,mul_inv_cancel_right]
  have hcQ : C≤Q := inf_le_left
  have hkcard : Nat.card f.ker=Nat.card C := by
    rw [hker,Nat.card_congr (subgroupOfEquivOfLe hcQ).toEquiv]
  have hmult := f.ker.card_mul_index
  rw [index_ker,hkcard,hQ] at hmult
  have hCge : 16≤Nat.card C := by nlinarith
  have hVindex : V.relIndex Q=2 := by
    have hh := relIndex_mul_relIndex (⊥:Subgroup G) V Q bot_le hVQ
    simp only [relIndex_bot_left] at hh
    rw [hV,hQ] at hh
    omega
  have hCV : C⊓V=U := by
    change (Q⊓centralizer (U:Set G))⊓V=U
    rw [inf_comm,← inf_assoc,inf_eq_left.mpr hVQ]
    exact hself
  have hupper : V.relIndex C≤2 := by
    have hh := relIndex_le_of_le_right hcQ (show V.relIndex Q≠0 by rw [hVindex]; decide)
    rwa [hVindex] at hh
  have hCmult := relIndex_mul_relIndex (⊥:Subgroup G) (C⊓V) C bot_le inf_le_left
  simp only [relIndex_bot_left,inf_relIndex_left] at hCmult
  rw [hCV,hU] at hCmult
  change Nat.card C=16
  nlinarith
end Subgroup
