module

public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.Sylow


/-!
# An internal conjugator for a pair with order-six image

Two order-two images inside a group of order six are Sylow conjugate.
Lift the conjugator into the original generated subgroup. If the full
preimage of the image normalizer normalizes the original subgroup, the
residual discrepancy preserves that full subgroup, so the conjugacy lifts.

This retains both original subgroups; it does not replace the generated
pair by a smaller subgroup with the same image. The source point-normalizer
condition supplies precisely this hypothesis in13.7.10.
Source: Aschbacher–Smith,13.7.10(2), printed p.941.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G K:Type*} [Group G] [Finite G] [Group K] [Finite K]

omit [Finite G] [Finite K] in
theorem map_conjBy_hom (f:G→*K) (A:Subgroup G) (g:G) :
    (A.conjBy g).map f=(A.map f).conjBy (f g) := by
  change (A.map (MulAut.conj g).toMonoidHom).map f=(A.map f).map _
  rw [map_map,map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]

/-- An order-two image in a group of order six is a Sylow subgroup. -/
private noncomputable def sylowTwoOfCardSix {J:Type*} [Group J] [Finite J]
    (hJ:Nat.card J=6) (A:Subgroup J) (hA:Nat.card A=2) : Sylow 2 J :=
  Sylow.ofCard A (by rw [hJ,hA];decide +kernel)

omit [Finite G] in
/-- If the image normalizer already normalizes the original subgroup, then
Sylow conjugacy in an order-six image lifts to a conjugator inside the
original generated pair. This retains the entire subgroup, not a minimal
subgroup with the same image. -/
theorem exists_internal_conjugator_of_six_image (f:G→*K) (A:Subgroup G) (g:G)
    (hcard:Nat.card ((A⊔A.conjBy g).map f)=6)
    (hA:Nat.card (A.map f)=2)
    (hn:(normalizer (A.map f:Set K)).comap f≤normalizer (A:Set G)) :
    ∃x:(A⊔A.conjBy g:Subgroup G), A.conjBy g=A.conjBy (x:G) := by
  let P:=A⊔A.conjBy g
  let J:=P.map f
  let U:Subgroup J:=(A.map f).subgroupOf J
  let W:Subgroup J:=((A.conjBy g).map f).subgroupOf J
  have hUJ:A.map f≤J:=map_mono le_sup_left
  have hWJ:(A.conjBy g).map f≤J:=map_mono le_sup_right
  have hU:Nat.card U=2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUJ).toEquiv).trans hA
  have hW:Nat.card W=2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWJ).toEquiv,map_conjBy_hom]
    change Nat.card ((A.map f).map (MulAut.conj (f g)).toMonoidHom)=2
    rw [card_map_of_injective (MulAut.conj (f g)).injective,hA]
  let SU:=sylowTwoOfCardSix hcard U hU
  let SW:=sylowTwoOfCardSix hcard W hW
  obtain ⟨z,hz⟩:=MulAction.exists_smul_eq J SU SW
  have hconj : U.conjBy z=W := by
    have he:=congrArg (fun S:Sylow 2 J=>(S:Subgroup J)) hz
    exact he
  have hconj' : (A.map f).conjBy (z:K)=(A.conjBy g).map f := by
    have he:=congrArg (Subgroup.map J.subtype) hconj
    rw [map_conjBy_hom,map_subgroupOf_eq_of_le hUJ,map_subgroupOf_eq_of_le hWJ] at he
    exact he
  obtain ⟨x,hx⟩:=f.subgroupMap_surjective P z
  have hx' : f (x:G)=(z:K):=congrArg Subtype.val hx
  have hnorm : f (g⁻¹*(x:G))∈normalizer (A.map f:Set K) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change (A.map f).conjBy (f (g⁻¹*(x:G)))=A.map f
    rw [map_mul,map_inv,hx']
    apply conjBy_inv_mul_cancel
    rw [←map_conjBy_hom,hconj']
  have hnA : A.conjBy (g⁻¹*(x:G))=A :=
    mem_normalizer_iff_map_conj_eq.mp (hn hnorm)
  refine ⟨x,?_⟩
  have hh:=congrArg (fun B:Subgroup G=>B.conjBy g) hnA
  rw [conjBy_conjBy,mul_inv_cancel_left] at hh
  exact hh.symm
end Subgroup
