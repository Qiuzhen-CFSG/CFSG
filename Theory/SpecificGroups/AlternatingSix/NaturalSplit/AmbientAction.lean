module
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.InnerCoordinates
public import Theory.GroupAction.NormalizerFixer
/-!
# Recognizing the full ambient action on a natural A6 block

A marked block embeds its faithful ambient normalizer in the deleted-module
model of Aut(K). A centralizer of order 32 fills the translation kernel, while
inner automorphisms supply all even permutation coordinates. If another
normalizing elementary subgroup has order at least 32 and escapes the
centralizer, the deleted elementary-placement criterion makes its image odd.
The normalizer therefore realizes every automorphism.

The placement criterion remains explicit at this group-action layer. The
original source20 consumer discharges it with the degree-six offender theorem.
Source: Aschbacher–Smith 14.3.20, first paragraph.
-/

public noncomputable section
open Subgroup SemidirectProduct
open scoped IsMulCommutative
namespace BinaryPermutation.SixNaturalSplit
variable {G:Type*} [Group G]
variable (K A:Subgroup G) (hAK:A≤K) (e:K≃*Model)
variable (hA:(A.subgroupOf K).map e.toMonoidHom=translations)
variable (hN : normalizer (action.range : Set (MulAut Vector)) = (naturalMulAction (Fin 6)).range)

noncomputable def ambientAction : normalizer (K:Set G) →* AutomorphismModel :=
  (markedAutomorphismEquiv e hN).toMonoidHom.comp K.normalizerMonoidHom

theorem ambientAction_surjective
    (hsurj : Function.Surjective K.normalizerMonoidHom) :
    Function.Surjective (ambientAction K e hN) :=
  (markedAutomorphismEquiv e hN).surjective.comp hsurj

theorem ambientAction_inner (k:K) :
    (ambientAction K e hN (inclusion K.le_normalizer k)).right=(e k).right.val := by
  have he : K.normalizerMonoidHom (inclusion K.le_normalizer k)=MulAut.conj k := by
    ext a
    rfl
  change (automorphismEquiv hN ((MulAut.congr e)
    (K.normalizerMonoidHom (inclusion K.le_normalizer k)))).right=_
  rw [he,MulAut.congr_conj]
  exact automorphismEquiv_conj_right hN (e k)

include hAK hA in
theorem ambientAction_right_eq_one (x:normalizer (K:Set G)) :
    (ambientAction K e hN x).right=1 ↔ (x:G)∈centralizer (A:Set G) := by
  change (automorphismEquiv hN ((MulAut.congr e) (K.normalizerMonoidHom x))).right=1 ↔ _
  rw [automorphismEquiv_right_eq_one,←fixingSubgroup_map (A.subgroupOf K) e hA,
    mem_map_equiv,MulEquiv.symm_apply_apply,mem_fixingSubgroup_iff]
  constructor
  · intro hx a ha
    have he := congrArg Subtype.val (hx (⟨a,hAK ha⟩:K) ha)
    change (x:G)*a*(x:G)⁻¹=a at he
    have hh := congrArg (fun y:G=>y*(x:G)) he
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh.symm
  · intro hx a ha
    apply Subtype.ext
    change (x:G)*(a:G)*(x:G)⁻¹=(a:G)
    rw [←hx (a:G) ha,mul_assoc,mul_inv_cancel,mul_one]

include hAK hA hN in
theorem ambientAction_surjective_of_large_elementary
    (hfaith:Function.Injective K.normalizerMonoidHom)
    (hCN:centralizer (A:Set G)≤normalizer (K:Set G))
    (hCc:Nat.card (centralizer (A:Set G))=32)
    (E:Subgroup G) [IsElementaryAbelian 2 E]
    (hEN:E≤normalizer (K:Set G)) (hEc:32≤Nat.card E)
    (hEC:¬E≤centralizer (A:Set G))
    (hmax:∀ (B:Subgroup AutomorphismModel),IsElementaryAbelian 2 B→
      B≤(alternatingGroup (Fin 6)).comap rightHom→32≤Nat.card B→B≤rightHom.ker) :
    Function.Surjective K.normalizerMonoidHom := by
  let : Finite AutomorphismModel := Finite.of_equiv
    (Multiplicative (Deleted (Fin 6)) × Equiv.Perm (Fin 6)) SemidirectProduct.equivProd.symm
  let N:=normalizer (K:Set G)
  let f:=ambientAction K e hN
  have hf:Function.Injective f := (markedAutomorphismEquiv e hN).injective.comp hfaith
  let P:Subgroup AutomorphismModel := (rightHom : AutomorphismModel→*Equiv.Perm (Fin 6)).ker
  let B:Subgroup AutomorphismModel := (alternatingGroup (Fin 6)).comap rightHom
  have hPcard:Nat.card P=32 := by
    change Nat.card (rightHom : AutomorphismModel→*Equiv.Perm (Fin 6)).ker=32
    rw [←range_inl_eq_ker_rightHom]
    rw [←Nat.card_congr (MonoidHom.ofInjective (inl_injective (φ:=deletedAction))).toEquiv]
    change Nat.card (Deleted (Fin 6))=32
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,finrank_deleted]
    decide
  have hCmap:((centralizer (A:Set G)).subgroupOf N).map f = P := by
    apply eq_of_le_of_card_ge
    · rintro y ⟨x,hx,rfl⟩
      exact (ambientAction_right_eq_one K A hAK e hA hN x).mpr hx
    · rw [card_map_of_injective hf,
        Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv,hCc,hPcard]
  have hPr:P≤f.range := hCmap ▸ map_le_range f _
  have hBr:B≤f.range := by
    intro x hx
    let s:Actor:=⟨x.right,hx⟩
    obtain ⟨k,hk⟩:=e.surjective (inr s)
    let y:N:=inclusion K.le_normalizer k
    have hy:(f y).right=x.right := by
      change (ambientAction K e hN (inclusion K.le_normalizer k)).right=x.right
      rw [ambientAction_inner,hk]
      rfl
    have hp:x*(f y)⁻¹∈P := by
      change rightHom (x*(f y)⁻¹)=1
      simp only [map_mul,map_inv]
      change x.right*((f y).right)⁻¹=1
      rw [hy,mul_inv_cancel]
    simpa only [inv_mul_cancel_right] using f.range.mul_mem (hPr hp) (show f y∈f.range from ⟨y,rfl⟩)
  let E':Subgroup AutomorphismModel := (E.subgroupOf N).map f
  let :IsElementaryAbelian 2 (E.subgroupOf N) := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hEN).toMonoidHom (subgroupOfEquivOfLe hEN).injective
  have he':IsElementaryAbelian 2 E' := IsElementaryAbelian.map f
  have hec:32≤Nat.card E' := by
    rw [card_map_of_injective hf,Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv]
    exact hEc
  have hnot:¬E'≤B := by
    intro he
    have hEP:E'≤P := hmax E' he' he hec
    apply hEC
    intro x hx
    exact (ambientAction_right_eq_one K A hAK e hA hN ⟨x,hEN hx⟩).mp
      (hEP (mem_map_of_mem f (show (⟨x,hEN hx⟩:N)∈E.subgroupOf N from hx)))
  obtain ⟨y,hy,hyB⟩:=SetLike.not_le_iff_exists.mp hnot
  have hyr:y∈f.range := map_le_range f _ hy
  have hBi:B.index=2 := by
    rw [index_comap_of_surjective _ rightHom_surjective,alternatingGroup.index_eq_two]
  have hsurj:Function.Surjective f := by
    intro x
    change x∈f.range
    by_cases hx:x∈B
    · exact hBr hx
    · have hp:x*y⁻¹∈B := (mul_mem_iff_of_index_two hBi).mpr
        (by simp only [hx,inv_mem_iff,hyB])
      simpa only [inv_mul_cancel_right] using f.range.mul_mem (hBr hp) hyr
  intro a
  obtain ⟨x,hx⟩:=hsurj (markedAutomorphismEquiv e hN a)
  exact ⟨x,(markedAutomorphismEquiv e hN).injective hx⟩
end BinaryPermutation.SixNaturalSplit
