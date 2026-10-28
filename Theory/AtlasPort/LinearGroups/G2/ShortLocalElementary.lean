module
public import Theory.AtlasPort.LinearGroups.G2.LieSpecialRadical
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Core

/-!
# Normal elementary subgroups of the short G₂ local group

An elementary abelian subgroup normalized by the short parabolic residual
lies in its five-root two-core. Commutation with a short-root conjugate
kills the fourth root coordinate; Weyl conjugation kills the first. The
square and Weyl-commutator identities kill the remaining two coordinates.
Thus the subgroup lies in the highest-root center, over every finite field
of characteristic two, including the binary field.

This is the local root calculation used to exclude a crossed natural G₂
block in Aschbacher--Smith 4.3.7, using the root pair of F.1.11--12.
Coordinates use the attributed ATLAS imports; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. No additional ATLAS source is copied here.
-/
public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Atlas.G2.LieParabolicSetup
open Explicit
variable {F : Type*} [Field F] [CharP F 2]
private theorem rootF_conjugate (t : Fin 6 → F) (ht : t 5 = 0) :
    rootF 1 * unipotentProduct t * (rootF 1)⁻¹ =
      unipotentProduct ![t 0 + t 3 ^ 2 + t 3*t 4 + t 4^2,
        t 1+t 2+t 3+t 4,t 2+t 4,t 3+t 4,t 4,0] := by
  have hf : rootF (1 : F) = unipotentProduct ![0,0,0,0,0,1] := by simp [unipotentProduct]
  rw [hf,unipotentProduct_inv,unipotentProduct_mul,unipotentProduct_mul]
  congr 1
  ext i
  fin_cases i <;> simp [unipotentProductParameters,unipotentInverseParameters,ht,
    CharTwo.neg_eq,CharTwo.sub_eq_add,CharTwo.ofNat_eq_mod]
  all_goals ring_nf
  all_goals simp [CharTwo.two_eq_zero]

private theorem fourth_zero (t : Fin 6 → F) (ht : t 5 = 0)
    (hc : Commute (unipotentProduct t) (rootF 1 * unipotentProduct t * (rootF 1)⁻¹)) :
    t 4 = 0 := by
  have hh := hc.commutator_eq
  rw [rootF_conjugate t ht,fiveRoot_commutator t _ ht rfl] at hh
  have he := rootA_injective (hh.trans rootA_zero.symm)
  simp [CharTwo.neg_eq,CharTwo.sub_eq_add,CharTwo.ofNat_eq_mod] at he
  have hz : t 4 ^ 2 = 0 := by
    linear_combination he - (t 1*t 4+t 2*t 4+t 3*t 4+t 2*t 3) * (CharTwo.two_eq_zero (R := F))
  exact (sq_eq_zero_iff).mp hz

theorem elementary_normal_short_local_le_highestRoot [Finite F]
    (E : Subgroup (Model F)) [IsElementaryAbelian 2 E]
    (hE : E ≤ local₁) (hn : local₁ ≤ normalizer (E : Set (Model F))) : E ≤ highestRoot := by
  have hcore := le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 E) hE hn
  rw [local₁_pCore] at hcore
  have hS : (weylS : Model F) ∈ local₁ := mem_sup_right (subset_closure (by simp))
  have hF : rootF (1 : F) ∈ local₁ := unipotent_le_local₁ (subset_closure (by simp))
  have hc (x y : Model F) (hx : x ∈ E) (hy : y ∈ E) : Commute x y :=
    congrArg Subtype.val ((inferInstance : IsMulCommutative E).is_comm.comm ⟨x,hx⟩ ⟨y,hy⟩)
  have hfour (t : Fin 6 → F) (ht : t 5 = 0) (he : unipotentProduct t ∈ E) : t 4 = 0 :=
    fourth_zero t ht (hc _ _ he ((mem_normalizer_iff.mp (hn hF) _).mp he))
  intro x hx
  obtain ⟨t,ht,rfl⟩ := hcore hx
  have h4 := hfour t ht hx
  have hxt := (mem_normalizer_iff.mp (hn hS) _).mp hx
  rw [weylS_fiveRoot_conjugate t ht] at hxt
  have h1 : t 1 = 0 := hfour _ rfl hxt
  have hs := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hx
  rw [fiveRoot_square t ht] at hs
  have h23 : t 2*t 3 = 0 := by
    have he := rootA_injective (hs.trans rootA_zero.symm)
    simpa [h1,h4,CharTwo.ofNat_eq_mod] using he
  have hss := (hc _ _ hx hxt).commutator_eq
  rw [fiveRoot_commutator t _ ht rfl] at hss
  have he := rootA_injective (hss.trans rootA_zero.symm)
  simp [h1,h4,CharTwo.neg_eq,CharTwo.sub_eq_add,CharTwo.ofNat_eq_mod] at he
  rcases mul_eq_zero.mp h23 with h2 | h3
  · have h3 : t 3 = 0 := mul_self_eq_zero.mp (by simpa [h2] using he)
    refine ⟨Multiplicative.ofAdd (t 0),?_⟩
    change rootA (t 0) = _
    simp [unipotentProduct,h1,h2,h3,h4,ht]
  · have h2 : t 2 = 0 := mul_self_eq_zero.mp (by simpa [h3] using he)
    refine ⟨Multiplicative.ofAdd (t 0),?_⟩
    change rootA (t 0) = _
    simp [unipotentProduct,h1,h2,h3,h4,ht]
end Atlas.G2.LieParabolicSetup
