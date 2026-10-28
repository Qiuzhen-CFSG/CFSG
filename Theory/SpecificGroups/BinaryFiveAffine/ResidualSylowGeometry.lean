module
public import Theory.SpecificGroups.BinaryFiveAffine.ResidualCoreMarks
public import Theory.SpecificGroups.SymmetricFourResidualCore
public import Theory.GroupTheory.SubgroupConjugation
/-!
# The residual four-group in the marked Sylow base

The two-core of the marked A₄ residual is the last-three translation
four-group. Its conjugate under the factor interchange spans the original
sixteen-group. Its commutators with the Sylow base lie on the complementary
pair axis. Conversely, an element of the base that centralizes the residual
four-group and has all base commutators on that axis belongs to the original
vector group.

The last implication checks four equations in the 128-element dihedral
wreath model. It avoids enumerating the full affine group or its automorphisms.
Source: Aschbacher–Smith, 2.4.29, printed pp.545–546.
-/
public section
namespace BinaryFiveAffine
open Subgroup
open scoped commutatorElement
open BinaryPermutation.AlternatingFiveExtension.SylowModel

theorem residual_core_eq_lastThree : residualImage.pCoreIn 2 =
    lastThree.map (SemidirectProduct.inl : V →* W) := by
  have hR : (pResidual 2 X).map X.subtype = residualImage := by
    rw [←map_pResidual 2 symmetricEquiv, map_map,
      Theory.SpecificGroups.SymmetricFourResidual.residual_eq, residualImage_eq]
    rfl
  rw [←hR,Theory.SpecificGroups.SymmetricFour.embedded_residual_twoCore X symmetricEquiv.symm]
  exact X_twoCore_image

private instance : Fintype PlaneWreath := Fintype.ofEquiv _ (RegularWreathProduct.equivProd PlaneGroup Bit).symm
private instance : DecidableEq PlaneWreath := (RegularWreathProduct.equivProd PlaneGroup Bit).injective.decidableEq
private instance : DecidableEq W := SemidirectProduct.equivProd.injective.decidableEq
private instance : DecidablePred (·∈planeBase) := fun x =>
  inferInstanceAs (Decidable (x.right=1))

private def reflectionLift : PlaneWreath := ⟨fun i=>if i=1 then reflection else 1,1⟩

private theorem base_commutator_centralizer_test :
    ∀ y : PlaneWreath, y∈planeBase →
      (⁅sylowEmbedding y,sylowEmbedding pairSquareRoot⁆=1 ∨
        ⁅sylowEmbedding y,sylowEmbedding pairSquareRoot⁆=t*standardZ) →
      (⁅sylowEmbedding y,sylowEmbedding reflectionLift⁆=1 ∨
        ⁅sylowEmbedding y,sylowEmbedding reflectionLift⁆=t*standardZ) →
      sylowEmbedding y * SemidirectProduct.inl (tailVector 1) =
        SemidirectProduct.inl (tailVector 1) * sylowEmbedding y →
      sylowEmbedding y * SemidirectProduct.inl (tailVector 2) =
        SemidirectProduct.inl (tailVector 2) * sylowEmbedding y →
      (sylowEmbedding y).right=1 := by decide +kernel

theorem residual_core_commutator_base_le :
    ⁅residualImage.pCoreIn 2,sylowBase⁆ ≤ zpowers (t*standardZ) := by
  rw [residual_core_eq_lastThree,commutator_le]
  rintro _ ⟨v,hv,rfl⟩ _ ⟨y,hy,rfl⟩
  have hcalc : ∀ (v:V), v∈lastThree → ∀ (y:PlaneWreath), y∈planeBase →
      ⁅(SemidirectProduct.inl v:W),sylowEmbedding y⁆=1 ∨
      ⁅(SemidirectProduct.inl v:W),sylowEmbedding y⁆=t*standardZ := by decide +kernel
  rcases hcalc v hv y hy with h|h
  · rw [h]; exact one_mem _
  · rw [h]; exact mem_zpowers _

theorem residual_core_sup_swap_eq :
    residualImage.pCoreIn 2 ⊔ (residualImage.pCoreIn 2).conjBy standardSwap = vectorGroup := by
  rw [residual_core_eq_lastThree]
  apply le_antisymm
  · apply sup_le
    · rintro _ ⟨v,hv,rfl⟩; exact ⟨v,rfl⟩
    · rintro _ ⟨w,hw,rfl⟩
      obtain ⟨v,hv,rfl⟩ := hw
      rw [mem_vectorGroup]
      simp [MulAut.conj_apply]
  · rintro _ ⟨v,rfl⟩
    have hcalc : ∀ v:V, ∃ a b:lastThree,
        SemidirectProduct.inl v = SemidirectProduct.inl (a:V) *
          (standardSwap * SemidirectProduct.inl (b:V) * standardSwap⁻¹ : W) := by decide +kernel
    obtain ⟨a,b,he⟩ := hcalc v
    rw [he]
    apply mul_mem
    · exact mem_sup_left ⟨a,a.property,rfl⟩
    · exact mem_sup_right ⟨SemidirectProduct.inl (b:V),⟨b,b.property,rfl⟩,rfl⟩

theorem mem_vectorGroup_of_base_centralizes_residual_core_of_commutators
    (w:W) (hw:w∈sylowBase)
    (hc:w∈Subgroup.centralizer (residualImage.pCoreIn 2:Set W))
    (hcomm:∀ j∈sylowBase, ⁅w,j⁆∈zpowers (t*standardZ)) : w∈vectorGroup := by
  obtain ⟨y,hy,rfl⟩ := hw
  have hpow : orderOf (t*standardZ)=2 :=
    (orderOf_eq_prime_iff).mpr ⟨by decide +kernel,t_standardZ_ne_one⟩
  have hmem (j:W) (hj:j∈sylowBase) : ⁅sylowEmbedding y,j⁆=1 ∨
      ⁅sylowEmbedding y,j⁆=t*standardZ := by
    have hh := hcomm j hj
    rw [mem_zpowers_iff_mem_range_orderOf,hpow] at hh
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hh
    have hn' : n=0 ∨ n=1 := by have := Finset.mem_range.mp hn; omega
    rcases hn' with rfl|rfl
    · exact Or.inl (by simpa using he.symm)
    · exact Or.inr (by simpa using he.symm)
  have hr : sylowEmbedding pairSquareRoot∈sylowBase := ⟨pairSquareRoot,rfl,rfl⟩
  have hf : sylowEmbedding reflectionLift∈sylowBase := ⟨reflectionLift,rfl,rfl⟩
  have ht (i:Fin 4) : SemidirectProduct.inl (tailVector i)∈residualImage.pCoreIn 2 := by
    rw [residual_core_eq_lastThree]
    exact ⟨tailVector i,tailVector_mem i,rfl⟩
  rw [mem_vectorGroup]
  exact base_commutator_centralizer_test y hy (hmem _ hr) (hmem _ hf)
    ((Subgroup.mem_centralizer_iff.mp hc) _ (ht 1)).symm
    ((Subgroup.mem_centralizer_iff.mp hc) _ (ht 2)).symm

theorem le_vectorGroup_of_base_centralizes_residual_core_of_commutator
    (A:Subgroup W) (hA:A≤sylowBase)
    (hc:A≤Subgroup.centralizer (residualImage.pCoreIn 2:Set W))
    (hcomm:⁅A,sylowBase⁆≤zpowers (t*standardZ)) : A≤vectorGroup := by
  intro w hw
  exact mem_vectorGroup_of_base_centralizes_residual_core_of_commutators w
    (hA hw) (hc hw) (fun j hj=>hcomm (commutator_mem_commutator hw hj))

theorem vectorGroup_le_sylowBase : vectorGroup ≤ sylowBase := by
  rw [←standardSylow_centralizer_t]
  refine le_inf ?_ ?_
  · rw [←pCore_eq_vectorGroup]
    exact pCore_isPGroup.le_sylow_of_normal standardSylow
  · rintro _ ⟨v,rfl⟩
    exact inl_mem_centralizer v

theorem sylowBase_le_normalizer_residual_core :
    sylowBase ≤ Subgroup.normalizer (residualImage.pCoreIn 2 : Set W) :=
  le_normalizer_iff_commutator_le_left.mpr
    (residual_core_commutator_base_le.trans
      (zpowers_le.mpr t_standardZ_mem_residual_core))

theorem residual_core_le_sylowBase : residualImage.pCoreIn 2 ≤ sylowBase := by
  rw [residual_core_eq_lastThree]
  exact (map_le_range (SemidirectProduct.inl:V→*W) lastThree).trans vectorGroup_le_sylowBase

theorem le_vectorGroup_map_of_base_centralizes_residual_core_of_commutator
    {G:Type*} [Group G] (f:W→*G) (hf:Function.Injective f)
    (A:Subgroup G) (hA:A≤sylowBase.map f)
    (hc:A≤Subgroup.centralizer ((residualImage.pCoreIn 2).map f:Set G))
    (hcomm:⁅A,sylowBase.map f⁆≤zpowers (f (t*standardZ))) : A≤vectorGroup.map f := by
  intro w hw
  obtain ⟨y,hy,rfl⟩ := hA hw
  apply mem_map_of_mem f
  apply mem_vectorGroup_of_base_centralizes_residual_core_of_commutators y hy
  · apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    apply hf
    simpa only [map_mul] using
      (Subgroup.mem_centralizer_iff.mp (hc hw)) (f z) (mem_map_of_mem f hz)
  · intro j hj
    have hh := hcomm (commutator_mem_commutator hw (mem_map_of_mem f hj))
    rw [←MonoidHom.map_zpowers] at hh
    obtain ⟨z,hz,he⟩ := hh
    have he' : f z = f ⁅y,j⁆ := by simpa only [map_commutatorElement] using he
    exact hf he' ▸ hz
end BinaryFiveAffine
