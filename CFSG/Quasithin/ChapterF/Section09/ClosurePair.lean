module
public import CFSG.Quasithin.ChapterF.Section09.ClosureOrthogonal
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.SingularInvolutionPairs

/-!
# Symmetric-three pairs in the identified quaternion closure

Act on the whole original U_H, whose quaternion structure is supplied by
its producer. The actual V generators have singular displacements by
F.9.5(2), and the original Q_H is the action kernel. The finite plus-space
pair theorem therefore identifies every non-two starred pair as S₃.
No intersecting-pair or plane-control assumption is needed on this branch.

Source application: Aschbacher–Smith13.5.15, printed p.920.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} (h : D.Hypothesis)
include h

theorem closure_pair_orthogonal_generators
    (hi : D.Vplus.relIndex D.V = 2) (hn : ¬D.V≤D.QH)
    (g : G) (hg : g ∈ D.H)
    (q : QuaternionCentralProductData D.UH)
    (hz : (center D.UH).map D.UH.subtype=D.V₁) :
    let I := D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom
    ∀ hIH:I≤D.H,
    ∃ a b : BinaryFourPlus.Wreath, a^2=1 ∧ b^2=1 ∧
      (∀ v, BinaryFourPlus.q ((BinaryFourPlus.wreathToIsometry a).val v-v)=0) ∧
      (∀ v, BinaryFourPlus.q ((BinaryFourPlus.wreathToIsometry b).val v-v)=0) ∧
      (closureOrthogonalAction I hIH q).range = zpowers a ⊔ zpowers b := by
  dsimp only
  intro hIH
  let := h.elementary
  let f := (MulAut.conj g).toMonoidHom
  let I := D.V ⊔ D.V.map f
  let P := D.UH
  have hVI : D.V ≤ I := le_sup_left
  have hBI : D.V.map f ≤ I := le_sup_right
  let n := hIH.trans (le_normalizer_conjugateSpanBy D.Vplus D.H)
  let α := closureOrthogonalAction I hIH q
  have hk : α.ker = D.QH.subgroupOf I := h.closureOrthogonalAction_ker I hIH q hz
  have hvn : ¬ D.V ≤ D.Vplus := by
    intro hv
    have he : D.Vplus = D.V := le_antisymm h.plus_le hv
    rw [he,relIndex_self] at hi
    omega
  obtain ⟨v,hv,hvn⟩ := Set.not_subset.mp hvn
  let a : I := ⟨v,hVI hv⟩
  let b : I := ⟨f v,hBI (mem_map_of_mem f hv)⟩
  have hbn : f v ∉ D.Vplus.map f := by
    rintro ⟨w,hw,he⟩
    exact hvn ((MulAut.conj g).injective he ▸ hw)
  have hseed : (D.Vplus.subgroupOf I) ≤ α.ker := by
    rw [hk]
    exact comap_mono ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  have hseedg : ((D.Vplus.map f).subgroupOf I) ≤ α.ker := by
    rw [hk]
    exact comap_mono ((pair_seed_conjugate_le_closure (D := D) g hg).trans h.UH_le_QH)
  have haimage : (D.V.subgroupOf I).map α = zpowers (α a) :=
    image_eq_zpowers_of_index_two (D.V.subgroupOf I) (D.Vplus.subgroupOf I) α
      (subgroupOf_mono I h.plus_le) (by rw [relIndex_subgroupOf hVI];exact hi) hseed a hv hvn
  have hbimage : ((D.V.map f).subgroupOf I).map α = zpowers (α b) :=
    image_eq_zpowers_of_index_two ((D.V.map f).subgroupOf I) ((D.Vplus.map f).subgroupOf I) α
      (subgroupOf_mono I (map_mono h.plus_le))
      (by rw [relIndex_subgroupOf hBI,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective];exact hi)
      hseedg b (mem_map_of_mem f hv) hbn
  have hgen : α.range = zpowers (α a) ⊔ zpowers (α b) := by
    rw [MonoidHom.range_eq_map,←haimage,←hbimage,←Subgroup.map_sup,
      ←subgroupOf_sup hVI hBI,subgroupOf_self]
  have ha2 : a^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian v hv)
  have hb2 : b^2=1 := by
    apply Subtype.ext
    change (f v)^2=1
    rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian v hv,map_one]
  have hPQ : P ≤ D.QH := h.UH_le_QH
  have hcomm := h.core_module_commutator_le_seed hi hn
  have hcommg : ⁅D.QH,D.V.map f⁆ ≤ D.Vplus.map f := by
    have hm := map_mono (f := f) hcomm
    have hQ : D.QH.map f = D.QH :=
      mem_normalizer_iff_map_conj_eq.mp (H_normalizes_QH (D := D) hg)
    rwa [map_commutator,hQ] at hm
  have hsing (x : I) (W : Subgroup G) (helem : IsElementaryAbelian 2 W)
      (hbound : ∀ p ∈ P, ⁅(x:G),p⁆ ∈ W) :
      ∀ v, BinaryFourPlus.q ((BinaryFourPlus.wreathToIsometry (α x)).val v-v)=0 := by
    apply q.wreath_singular_displacement (seedConjugation I P n x)
    intro p
    apply Subtype.ext
    change (((x:G)*(p:G)*(x:G)⁻¹)*(p:G)⁻¹)^2=1
    let := helem
    exact elemPow_eq_one_of_isElementaryAbelian _ (hbound p p.property)
  refine ⟨α a,α b,by rw [←map_pow,ha2,map_one],by rw [←map_pow,hb2,map_one],?_,?_,hgen⟩
  · apply hsing a D.Vplus (IsElementaryAbelian.of_le h.plus_le)
    intro p hp'
    rw [←commutatorElement_inv]
    exact D.Vplus.inv_mem (hcomm (commutator_mem_commutator (hPQ hp') hv))
  · let : IsElementaryAbelian 2 (D.V.map f) := IsElementaryAbelian.map f
    apply hsing b (D.Vplus.map f) (IsElementaryAbelian.of_le (map_mono h.plus_le))
    intro p hp'
    rw [←commutatorElement_inv]
    exact (D.Vplus.map f).inv_mem
      (hcommg (commutator_mem_commutator (hPQ hp') (mem_map_of_mem f hv)))

theorem closure_pair_star_symmetricThree
    (hi : D.Vplus.relIndex D.V = 2) (hV : ¬D.V≤D.QH)
    (g : G) (hg : g ∈ D.H)
    (q : QuaternionCentralProductData D.UH)
    (hz : (center D.UH).map D.UH.subtype=D.V₁)
    (hn : ¬ IsPGroup 2 (((D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom).subgroupOf D.H).map
      (QuotientGroup.mk' (pCore 2 D.H)))) :
    Nonempty ((((D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom).subgroupOf D.H).map
      (QuotientGroup.mk' (pCore 2 D.H))) ≃* Equiv.Perm (Fin 3)) := by
  let I := D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom
  have hIH : I≤D.H := sup_le h.V_le_H (by
    rintro _ ⟨v,hv,rfl⟩
    exact D.H.mul_mem (D.H.mul_mem hg (h.V_le_H hv)) (D.H.inv_mem hg))
  let e := h.closureOrthogonalEquiv I hIH q hz
  obtain ⟨a,b,ha,hb,hsa,hsb,he⟩ := h.closure_pair_orthogonal_generators hi hV g hg q hz hIH
  let f := e.trans (MulEquiv.subgroupCongr he)
  have hab : ¬ IsPGroup 2 (zpowers a ⊔ zpowers b : Subgroup BinaryFourPlus.Wreath) :=
    fun hh => hn (hh.of_equiv f.symm)
  obtain ⟨j⟩ := BinaryFourPlus.symmetricThree_of_singular_involutions a b ha hb hsa hsb hab
  exact ⟨f.trans j⟩

end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
end
