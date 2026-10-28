module
public import CFSG.Quasithin.ChapterF.Section09.ConjugatePair.Action

/-!
# Singular involution generators of the original pair action

Choose one element outside the index-two seed. Its conjugate supplies the
second generator. The seed lies in the pair action kernel, and the full core
commutator bound puts every displacement in the appropriate elementary seed.
Thus the range is a literal two-generator subgroup of O₄⁺(2).
Source: Aschbacher–Smith F.9.5(6.i), printed p.319.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} (h : D.Hypothesis)
include h

/-- The pair's orthogonal range has two original singular involution generators. -/
theorem pair_orthogonal_generators
    (hi : D.Vplus.relIndex D.V = 2) (hcard : Nat.card D.V = 16)
    (hp : ∀ g ∈ D.H, D.V₁ < D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom →
      IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G))
    (hc : ⁅D.V,D.H ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁)
    (g : G) (hg : g ∈ D.H)
    (hn : ¬ IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G))
    (q : QuaternionCentralProductData
      (D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    let I := D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom
    let P := D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom
    let α := seedOrthogonalAction I P (h.pair_normalizes_seed_join hi g hg hn) q
    ∃ a b : BinaryFourPlus.Wreath, a^2=1 ∧ b^2=1 ∧
      (∀ v, BinaryFourPlus.q ((BinaryFourPlus.wreathToIsometry a).val v-v)=0) ∧
      (∀ v, BinaryFourPlus.q ((BinaryFourPlus.wreathToIsometry b).val v-v)=0) ∧
      α.range = zpowers a ⊔ zpowers b := by
  dsimp only
  let := h.elementary
  let f := (MulAut.conj g).toMonoidHom
  let I := D.V ⊔ D.V.map f
  let P := D.Vplus ⊔ D.Vplus.map f
  have hVI : D.V ≤ I := le_sup_left
  have hBI : D.V.map f ≤ I := le_sup_right
  have hWI : D.Vplus ≤ I := h.plus_le.trans hVI
  have hEI : D.Vplus.map f ≤ I := (map_mono h.plus_le).trans hBI
  have hIH : I ≤ D.H := sup_le h.V_le_H (by
    rintro _ ⟨a,ha,rfl⟩
    exact D.H.mul_mem (D.H.mul_mem hg (h.V_le_H ha)) (D.H.inv_mem hg))
  let n := h.pair_normalizes_seed_join hi g hg hn
  let α := seedOrthogonalAction I P n q
  have hk : α.ker = D.QH.subgroupOf I := by
    rw [seedOrthogonalAction_ker I P D.V₁ n q (h.pair_seed_center hp hc g hg hn)
      (hIH.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))),
      h.pair_seed_kernel hi hcard hp hc g hg hn]
    ext x
    exact and_iff_right x.property
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
  have hPQ : P ≤ D.QH := sup_le ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
    ((pair_seed_conjugate_le_closure (D := D) g hg).trans h.UH_le_QH)
  have hcomm := h.core_module_commutator_le_seed hi (pair_module_not_le_core (D := D) g hg hn)
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
end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
