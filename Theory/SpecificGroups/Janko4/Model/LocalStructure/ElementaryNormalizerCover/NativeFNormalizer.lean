module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NativeFBranch
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.Container

/-!
# Whole normalizers in the native F branch

The two checked exterior-action orbits place every second-class involution
of F at the literal nondecomposable representative, which lies in E. The
transporter belongs to the full normalizer of F. After moving X with that
same transporter, the proved native occurrence and centralizer theorems give
N(X) inside the actual linear-five local or a conjugate of the Mathieu local.
All earlier positioning, occurrence and centralizer premises are discharged.

The result covers every subgroup of a conjugate of F containing a 2B element.
The maximal-two-local and radical applications preserve the actual ambient
conjugator, the full local normalizer and both intrinsic and embedded cores.
It remains necessary to prove that the remaining source configurations reach
this branch or the other named locals; no global four-local cover is asserted.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Proposition
2.2.3, p.491, the F branch. Native class and action certificates, including
their ATLAS attribution, are reused through the LinearFive imports.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover
open LinearFive LinearFive.NativeNormalizer
open Representation.SL5ExteriorSquare.TwoGeneratorRecognition
attribute [local irreducible] modelGroup matrixA matrixB

/-- The marked second-class representative in F is literally in the Mathieu kernel. -/
theorem nativeF_second_rep_mem_kernel : (nondecomposableRep : Model) ∈ embeddedKernel := by
  have hr : (nondecomposableRep : Model) = (kernelValue 51 : Model) := by
    change fValue 1 = _
    rw [show (1 : ℕ) = 2^(0 : Fin 10).val from rfl, fValue_basis]
    rfl
  rw [hr]
  exact mem_map_of_mem M.subtype (Simplicity.Max1Fusion.KernelOrbits.maskValue
    matrixA_mul_self matrixB_pow_four 51).property

/-- An arbitrary nonfirst-class involution of F can be positioned in E by
an element of the full F-normalizer, keeping the native F fixed. -/
theorem nativeF_nonfirst_transporter (t : Model) (htF : t ∈ nativeF)
    (ht2 : orderOf t = 2) (hnt : ¬ IsConj a t) :
    ∃ n : normalizer (nativeF : Set Model),
      (MulAut.conj (n : Model)) (nondecomposableRep : Model) = t := by
  have ht1 : (⟨t,htF⟩ : F) ≠ 1 := by
    intro h
    have he : t = 1 := congrArg Subtype.val h
    rw [he,orderOf_one] at ht2
    omega
  rcases cover_nonidentity_from_native_actions F exteriorMarking
    (normalizerElement 0) (normalizerElement 1)
    (exterior_conjugation 0) (exterior_conjugation 1)
    decomposableRep nondecomposableRep decomposableRep_marking nondecomposableRep_marking
    ⟨t,htF⟩ ht1 with ⟨n,hn⟩ | ⟨n,hn⟩
  · exact (hnt (decomposableRep_first.symm.trans (isConj_iff.mpr ⟨n,hn⟩))).elim
  · exact ⟨n,hn⟩

/-- Whole-normalizer coverage for every subgroup of F containing a 2B member.
No centralizer-container, occurrence or positioning premise remains. -/
theorem nativeF_nonfirst_normalizer_cover (X : Subgroup Model) (hXF : X ≤ nativeF)
    (t : Model) (htX : t ∈ X) (ht2 : orderOf t = 2) (hnt : ¬ IsConj a t) :
    ∃ n : normalizer (nativeF : Set Model),
      normalizer (X : Set Model) ≤ LinearFive.M_F ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj (n : Model)).toMonoidHom := by
  obtain ⟨n,hn⟩ := nativeF_nonfirst_transporter t (hXF htX) ht2 hnt
  let e := MulAut.conj (n : Model)⁻¹
  let Y := X.map e.toMonoidHom
  have hYF : Y ≤ nativeF := by
    have hm := map_mono (f := e.toMonoidHom) hXF
    have he := mem_normalizer_iff_map_conj_eq.mp ((normalizer (nativeF : Set Model)).inv_mem n.property)
    exact he ▸ hm
  have hrepY : (nondecomposableRep : Model) ∈ Y := by
    refine ⟨t,htX,?_⟩
    rw [← hn]
    simp [e,mul_assoc]
  have hrep2 : orderOf (nondecomposableRep : Model) = 2 := by
    have h := (MulAut.conj (n : Model)).orderOf_eq (nondecomposableRep : Model)
    exact (hn ▸ h).symm.trans ht2
  have hnrep : ¬ IsConj a (nondecomposableRep : Model) := by
    intro h
    exact hnt (h.trans (isConj_iff.mpr ⟨n,hn⟩))
  have hback : Y.map (MulAut.conj (n : Model)).toMonoidHom = X := by
    rw [map_map]
    have he : (MulAut.conj (n : Model)).toMonoidHom.comp e.toMonoidHom =
        MonoidHom.id Model := by ext x; simp [e,mul_assoc]
    rw [he,map_id]
  have hrows : normalizer (Y : Set Model) ≤ LinearFive.M_F ∨
      normalizer (Y : Set Model) ≤ max1 := by
    by_cases hYE : Y ≤ embeddedKernel
    · exact Or.inr (normalizer_le_mathieu_of_nonfirst_kernel_involution
        Y hYE _ hrepY hrep2 hnrep)
    · exact LinearFive.Geometry.source_F_normalizer_alternatives
        Y hYF hYE _ hrepY nativeF_second_rep_mem_kernel hrep2 hnrep
  refine ⟨n,?_⟩
  rcases hrows with h | h
  · left
    have hm := map_mono (f := (MulAut.conj (n : Model)).toMonoidHom) h
    rw [map_equiv_normalizer_eq,hback] at hm
    have hnMF : (n : Model) ∈ LinearFive.M_F := by
      rw [← nativeF_fullNormalizer_eq]
      exact n.property
    have he := mem_normalizer_iff_map_conj_eq.mp (LinearFive.M_F.le_normalizer hnMF)
    exact he ▸ hm
  · right
    have hm := map_mono (f := (MulAut.conj (n : Model)).toMonoidHom) h
    rwa [map_equiv_normalizer_eq,hback] at hm


private theorem conjugate_comp (X : Subgroup Model) (g h : Model) :
    (X.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      X.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

/-- The unpositioned F branch, with the actual ambient conjugator retained.
The second-class witness belongs to X itself; it need not lie in the chosen E. -/
theorem nativeF_conjugate_nonfirst_normalizer_cover
    (X : Subgroup Model) (g : Model)
    (hXF : X ≤ nativeF.map (MulAut.conj g).toMonoidHom)
    (t : Model) (htX : t ∈ X) (ht2 : orderOf t = 2) (hnt : ¬ IsConj a t) :
    ∃ k : Model,
      normalizer (X : Set Model) ≤ LinearFive.M_F.map (MulAut.conj k).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj k).toMonoidHom := by
  let e := MulAut.conj g⁻¹
  let Y := X.map e.toMonoidHom
  have hYF : Y ≤ nativeF := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy,he⟩ := hXF hx
    have hy' : e x = y := by rw [← he]; simp [e,mul_assoc]
    exact hy' ▸ hy
  have htY : e t ∈ Y := mem_map_of_mem _ htX
  have hte2 : orderOf (e t) = 2 := (e.orderOf_eq t).trans ht2
  have hnte : ¬ IsConj a (e t) := by
    intro h
    exact hnt (h.trans (isConj_iff.mpr ⟨g,by simp [e,mul_assoc]⟩))
  have hback : Y.map (MulAut.conj g).toMonoidHom = X := by
    change (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = X
    rw [conjugate_comp,mul_inv_cancel]
    exact mem_normalizer_iff_map_conj_eq.mp (normalizer (X : Set Model)).one_mem
  obtain ⟨n,hn | hn⟩ := nativeF_nonfirst_normalizer_cover Y hYF (e t) htY hte2 hnte
  · refine ⟨g,Or.inl ?_⟩
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hn
    rwa [map_equiv_normalizer_eq,hback] at hm
  · refine ⟨g*(n : Model),Or.inr ?_⟩
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hn
    rwa [map_equiv_normalizer_eq,hback,conjugate_comp] at hm

/-- Maximality among two-locals closes the F branch with an equality of actual
ambient subgroups. No maximality among all proper subgroups is used. -/
theorem maximal_twoLocal_of_nativeF_conjugate
    (X H : Subgroup Model) (g : Model)
    (hXF : X ≤ nativeF.map (MulAut.conj g).toMonoidHom)
    (t : Model) (htX : t ∈ X) (ht2 : orderOf t = 2) (hnt : ¬ IsConj a t)
    (hH : IsMaximalTwoLocal H) (hHX : H = normalizer (X : Set Model)) :
    ∃ k : Model, H = LinearFive.M_F.map (MulAut.conj k).toMonoidHom ∨
      H = max1.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨k,hk | hk⟩ := nativeF_conjugate_nonfirst_normalizer_cover X g hXF t htX ht2 hnt
  · exact ⟨k,Or.inl (hH.eq_of_le (nativeF_generated_isTwoLocal.map_equiv (MulAut.conj k))
      (hHX ▸ hk))⟩
  · exact ⟨k,Or.inr (hH.eq_of_le (embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj k))
      (hHX ▸ hk))⟩

/-- The actual radical consumer of the unpositioned native F branch. The
chosen conjugate contains the whole normalizer of P; its local normalizer and
full normalizer core map to precisely the original ambient subgroups. -/
theorem radical_local_of_nativeF_conjugate
    (P X : Subgroup Model) (hP : P.IsPRadical 2) (g : Model)
    (hXF : X ≤ nativeF.map (MulAut.conj g).toMonoidHom)
    (t : Model) (htX : t ∈ X) (ht2 : orderOf t = 2) (hnt : ¬ IsConj a t)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    ∃ (k : Model) (H : Subgroup Model), IsTwoLocal H ∧
      (H = LinearFive.M_F.map (MulAut.conj k).toMonoidHom ∨
        H = max1.map (MulAut.conj k).toMonoidHom) ∧
      normalizer (P : Set Model) ≤ H ∧ P ≤ H ∧
      (normalizer (P.subgroupOf H : Set H)).map H.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf H).IsPRadical 2 ∧
      (normalizer (P.subgroupOf H : Set H)).pCoreIn 2 = P.subgroupOf H ∧
      ((normalizer (P.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = P := by
  obtain ⟨k,hk⟩ := nativeF_conjugate_nonfirst_normalizer_cover X g hXF t htX ht2 hnt
  obtain ⟨H,hH,hrow,hNH⟩ : ∃ H : Subgroup Model, IsTwoLocal H ∧
      (H = LinearFive.M_F.map (MulAut.conj k).toMonoidHom ∨
        H = max1.map (MulAut.conj k).toMonoidHom) ∧ normalizer (P : Set Model) ≤ H := by
    rcases hk with h | h
    · exact ⟨_,nativeF_generated_isTwoLocal.map_equiv (MulAut.conj k),Or.inl rfl,hNX.trans h⟩
    · exact ⟨_,embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj k),Or.inr rfl,hNX.trans h⟩
  have hPH := P.le_normalizer.trans hNH
  have hN := hNH.trans H.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf H hPH hN
  refine ⟨k,H,hH,hrow,hNH,hPH,?_,hP.subgroupOf_of_normalizer_normalizes H hPH hN,hcore,?_⟩
  · rw [← subgroupOf_normalizer_eq hPH,map_subgroupOf_eq_of_le hNH]
  · rw [hcore,map_subgroupOf_eq_of_le hPH]

end Janko4.LocalStructure.ElementaryNormalizerCover
