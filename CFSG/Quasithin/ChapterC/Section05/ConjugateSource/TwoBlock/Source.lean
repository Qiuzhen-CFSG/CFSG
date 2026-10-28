module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.TwoBlock.Terminal
/-!
# The complete two-block alternating-five C.5.6(7) conclusion

The proved full centralizer identification supplies D=C_R(K), and the genuine
involution-cover argument supplies U=O₂(K). The earlier source C.5.4.4 identity
then gives O₂(KR)=UD. These are assembled with the proved Frattini,
intersection, Thompson and invariant maximum-elementary family assertions.
The earlier marked setup and C.5.4.4 producer retain their original obligations.

Source: Aschbacher–Smith, C.5.6(7)(iii), printed pp.156 and158–160.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.source_C56_two_block_7
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (H M T_H : Subgroup G) (hRTH : R ≤ T_H) (hTHM : T_H ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (hTHKL : T_H ≤ normalizer ((K ⊔ L : Subgroup G) : Set G))
    (hH : H = (K ⊔ L) ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M ≤ normalizer (W : Set G) → W = ⊥)
    (hfull : R ⊓ centralizer (sourceModule K ⊔ sourceModule L : Subgroup G) =
      ((K ⊔ L) ⊔ R).pCoreIn 2)
    (x : G) (hx : x ∈ M) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let S := ChapterB.baumann R
    let U := sourceModule K ⊔ sourceModule L
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
    (K ⊔ L).pCoreIn 2 = U ∧
      (frattini D).map D.subtype = ⊥ ∧
      D ⊓ D.map (MulAut.conj x⁻¹).toMonoidHom = ⊥ ∧
      D = R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G) ∧
      ((K ⊔ L) ⊔ R).pCoreIn 2 = U ⊔ D ∧
      ((K ⊔ L) ⊔ R).pCoreIn 2 ∈ elementaryAbelianMaxSubgroups R ∧
      S = (U ⊔ V) ⊔ D ∧ S = elementaryAbelianMaxJ R ∧
      {A ∈ elementaryAbelianMaxSubgroups R | T_H ≤ normalizer (A : Set G)} =
        {U ⊔ D,V ⊔ D} := by
  have hp := h.two_block_source_product h' H M T_H hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc
  have ht' := h.two_block_full_centralizer_eq h' H M T_H (hRTH.trans hTHM) hTHM hMR hTHKL hH hno
    x hx hindex hpair ht hnc
  have hf := h.two_block_invariant_family h' H M T_H hRTH hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc
  have hcore := h.two_block_core_eq_module h' M T_H x hx (hMR hx) hindex hpair ht hnc
  have hc := hfull.symm.trans ht'.1
  refine ⟨hcore,hp.2.2.2.1,hp.2.2.2.2.1,ht'.2.symm,hc.trans hp.1,?_,hp.2.2.1,hf.2.1,?_⟩
  · rw [hc]
    exact hf.1
  · rw [hf.2.2.2,← hf.2.2.1,hp.1]
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
