module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingFactorization
public import Theory.Frattini.ConjugateCentralFactors

/-!
# Frattini invariance in the alternating-five branch of C.5.6

The two conjugate cores have central elementary supplements over their
intersection, so their embedded Frattini subgroups coincide. The original
product Q = UD identifies this common Frattini subgroup with Φ(D).
All factorization inputs are discharged by the preceding source module.

Source: Aschbacher–Smith, C.5.6(4), printed p.157.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.frattini_invariant (h : AlternatingPairSetup R K L)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
    ((frattini D).map D.subtype).map (MulAut.conj x⁻¹).toMonoidHom =
      (frattini D).map D.subtype := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let Q := (K ⊔ S).pCoreIn 2
  let D := S ⊓ centralizer (K : Set G)
  have hSmap : S.map (MulAut.conj x⁻¹).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp
      (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx))
  have hU : IsElementaryAbelian 2 U := by
    let := h.block.2.1.elementary
    exact IsElementaryAbelian.map K.subtype
  have hSQ : S ≤ normalizer (Q : Set G) :=
    (le_sup_right : S ≤ K ⊔ S).trans ((K ⊔ S).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (K ⊔ S) (pCore 2 (K ⊔ S : Subgroup G))))
  exact frattini_conjugate_central_factors S U Q D (MulAut.conj x⁻¹) hSmap
    h.core h.product (h.centralizer_centralizes_conjugate x hx hnc)
    (h.first_factorization x hx hnc) hU (isPGroup_pCoreIn 2 (K ⊔ S)) hSQ
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
