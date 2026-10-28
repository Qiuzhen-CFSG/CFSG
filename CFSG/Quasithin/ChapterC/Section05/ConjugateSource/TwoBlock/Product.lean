module
public import Theory.GroupAction.IndexTwoIntersectionCore
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingOrbit
public import Theory.Frattini.ConjugateCentralFactors

/-!
# The full product and Frattini subgroup in the two-block A₅ case

The two individual core products intersect to give C_S(U₁U₂)=U₁U₂D,
where D=C_S(K₁K₂). The conjugate factors supply S=UˣQ. The actual four-module
action transfers the original noncommutation to the second block, so no
second noncommutation premise is assumed. The central-factor Frattini theorem
then preserves Φ(D), and the original index-two/common-normal hypothesis
forces Φ(D)=1. In particular the full core is elementary abelian.

Source: Aschbacher–Smith, C.5.6(7), printed pp.158–159.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G]

private theorem centralizer_join (A B : Subgroup G) :
    centralizer (A ⊔ B : Subgroup G) = centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf (centralizer_le (show A ≤ A ⊔ B from le_sup_left))
      (centralizer_le (show B ≤ A ⊔ B from le_sup_right))
  · apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)

private theorem product_intersection (A B D E : Subgroup G)
    (hDA : D ≤ normalizer (A : Set G)) (hEB : E ≤ normalizer (B : Set G))
    (hAE : A ≤ E) (hBD : B ≤ D) :
    (A ⊔ D) ⊓ (B ⊔ E) = (A ⊔ B) ⊔ (D ⊓ E) := by
  apply le_antisymm
  · rintro g ⟨hg1, hg2⟩
    have hgm : g ∈ (A : Set G) * (D : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left A D hDA]
      exact hg1
    obtain ⟨a, ha, d, hd, rfl⟩ := hgm
    have hdBE : d ∈ B ⊔ E := by
      simpa using (B ⊔ E).mul_mem ((B ⊔ E).inv_mem ((show E ≤ B ⊔ E from le_sup_right) (hAE ha))) hg2
    have hdm : d ∈ (B : Set G) * (E : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left B E hEB]
      exact hdBE
    obtain ⟨b, hb, e, he, rfl⟩ := hdm
    have heD : e ∈ D := by simpa using D.mul_mem (D.inv_mem (hBD hb)) hd
    have hh := mul_mem_sup (mul_mem_sup ha hb) (show e ∈ D ⊓ E from ⟨heD, he⟩)
    simpa only [mul_assoc] using hh
  · apply sup_le
    · exact sup_le (le_inf le_sup_left (hAE.trans le_sup_right))
        (le_inf (hBD.trans le_sup_right) le_sup_left)
    · exact le_inf (inf_le_left.trans le_sup_right) (inf_le_right.trans le_sup_right)

private theorem span_intersection (S A B Q P : Subgroup G)
    (hS : S = A ⊔ Q) (hS' : S = B ⊔ P)
    (hBQ : B ≤ Q) (hBP : B ≤ normalizer (P : Set G)) :
    S = (A ⊔ B) ⊔ (Q ⊓ P) := by
  have hQ : Q = B ⊔ (Q ⊓ P) := by
    apply le_antisymm
    · intro q hq
      have hm : q ∈ (B : Set G) * (P : Set G) := by
        rw [← coe_mul_of_left_le_normalizer_right B P hBP, ← hS']
        exact (show Q ≤ S from le_sup_right.trans_eq hS.symm) hq
      obtain ⟨b, hb, p, hp, rfl⟩ := hm
      have hpQ : p ∈ Q := by simpa using Q.mul_mem (Q.inv_mem (hBQ hb)) hq
      exact mul_mem_sup hb ⟨hpQ, hp⟩
    · exact sup_le hBQ inf_le_left
  calc
    S = A ⊔ Q := hS
    _ = A ⊔ (B ⊔ (Q ⊓ P)) := congrArg (fun W => A ⊔ W) hQ
    _ = (A ⊔ B) ⊔ (Q ⊓ P) := (sup_assoc _ _ _).symm

theorem FourModuleOrbit.SourceInputs.second_noncommuting {M T U V : Subgroup G} {x : G}
    (h : FourModuleOrbit.SourceInputs M T U V x) :
    ¬ V.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (V : Set G) := by
  obtain ⟨t, ht⟩ := FourModuleOrbit.source_setup h.toInputs
  have htable := ht.table t
  have h02 : FourModuleOrbit.action h.toInputs t 0 = 1 ∧
      FourModuleOrbit.action h.toInputs t 2 = 3 := by
    rcases htable with h0 | h1 | h2 | h3
    · have hh := ht.t_zero
      rw [h0.1] at hh
      contradiction
    · exact ⟨h1.1, h1.2.2.1⟩
    · have hh := ht.t_zero
      rw [h2.1] at hh
      contradiction
    · have hh := ht.t_zero
      rw [h3.1] at hh
      contradiction
  have hh := ht.invariant t 0 2 ht.noncommuting
  rw [h02.1, h02.2] at hh
  change ⁅V, V.map (MulAut.conj x⁻¹).toMonoidHom⁆ ≠ ⊥ at hh
  exact fun hc => hh (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))

variable [Finite G] {R K L : Subgroup G}

private theorem paired_factorization
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (hnc' : ¬ (sourceModule L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule L : Set G)) :
    let S := ChapterB.baumann R
    let U := sourceModule K ⊔ sourceModule L
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let Q := S ⊓ centralizer (U : Set G)
    let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
    Q = U ⊔ D ∧ D ≤ centralizer (V : Set G) ∧ S = V ⊔ Q ∧
      ((frattini D).map D.subtype).map (MulAut.conj x⁻¹).toMonoidHom = (frattini D).map D.subtype := by
  let S := ChapterB.baumann R
  let U₁ := sourceModule K
  let U₂ := sourceModule L
  let V₁ := U₁.map (MulAut.conj x⁻¹).toMonoidHom
  let V₂ := U₂.map (MulAut.conj x⁻¹).toMonoidHom
  let Q₁ := (K ⊔ S).pCoreIn 2
  let Q₂ := (L ⊔ S).pCoreIn 2
  let D₁ := S ⊓ centralizer (K : Set G)
  let D₂ := S ⊓ centralizer (L : Set G)
  let U := U₁ ⊔ U₂
  let Q := S ⊓ centralizer (U : Set G)
  let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
  have hU₁D₂ : U₁ ≤ D₂ := le_inf h.module_le ((map_subtype_le _).trans h'.commute)
  have hU₂D₁ : U₂ ≤ D₁ := le_inf h'.module_le ((map_subtype_le _).trans h.commute)
  have hDi : D = D₁ ⊓ D₂ := by
    dsimp [D, D₁, D₂]
    rw [centralizer_join]
    simp only [inf_assoc, inf_left_comm, inf_left_idem]
  have hQi : Q = Q₁ ⊓ Q₂ := by
    change S ⊓ centralizer (U₁ ⊔ U₂ : Subgroup G) = Q₁ ⊓ Q₂
    rw [centralizer_join]
    have h1 : Q₁ = S ⊓ centralizer (U₁ : Set G) := h.core
    have h2 : Q₂ = S ⊓ centralizer (U₂ : Set G) := h'.core
    rw [h1, h2]
    simp only [inf_assoc, inf_left_comm, inf_left_idem]
  have hD₁U₁ : D₁ ≤ centralizer (U₁ : Set G) :=
    inf_le_right.trans (centralizer_le (map_subtype_le _))
  have hD₂U₂ : D₂ ≤ centralizer (U₂ : Set G) :=
    inf_le_right.trans (centralizer_le (map_subtype_le _))
  have hprod : Q = U ⊔ D := by
    rw [hQi]
    have h1 : Q₁ = U₁ ⊔ D₁ := h.product
    have h2 : Q₂ = U₂ ⊔ D₂ := h'.product
    rw [h1, h2, product_intersection U₁ U₂ D₁ D₂
      (hD₁U₁.trans (Subgroup.centralizer_le_normalizer _))
      (hD₂U₂.trans (Subgroup.centralizer_le_normalizer _)) hU₁D₂ hU₂D₁, ← hDi]
  have hSx : S.map (MulAut.conj x⁻¹).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp
      (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx))
  have hV₂S : V₂ ≤ S := (map_mono h'.module_le).trans_eq hSx
  have hV₂Q₁ : V₂ ≤ Q₁ :=
    (le_inf hV₂S (le_centralizer_iff.mp
      (hU₁D₂.trans (h'.centralizer_centralizes_conjugate x hx hnc')))).trans_eq h.core.symm
  have hSQ₂ : S ≤ normalizer (Q₂ : Set G) :=
    le_sup_right.trans ((L ⊔ S).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (L ⊔ S) (pCore 2 (L ⊔ S : Subgroup G))))
  have hspan : S = U.map (MulAut.conj x⁻¹).toMonoidHom ⊔ Q := by
    change S = (U₁ ⊔ U₂).map (MulAut.conj x⁻¹).toMonoidHom ⊔ Q
    rw [Subgroup.map_sup, hQi]
    exact span_intersection S V₁ V₂ Q₁ Q₂ (h.first_factorization x hx hnc)
      (h'.first_factorization x hx hnc') hV₂Q₁ (hV₂S.trans hSQ₂)
  have hDC : D ≤ centralizer (U.map (MulAut.conj x⁻¹).toMonoidHom : Set G) := by
    change D ≤ centralizer ((U₁ ⊔ U₂).map (MulAut.conj x⁻¹).toMonoidHom : Set G)
    rw [Subgroup.map_sup, centralizer_join, hDi]
    exact le_inf (inf_le_left.trans (h.centralizer_centralizes_conjugate x hx hnc))
      (inf_le_right.trans (h'.centralizer_centralizes_conjugate x hx hnc'))
  have hU : IsElementaryAbelian 2 U := by
    let : IsElementaryAbelian 2 U₁ := by
      let := h.block.2.1.elementary
      exact IsElementaryAbelian.map K.subtype
    let : IsElementaryAbelian 2 U₂ := by
      let := h'.block.2.1.elementary
      exact IsElementaryAbelian.map L.subtype
    exact IsElementaryAbelian.sup_of_le_centralizer (hU₂D₁.trans hD₁U₁)
  have hSQ : S ≤ normalizer (Q : Set G) := by
    rw [hQi]
    have hSQ₁ : S ≤ normalizer (Q₁ : Set G) :=
      le_sup_right.trans ((K ⊔ S).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K ⊔ S) (pCore 2 (K ⊔ S : Subgroup G))))
    exact (le_inf hSQ₁ hSQ₂).trans inf_normalizer_le_normalizer_inf
  exact ⟨hprod, hDC, hspan, frattini_conjugate_central_factors S U Q D (MulAut.conj x⁻¹)
    hSx rfl hprod hDC hspan hU (h.twoGroup.to_le (inf_le_left.trans inf_le_left)) hSQ⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open Subgroup
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.two_block_factorization
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (M T_H : Subgroup G) (x : G) (hx : x ∈ M)
    (hxR : x ∈ normalizer (R : Set G)) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let S := ChapterB.baumann R
    let U := sourceModule K ⊔ sourceModule L
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let Q := S ⊓ centralizer (U : Set G)
    let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
    Q = U ⊔ D ∧ D ≤ centralizer (V : Set G) ∧ S = V ⊔ Q ∧
      ((frattini D).map D.subtype).map (MulAut.conj x⁻¹).toMonoidHom = (frattini D).map D.subtype :=
  paired_factorization h h' x hxR hnc (FourModuleOrbit.SourceInputs.second_noncommuting
    (h.fourModuleSourceInputs h'.module_le M T_H x hx hxR hindex hpair ht hnc))
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open Subgroup
variable {G : Type*} [Group G]

private theorem no_common_normal_index_two
    (R H M T P : Subgroup G) (hPM : P ≤ R)
    (hHP : H ≤ normalizer (P : Set G)) (hTP : T ≤ normalizer (P : Set G))
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M ≤ normalizer (W : Set G) → W = ⊥)
    (hindex : T.relIndex M = 2) (x : G) (hx : x ∈ M) (hxT : x ∉ T)
    (hxP : x ∈ normalizer (P : Set G)) : P = ⊥ := by
  apply hno P hPM hHP
  intro g hg
  by_cases hgT : g ∈ T
  · exact hTP hgT
  · have hm : g * x⁻¹ ∈ T := by
      have hi : (T.subgroupOf M).index = 2 := hindex
      exact (mul_mem_iff_of_index_two hi (a := (⟨g, hg⟩ : M))
        (b := (⟨x⁻¹, M.inv_mem hx⟩ : M))).mpr
        (iff_of_false hgT (fun hi => hxT (by
          have hi' : x⁻¹ ∈ T := hi
          simpa only [inv_inv] using T.inv_mem hi')))
    have hh := (normalizer (P : Set G)).mul_mem (hTP hm) hxP
    simpa using hh

variable [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.two_block_source_product
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (H M T_H : Subgroup G) (hTHM : T_H ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (hTHKL : T_H ≤ normalizer ((K ⊔ L : Subgroup G) : Set G))
    (hH : H = (K ⊔ L) ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M ≤ normalizer (W : Set G) → W = ⊥)
    (x : G) (hx : x ∈ M) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let S := ChapterB.baumann R
    let U := sourceModule K ⊔ sourceModule L
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let Q := S ⊓ centralizer (U : Set G)
    let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
    Q = U ⊔ D ∧ D ≤ centralizer (V : Set G) ∧ S = (U ⊔ V) ⊔ D ∧
      (frattini D).map D.subtype = ⊥ ∧
      D ⊓ D.map (MulAut.conj x⁻¹).toMonoidHom = ⊥ ∧ IsElementaryAbelian 2 Q := by
  let S := ChapterB.baumann R
  let U := sourceModule K ⊔ sourceModule L
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  let Q := S ⊓ centralizer (U : Set G)
  let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
  let P := (frattini D).map D.subtype
  have hc := h.two_block_factorization h' M T_H x hx (hMR hx) hindex hpair ht hnc
  have hd := h.fourModuleSourceInputs h'.module_le M T_H x hx (hMR hx) hindex hpair ht hnc
  have hTD : T_H ≤ normalizer (D : Set G) := by
    have hnC : normalizer ((K ⊔ L : Subgroup G) : Set G) ≤
        normalizer (centralizer ((K ⊔ L : Subgroup G) : Set G) : Set G) :=
      (normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer ((K ⊔ L : Subgroup G) : Set G))).mp inferInstance
    exact (le_inf ((hTHM.trans hMR).trans (Stellmacher.normalizer_le_normalizer_baumann R))
      (hTHKL.trans hnC)).trans inf_normalizer_le_normalizer_inf
  have hTP : T_H ≤ normalizer (P : Set G) :=
    hTD.trans (normalizer_le_normalizer_characteristic_image D (frattini D))
  have hKLP : K ⊔ L ≤ normalizer (P : Set G) :=
    (le_centralizer_iff.mp (show P ≤ centralizer ((K ⊔ L : Subgroup G) : Set G) from
      (map_subtype_le _).trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  have hxP : x ∈ normalizer (P : Set G) := by
    have hh : x⁻¹ ∈ normalizer (P : Set G) :=
      mem_normalizer_iff_map_conj_eq.mpr hc.2.2.2
    simpa only [inv_inv] using (normalizer (P : Set G)).inv_mem hh
  have hphi : P = ⊥ := no_common_normal_index_two R H M T_H P
    ((map_subtype_le _).trans (inf_le_left.trans inf_le_left))
    (hH ▸ sup_le hKLP hTP) hTP hno hindex x hx hd.x_outside hxP
  let I := D ⊓ D.map (MulAut.conj x⁻¹).toMonoidHom
  have hMI : M ≤ normalizer (I : Set G) :=
    index_two_conjugate_intersection_normalized M T_H D hTHM hindex hTD x hx hd.x_outside
  have hKLI : K ⊔ L ≤ normalizer (I : Set G) :=
    (le_centralizer_iff.mp (show I ≤ centralizer ((K ⊔ L : Subgroup G) : Set G) from
      inf_le_left.trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  have hI : I = ⊥ := hno I (inf_le_left.trans (inf_le_left.trans inf_le_left))
    (hH ▸ sup_le hKLI (hTHM.trans hMI)) hMI
  have hU : IsElementaryAbelian 2 U := by
    let : IsElementaryAbelian 2 (sourceModule K) := by
      let := h.block.2.1.elementary
      exact IsElementaryAbelian.map K.subtype
    let : IsElementaryAbelian 2 (sourceModule L) := by
      let := h'.block.2.1.elementary
      exact IsElementaryAbelian.map L.subtype
    exact IsElementaryAbelian.sup_of_le_centralizer
      ((map_subtype_le _).trans (h.commute.trans (centralizer_le (map_subtype_le _))))
  have hD : IsElementaryAbelian 2 D := by
    let : Fact (IsPGroup 2 D) := ⟨h.twoGroup.to_le (inf_le_left.trans inf_le_left)⟩
    apply (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
    exact (map_injective D.subtype_injective) (hphi.trans (map_bot D.subtype).symm)
  have hDU : D ≤ centralizer (U : Set G) :=
    inf_le_right.trans (centralizer_le (sup_le ((map_subtype_le _).trans le_sup_left)
      ((map_subtype_le _).trans le_sup_right)))
  have hQ : IsElementaryAbelian 2 Q := by
    let := hU
    let := hD
    have hq : Q = U ⊔ D := hc.1
    rw [hq]
    exact IsElementaryAbelian.sup_of_le_centralizer hDU
  refine ⟨hc.1, hc.2.1, ?_, hphi, hI, hQ⟩
  change S = (U ⊔ V) ⊔ D
  have hs : S = V ⊔ Q := hc.2.2.1
  have hq : Q = U ⊔ D := hc.1
  rw [hs, hq]
  ac_rfl
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
