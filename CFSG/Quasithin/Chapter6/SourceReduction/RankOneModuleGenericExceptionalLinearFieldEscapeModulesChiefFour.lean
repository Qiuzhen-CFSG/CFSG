module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesChiefPlane
public import Theory.GroupAction.SL2FourCubicLength
public import Theory.GroupTheory.AbelianConjugateSpan

/-!
# The second cubic factor inside the original two-core

Local characteristic two puts the original central involution in
O₂(LT). Its moving four-plane is fixed by T∩L and centralizes O₂(LT).
The plane is its own cubic commutator and therefore lies in L. Its
literal L-span is normal, abelian and contained in O₂(L). The SL₂(4)
cubic-length obstruction forces this span, hence O₂(L), to contribute
at least two noncentral cubic factors.

No new constituent or quotient action is selected. This supplies the
field-four kernel contribution in Aschbacher--Smith 5.1.23, printed
pp.645--646, refs/quasithin.pdf. The Chapter 12 consumer combines it
with the original Sylow quotient and exact opposite-image rank formula.
-/

public noncomputable section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- The original moving plane forces two cubic factors in O₂(L), over F₄. -/
theorem LocalData.core_cubic_length_ge_two_of_field_four
    (d : LocalData T H C z)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4)
    (hC : Nat.card C = 3) (hCL : C ≤ L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hCP : C ≤ normalizer (((T : Subgroup G) ⊓ L) : Set G))
    (hchar : centralizer (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) :
      Set (L ⊔ (T : Subgroup G) : Subgroup G)) ≤ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) :
    2 ≤ conjugationCubicLength C (L.pCoreIn 2) := by
  let J := L ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  let E := plane C z
  let W := conjugateSpanBy E L
  have hQT : Q ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow J (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hz := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp d.point_mem
  have hzQ : z ∈ Q := by
    apply mem_map_of_mem J.subtype (x := ⟨z,mem_sup_right hz.1⟩)
    apply hchar
    intro q hq
    apply Subtype.ext
    exact hz.2.2 q (hQT (mem_map_of_mem J.subtype hq))
  have hJQ : J ≤ normalizer (Q : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hCQ : C ≤ normalizer (Q : Set G) := hCL.trans (le_sup_left.trans hJQ)
  have hEQ : E ≤ Q := conjugateSpanBy_le (zpowers_le.mpr hzQ) hCQ
  have hQE : Q ≤ centralizer (E : Set G) := by
    apply le_centralizer_conjugateSpanBy_of_normalizes Q (zpowers z) C hCQ
    apply le_centralizer_iff.mpr
    apply zpowers_le.mpr
    intro q hq
    exact hz.2.2 q (hQT hq)
  have hWQ : W ≤ Q := conjugateSpanBy_le hEQ (le_sup_left.trans hJQ)
  have hWC : W ≤ centralizer (Q : Set G) := conjugateSpanBy_le
    (le_centralizer_iff.mp hQE)
    ((le_sup_left.trans hJQ).trans (normalizer_le_normalizer_centralizer Q))
  let : IsMulCommutative W := le_centralizer_iff_isMulCommutative.mp
    (hWC.trans (centralizer_le hWQ))
  let : IsElementaryAbelian 2 E := d.g2.elementary
  have hCE : C ≤ normalizer (E : Set G) := le_normalizer_conjugateSpanBy _ _
  have hthree : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by simpa using hC)
  have hEcomm : ⁅E,C⁆ = E :=
    Matrix.SpecialLinearGroup.CubicChiefCount.moved_eq_plane C E E hthree
      d.g2.elementary.isPGroup le_rfl hCE hCE d.plane_card
      (d.plane_cubic_length hC) (by rw [d.plane_cubic_length hC])
  have hEL : E ≤ L := by
    rw [← hEcomm]
    exact (commutator_mono le_rfl hCL).trans
      (le_normalizer_iff_commutator_le_right.mp (d.g2.V_le_T.trans hTL))
  have hWL : W ≤ L := conjugateSpanBy_le_self hEL
  have hWcore : W ≤ L.pCoreIn 2 :=
    (le_inf hWL hWQ).trans (inf_pCoreIn_le_of_le 2 (show L ≤ J from le_sup_left))
  have hLW : L ≤ normalizer (W : Set G) := le_normalizer_conjugateSpanBy _ _
  have hEW : E ≤ W := le_conjugateSpanBy _ _
  have hRE : (T : Subgroup G) ⊓ L ≤ centralizer (E : Set G) := by
    apply le_centralizer_conjugateSpanBy_of_normalizes _ (zpowers z) C hCP
    apply le_centralizer_iff.mpr
    apply zpowers_le.mpr
    intro t ht
    exact hz.2.2 t ht.1
  obtain ⟨F,_,_,hF,⟨e₀⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    simpa only [Nat.card_eq_fintype_card,show (2 : ℕ) ^ 2 = 4 from by decide] using hF)
  let e := e₀.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  let q : L →* SL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  have hPR : (P : Subgroup L) = ((T : Subgroup G) ⊓ L).subgroupOf L := by
    rw [hP]
    ext x
    change (x : G) ∈ (T : Subgroup G) ↔ (x : G) ∈ (T : Subgroup G) ⊓ L
    exact ⟨fun hx => ⟨hx,x.property⟩,fun hx => hx.1⟩
  have hAP : C.subgroupOf L ≤ normalizer (P : Set L) := by
    change C.subgroupOf L ≤ normalizer ((P : Subgroup L) : Set L)
    rw [hPR]
    apply le_normalizer_iff.mpr
    intro a ha x hx
    have haC : (a : G) ∈ C := ha
    have hxR : (x : G) ∈ (T : Subgroup G) ⊓ L := hx
    change (a : G) * (x : G) * (a : G)⁻¹ ∈ (T : Subgroup G) ⊓ L
    exact (mem_normalizer_iff.mp (hCP haC) (x : G)).mp hxR
  let : (W.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer hLW
  let : IsMulCommutative (W.subgroupOf L) :=
    IsMulCommutative.of_comm fun x y => (subgroupOfEquivOfLe hWL).injective
      (by simp only [map_mul,mul_comm])
  have hWtwo : IsPGroup 2 (W.subgroupOf L) :=
    (T.isPGroup'.to_le (hWQ.trans hQT)).of_injective
      (subgroupOfEquivOfLe hWL).toMonoidHom (subgroupOfEquivOfLe hWL).injective
  have hAE : C.subgroupOf L ≤ normalizer (E.subgroupOf L : Set L) := by
    apply le_normalizer_iff.mpr
    intro a ha x hx
    exact (mem_normalizer_iff.mp (hCE ha) (x : G)).mp hx
  have hPE : (P : Subgroup L) ≤ centralizer (E.subgroupOf L : Set L) := by
    rw [hPR]
    intro p hp v hv
    exact Subtype.ext (hRE hp v hv)
  have hc := Matrix.SpecialLinearGroup.CubicChiefCount.length_ge_two hF q hq
    (hk.symm ▸ pCore_isPGroup) P (C.subgroupOf L) (W.subgroupOf L) (E.subgroupOf L)
    ((Nat.card_congr (subgroupOfEquivOfLe hCL).toEquiv).trans hC) hWtwo hAP
    (comap_mono hEW) hAE ((Nat.card_congr (subgroupOfEquivOfLe hEL).toEquiv).trans d.plane_card)
    (by rw [CubicComparison.length_subgroupOf C E L hCL hEL]; exact d.plane_cubic_length hC) hPE
  rw [CubicComparison.length_subgroupOf C W L hCL hWL] at hc
  exact hc.trans (conjugationCubicLength_mono C hWcore)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
