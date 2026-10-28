module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Marking
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.Generation
public import Theory.GroupTheory.PResidual.FaithfulSylowCover
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.AlmostSpecialIntersection

/-!
# The original two-root generation and core calculation

The original quotient map lifts generation through its normalizing two-kernel.
Its Sylow preimage is an actual Sylow subgroup of K, embedded back into G.
The two-root product is normal: its commutators with either generator remain
in the corresponding root intersection. The perfect-group Sylow theorem then
forces this product to equal O₂(K). No equality O₂(H)=O₂(K) is used.

For the source S=⟨Uᴸ⟩, the 14.7.72 core identification makes O₂(H) normalize S.
The same original k gives U≤E and [E,K]≤U before any natural-module recognition.
The still-needed starred generation and Sylow-image calculations are explicit
inputs to these algebraic reductions. Their construction is part of 14.7.73.

Source: Aschbacher–Smith 14.7.73, printed pp.1076–1077, manuscript of
1 March 2004. The companion Applications module feeds the quotient leaves.
-/

public section
open Subgroup Representation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalizes_right_conjugate (P A K : Subgroup G) (k : K)
    (hKP : K ≤ normalizer P) (hPA : P ≤ normalizer A) :
    P ≤ normalizer (A.conjBy ((k : G)⁻¹)) := by
  have hP : P.map (MulAut.conj ((k : G)⁻¹)).toMonoidHom = P :=
    mem_normalizer_iff_map_conj_eq.mp (hKP (K.inv_mem k.property))
  have h := (map_mono (f := (MulAut.conj ((k : G)⁻¹)).toMonoidHom) hPA).trans
    (A.le_normalizer_map (MulAut.conj ((k : G)⁻¹)).toMonoidHom)
  rwa [hP] at h

omit [Finite G] in
/-- Lift generation from the original quotient through its normalizing two-kernel. -/
private theorem generation_of_image
    (K P A : Subgroup G) (k : K) (hAK : A ≤ K)
    (hKP : K ≤ normalizer P) (hPA : P ≤ normalizer A)
    {D : Type*} [Group D] (q : K →* D) (hqP : q.ker = P.subgroupOf K)
    (hq : IsPGroup 2 q.ker) (hperfect : IsPPerfect 2 K)
    (himage : ((A ⊔ A.conjBy ((k : G)⁻¹)).subgroupOf K).map q = q.range) :
    K = A ⊔ A.conjBy ((k : G)⁻¹) := by
  let B := A.conjBy ((k : G)⁻¹)
  let J := A ⊔ B
  have hBK : B ≤ K := by
    rintro x ⟨a, ha, rfl⟩
    exact K.mul_mem (K.mul_mem (K.inv_mem k.property) (hAK ha))
      (K.inv_mem (K.inv_mem k.property))
  have hJK : J ≤ K := sup_le hAK hBK
  have hPJ : P ≤ normalizer J :=
    (le_inf hPA (normalizes_right_conjugate P A K k hKP hPA)).trans
      (normalizer_inf_normalizer_le_normalizer_sup A B)
  let J' := J.subgroupOf K
  have hqJ : q.ker ≤ normalizer J' := by
    rw [hqP]
    exact (comap_mono hPJ).trans (le_normalizer_comap _)
  have hcover : J' ⊔ q.ker = ⊤ := by
    have h := congrArg (fun X => X.comap q) himage
    simpa only [comap_map_eq, MonoidHom.comap_range_self] using h
  let : J'.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← hcover]
    exact sup_le J'.le_normalizer hqJ))
  have hp : IsPGroup 2 (K ⧸ J') := isPGroup_quotient_of_sup_eq_top J' q.ker hq hcover
  have hz := hperfect.hom_eq_one_of_isPGroup hp (QuotientGroup.mk' J')
  apply le_antisymm ?_ hJK
  intro x hx
  exact (QuotientGroup.eq_one_iff (N := J') (⟨x, hx⟩ : K)).mp
    (DFunLike.congr_fun hz ⟨x, hx⟩)

omit [Finite G] in
/-- Normality of the two-root product and the central-cover commutator bound. -/
private theorem root_product_normal_and_commutator
    (K P A B : Subgroup G) (hKP : K ≤ normalizer P)
    (hPA : P ≤ normalizer A) (hPB : P ≤ normalizer B) (hgen : K = A ⊔ B) :
    K ≤ normalizer ((A ⊓ P) ⊔ (B ⊓ P) : Subgroup G) ∧
      ⁅P, K⁆ ≤ (A ⊓ P) ⊔ (B ⊓ P) := by
  let D := (A ⊓ P) ⊔ (B ⊓ P)
  have hDP : D ≤ P := sup_le inf_le_right inf_le_right
  have hA : ⁅P, A⁆ ≤ A ⊓ P := le_inf
    (le_normalizer_iff_commutator_le_right.mp hPA)
    (le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans (hgen.ge.trans hKP)))
  have hB : ⁅P, B⁆ ≤ B ⊓ P := le_inf
    (le_normalizer_iff_commutator_le_right.mp hPB)
    (le_normalizer_iff_commutator_le_left.mp (le_sup_right.trans (hgen.ge.trans hKP)))
  have hKD : K ≤ normalizer D := by
    rw [hgen]
    exact sup_le
      (le_normalizer_iff_commutator_le_left.mpr
        ((commutator_mono hDP le_rfl).trans (hA.trans le_sup_left)))
      (le_normalizer_iff_commutator_le_left.mpr
        ((commutator_mono hDP le_rfl).trans (hB.trans le_sup_right)))
  refine ⟨hKD, ?_⟩
  have hAC : A ≤ commutatorPreimage K P D :=
    le_commutatorPreimage (le_sup_left.trans hgen.ge)
      ((commutator_comm A P).le.trans (hA.trans le_sup_left))
  have hBC : B ≤ commutatorPreimage K P D :=
    le_commutatorPreimage (le_sup_right.trans hgen.ge)
      ((commutator_comm B P).le.trans (hB.trans le_sup_right))
  rw [commutator_comm]
  exact (commutator_mono (hgen.le.trans (sup_le hAC hBC)) le_rfl).trans
    (commutator_commutatorPreimage_le K P D hKD)

/-- A perfect-group Sylow argument identifies the root product with the kernel. -/
private theorem root_product_eq_of_sylow
    (K P A B : Subgroup G) [Group.IsPerfect K]
    (hPK : P ≤ K) (hKP : K ≤ normalizer P)
    (hPA : P ≤ normalizer A) (hPB : P ≤ normalizer B) (hgen : K = A ⊔ B)
    (hp : IsPGroup 2 P) (hderived : ⁅A, A⁆ ≤ A ⊓ P)
    (R : Sylow 2 K) (hR : (R : Subgroup K).map K.subtype = A ⊔ P) :
    (A ⊓ P) ⊔ (B ⊓ P) = P := by
  let D := (A ⊓ P) ⊔ (B ⊓ P)
  have hDP : D ≤ P := sup_le inf_le_right inf_le_right
  obtain ⟨hKD, hcomm⟩ := root_product_normal_and_commutator K P A B hKP hPA hPB hgen
  let : (P.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hKP
  let : (D.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hKD
  have h := commutator_generation_of_source_sylow K P A D hPK
    (le_sup_left.trans hgen.ge) hDP hp R hR (hderived.trans le_sup_left)
  exact le_antisymm hDP (h.ge.trans (sup_le hcomm le_rfl))

open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

include d in
theorem K_perfect : Group.IsPerfect (K F) := by
  let := d.component.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (K_le_H F)).toMonoidHom)
    (subgroupOfEquivOfLe (K_le_H F)).surjective

include d in
theorem U_le_QH : F.U ≤ F.H.pCoreIn 2 := by
  let := d.U_elementary
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 F.U)
    d.conjugationSection.section_le d.conjugationSection.normalized

omit [Finite G] in
/-- The source two-core of H normalizes the original S, using 14.7.72. -/
theorem QH_normalizes_S (hS : S L F = L.pCoreIn 2)
    (hTL : (T : Subgroup G) ≤ normalizer L) :
    F.H.pCoreIn 2 ≤ normalizer (S L F) := by
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := pCoreIn_le_sylow F.H (T.subtype (F.invariant 1)) hx
    exact ht
  rw [hS]
  exact hQT.trans (hTL.trans (normalizer_le_normalizer_characteristic_image _ _))

include d in
theorem U_le_E (k : K F) : F.U ≤ E L F k := by
  have hUS : F.U ≤ S L F := le_conjugateSpanBy _ _
  have hU : F.U.map (MulAut.conj ((k : G)⁻¹)).toMonoidHom = F.U :=
    mem_normalizer_iff_map_conj_eq.mp (d.conjugationSection.normalized
      (K_le_H F ((K F).inv_mem k.property)))
  exact le_inf hUS (hU.ge.trans (map_mono hUS))

include d in
/-- Centrality of E/U follows before recognizing the quotient P/E. -/
theorem E_commutator_le_U (k : K F)
    (hgen : K F = S L F ⊔ (S L F).conjBy ((k : G)⁻¹))
    (hderived : ⁅S L F, S L F⁆ ≤ F.U) : ⁅E L F k, K F⁆ ≤ F.U := by
  have hU : F.U.map (MulAut.conj ((k : G)⁻¹)).toMonoidHom = F.U :=
    mem_normalizer_iff_map_conj_eq.mp (d.conjugationSection.normalized
      (K_le_H F ((K F).inv_mem k.property)))
  have hder : ⁅(S L F).conjBy ((k : G)⁻¹), (S L F).conjBy ((k : G)⁻¹)⁆ ≤ F.U := by
    change ⁅(S L F).map (MulAut.conj ((k : G)⁻¹)).toMonoidHom,
      (S L F).map (MulAut.conj ((k : G)⁻¹)).toMonoidHom⁆ ≤ F.U
    rw [← map_commutator]
    exact (map_mono hderived).trans hU.le
  rw [hgen]
  exact intersection_commutator_sup_le hderived hder
    (hgen.ge.trans ((K_le_H F).trans d.conjugationSection.normalized))

include d in
theorem K_normalizes_E (k : K F)
    (hgen : K F = S L F ⊔ (S L F).conjBy ((k : G)⁻¹))
    (hderived : ⁅S L F, S L F⁆ ≤ F.U) : K F ≤ normalizer (E L F k) :=
  le_normalizer_iff_commutator_le_left.mpr
    ((E_commutator_le_U d k hgen hderived).trans (U_le_E d k))

/-- The genuine Sylow preimage, embedded back in the original G. -/
theorem source_sylow (hSK : S L F ≤ K F)
    (R : Sylow 2 SL2FourNatural.SL)
    (hR : ((S L F).subgroupOf (K F)).map (qK d) = (R : Subgroup _)) :
    ∃ R' : Sylow 2 (K F),
      (R' : Subgroup (K F)).map (K F).subtype = S L F ⊔ (K F).pCoreIn 2 := by
  obtain ⟨R', hR'⟩ := exists_sylow_eq_sup_ker_of_sylow_image
    (qK d) (qK_ker_isPGroup d) ((S L F).subgroupOf (K F)) R hR
  exact ⟨R', by rw [hR', Subgroup.map_sup, qK_ker,
    map_subgroupOf_eq_of_le hSK, map_subgroupOf_eq_of_le (pCoreIn_le 2 _)]⟩

/-- The original two roots generate K once their marked images do. -/
theorem source_generation (k : K F) (hSK : S L F ≤ K F)
    (hQS : F.H.pCoreIn 2 ≤ normalizer (S L F))
    (himage : ((S L F ⊔ (S L F).conjBy ((k : G)⁻¹)).subgroupOf (K F)).map
      (qK d) = ⊤) : K F = S L F ⊔ (S L F).conjBy ((k : G)⁻¹) := by
  refine generation_of_image (K F) (F.H.pCoreIn 2) (S L F) k hSK
    ((K_le_H F).trans (F.H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ _))) hQS (qK d)
      ?_ (qK_ker_isPGroup d) (K_twoPerfect F) ?_
  · ext x
    rw [qK_ker, K_core_eq_intersection]
    exact ⟨fun h => h.2, fun h => ⟨x.property, h⟩⟩
  · rw [himage, MonoidHom.range_eq_top.mpr (qK_surjective d)]

/-- The original product candidate is normal in K and equals O₂(K). -/
theorem source_product_eq_core (k : K F) (hSK : S L F ≤ K F)
    (hQS : F.H.pCoreIn 2 ≤ normalizer (S L F))
    (hgen : K F = S L F ⊔ (S L F).conjBy ((k : G)⁻¹))
    (hderived : ⁅S L F, S L F⁆ ≤ F.U) (hUQ : F.U ≤ F.H.pCoreIn 2)
    (R : Sylow 2 SL2FourNatural.SL)
    (hR : ((S L F).subgroupOf (K F)).map (qK d) = (R : Subgroup _)) :
    K F ≤ normalizer (P₀ L F k) ∧ P₀ L F k = (K F).pCoreIn 2 := by
  let := K_perfect d
  let P := (K F).pCoreIn 2
  let B := (S L F).conjBy ((k : G)⁻¹)
  have hKP : K F ≤ normalizer P := (K F).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ _)
  have hPQ : P ≤ F.H.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (K_le_H F) (H_normalizes_K F)
  have hPS : P ≤ normalizer (S L F) := hPQ.trans hQS
  have hPB : P ≤ normalizer B := normalizes_right_conjugate P (S L F) (K F) k hKP hPS
  have hBK : B ≤ K F := le_sup_right.trans hgen.ge
  have hinter (A : Subgroup G) (hAK : A ≤ K F) : A ⊓ F.H.pCoreIn 2 = A ⊓ P := by
    change _ = A ⊓ (K F).pCoreIn 2
    rw [K_core_eq_intersection]
    exact le_antisymm (fun _ h => ⟨h.1, hAK h.1, h.2⟩) (fun _ h => ⟨h.1, h.2.2⟩)
  have hprod : P₀ L F k = (S L F ⊓ P) ⊔ (B ⊓ P) := by
    unfold P₀
    rw [hinter (S L F) hSK, hinter B hBK]
  obtain ⟨R', hR'⟩ := source_sylow d hSK R hR
  have hder : ⁅S L F, S L F⁆ ≤ S L F ⊓ P := by
    rw [← hinter (S L F) hSK]
    exact le_inf (commutator_le_self _) (hderived.trans hUQ)
  rw [hprod]
  exact ⟨(root_product_normal_and_commutator (K F) P (S L F) B hKP hPS hPB hgen).1,
    root_product_eq_of_sylow (K F) P (S L F) B (pCoreIn_le 2 _) hKP hPS hPB
      hgen (isPGroup_pCoreIn 2 _) hder R' hR'⟩

omit [Finite G] in
/-- The join defining P₀ is the ordered subgroup product in the source. -/
theorem P₀_coe_eq_product (k : K F)
    (hQS : F.H.pCoreIn 2 ≤ normalizer (S L F)) :
    (P₀ L F k : Set G) = ((S L F ⊓ F.H.pCoreIn 2 : Subgroup G) : Set G) *
      (((S L F).conjBy ((k : G)⁻¹) ⊓ F.H.pCoreIn 2 : Subgroup G) : Set G) := by
  apply coe_mul_of_left_le_normalizer_right
  apply (inf_le_right : S L F ⊓ F.H.pCoreIn 2 ≤ F.H.pCoreIn 2).trans
  apply (le_inf ?_ (F.H.pCoreIn 2).le_normalizer).trans inf_normalizer_le_normalizer_inf
  exact normalizes_right_conjugate (F.H.pCoreIn 2) (S L F) (K F) k
    ((K_le_H F).trans (F.H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ _))) hQS

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition
