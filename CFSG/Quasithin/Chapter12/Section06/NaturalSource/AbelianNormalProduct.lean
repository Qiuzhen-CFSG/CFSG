module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalFourReduction
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianProduct
public import Theory.SpecificGroups.SymmetricFiveThreeRecognition

/-!
# The symmetric product in the original normal PSL₂(4) branch

The Borel over T ∩ K is normalized by the actual L₁T. Its two-core is
T ∩ K, so that intersection lies in the original edge core R₁. In H/O₂(H),
the proved point-residual splitting supplies the normal centralizing cubic C.
The quotient by K-star times C is a two-group. If it were cyclic, restriction
to the original T would have kernel in R₁: its cubic coordinate vanishes by
coprimality, and the entire O₂(H) kernel lifts into R₁. This contradicts the
original noncyclic point-Sylow quotient.

The intrinsic recognition theorem now constructs H/O₂(H) ≃ S₅ × S₃.
Apply it to the selected reduced actor J = K₀L₁T, whose actual membership
in Hz is already proved, and invoke the terminal product contradiction.
No extra recognition hypothesis or catalogue callback is introduced.

The earlier fixed-space, point-invariance, TI, intersection and nonsingular
centralizer inputs remain explicit. Their discharge and the universal
Section09.NaturalReduction statement remain source-assembly obligations.
The independent index-five and marked-core clauses are not asserted here.

Source: Aschbacher–Smith 12.6.31(3), 12.6.33–34, printed pp.836–838,
refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)

include hz hTV hTz hbound hTI hns hH hKH in
/-- The literal component-Sylow intersection lies in the original edge core. -/
theorem SourceHypothesis.original_abelian_normal_linearFour_sylow_le_edge_core
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    (T : Subgroup G) ⊓ K ≤ (D.fullSetup hZ T z).R₁ := by
  let E := D.fullSetup hZ T z
  obtain ⟨_,_,_,_,hnB,_⟩ := S.original_abelian_normal_linearTwo_borel
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hout (n := 2) (by decide) hm
  have hcore := S.original_abelian_normal_linearTwo_borel_core
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hout (n := 2) (by decide) hm
  apply le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
    (inf_le_left.trans le_sup_right)
  rw [←hcore]
  exact hnB.trans (normalizer_le_normalizer_characteristic_image
    (K ⊓ M L) (pCore 2 (K ⊓ M L : Subgroup G)))

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The original reduced normal PSL₂(4) actor has the full symmetric-product
quotient. Both independent factor actions are forced by the point quotient. -/
theorem SourceHypothesis.original_abelian_normal_linearFour_product
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    Nonempty ((H ⧸ pCore 2 H) ≃* Terminal.Product) := by
  let E := D.fullSetup hZ T z
  let A := actorImage H E.L₁
  let B := actorImage H K
  let C := A ⊓ centralizer (B : Set (H ⧸ pCore 2 H))
  let π := QuotientGroup.mk' (pCore 2 H)
  let : B.Normal := hn.map π (QuotientGroup.mk'_surjective _)
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  obtain ⟨hCn,hC3,hCc⟩ := S.original_abelian_normal_linearTwo_centralizer_card
    D hZ z hz hTV hTz hH hKH hK hgen hn (n := 2) (by decide) hm
  let : C.Normal := hCn
  let : IsElementaryAbelian 3 C := hC3
  have hsplit := (S.original_abelian_normal_linearTwo_split
    D hZ z hz hTV hTz hH hKH hK hgen hn (n := 2) (by decide) hm).1
  have hgenstar : (B ⊔ C) ⊔ actorImage H T = ⊤ := by
    have hg := hgen
    rw [conjugateSpan_eq_of_normal H K T hKH hTH hn] at hg
    have hfull : B ⊔ A ⊔ actorImage H T = ⊤ := by
      unfold B A actorImage
      rw [←Subgroup.map_sup,←Subgroup.map_sup,←subgroupOf_sup hKH hLH,
        ←subgroupOf_sup (sup_le hKH hLH) hTH,hg,subgroupOf_self,
        map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    have hBA : B ⊔ A = B ⊔ C := by
      change A = (A ⊓ B) ⊔ C at hsplit
      rw [hsplit,←sup_assoc,sup_eq_left.mpr (show A ⊓ B ≤ B from inf_le_right)]
    rwa [hBA] at hfull
  have hquot : IsPGroup 2 ((H ⧸ pCore 2 H) ⧸ (B ⊔ C)) :=
    isPGroup_quotient_of_sup_eq_top (B ⊔ C) (actorImage H T)
      (T.isPGroup'.comap_subtype.map π) hgenstar
  have hcore := S.original_abelian_normal_linearFour_sylow_le_edge_core
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hout hm
  have hncyc : ¬ IsCyclic ((H ⧸ pCore 2 H) ⧸ (B ⊔ C)) := by
    intro hcyc
    let := hcyc
    let q := QuotientGroup.mk' (B ⊔ C)
    let f := q.comp (π.comp (inclusion hTH))
    apply S.original_point_sylow_cyclic_kernel_impossible D hZ z hz hTz f
    intro t ht
    have hbc : π (inclusion hTH t) ∈ B ⊔ C := (QuotientGroup.eq_one_iff _).mp ht
    let b := QuotientGroup.mk' B
    have hmap : (B ⊔ C).map b = C.map b := by
      rw [Subgroup.map_sup,QuotientGroup.map_mk'_self,bot_sup_eq]
    have hd : Disjoint ((actorImage H T).map b) (C.map b) :=
      (T.isPGroup'.comap_subtype.map π |>.map b).disjoint_of_coprime
        ((IsElementaryAbelian.isPGroup 3 C).map b) (by decide)
    have htB : π (inclusion hTH t) ∈ B := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact Subgroup.disjoint_def.mp hd
        (mem_map_of_mem b (mem_map_of_mem π t.property))
        (hmap ▸ mem_map_of_mem b hbc)
    obtain ⟨k,hk,he⟩ := htB
    have hdiff : inclusion hTH t * k⁻¹ ∈ pCore 2 H := by
      apply (QuotientGroup.eq_one_iff _).mp
      change π (inclusion hTH t * k⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hdiffR : (t : G) * (k : G)⁻¹ ∈ E.R₁ :=
      S.original_core_le_point_core D hZ z hH (mem_map_of_mem H.subtype hdiff)
    have hRT : E.R₁ ≤ (T : Subgroup G) := (S.original_point_core_eq D hZ z hz hTz).2.2
    have hkT : (k : G) ∈ (T : Subgroup G) := by
      have hh := (T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem (hRT hdiffR)) t.property
      simpa only [mul_inv_rev,inv_inv,inv_mul_cancel_right] using hh
    have hh := E.R₁.mul_mem hdiffR (hcore ⟨hkT,hk⟩)
    change (t : G) ∈ E.R₁
    simpa only [inv_mul_cancel_right] using hh
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let := hF
  let := hfin
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hcard
  let eB := (componentStarEquiv H K hKH hK).symm.trans (e.trans a)
  exact symmetric_five_three_of_normal_five_cubic B C eB hCc inf_le_right hquot
    (pCore_quotient_pCore_eq_bot 2) hncyc

include hz hTV hTz hbound hTI hns hH in
/-- The original source family Hz is impossible under the retained earlier
geometry: recognize the same selected J and apply its terminal contradiction. -/
theorem SourceHypothesis.original_abelian_point_overgroup_impossible : False := by
  obtain ⟨K,hKH,hK,hout,_,_,_,_,hJ,hKJ,hn,_,hm,_⟩ :=
    S.original_abelian_reduced_normal_linearFour D hZ z hz hTz hTV hbound hTI hns hH
  let J := conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
  have hKle : K ≤ J := (le_conjugateSpanBy K (T : Subgroup G)).trans
    (le_sup_left.trans le_sup_left)
  have hproduct := S.original_abelian_normal_linearFour_product
    D hZ z hz hTV hTz hbound hTI hns hJ hKle hKJ rfl hn hout hm
  exact S.original_symmetric_product_impossible D hZ z hz hTz hJ hTV hbound hTI hns hproduct
end CFSG.Quasithin.Chapter12.Section06
