module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.ConjugateProduct
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.CoreFrattini
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.SourcePushingUp
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.SourceCore

/-!
# The elementary direct product in the original unitary argument

The genuine G₂ block supplies an escaping conjugate of V. Two opposite
root eights give Q = V × C_B(L), and the same conjugate centralizes C_B(L).
Conjugating the two core centralizers fixes Φ(C_B(L)); maximal-local
uniqueness forces this Frattini subgroup to vanish. Consequently Q is
elementary abelian. The escaping conjugate and the exact product B=VˣQ
are retained for the final normalizer argument.

The proofs specialize and assemble the checked OriginalUnitaryNoncentrality
lemmas using normalizer escape directly. Source: Aschbacher--Smith
13.3.10(2), pp.887--888; C.1.37 and C.6.3.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]
theorem unitary_original_baumann_elementary_of_escape
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (e : inducedAutomizer D.V D.L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive D.V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer D.V D.L) v,
      E0 (automizerRepresentation D.V l v) =
        Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hout : ¬ normalizer (ChapterB.baumann ((D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2) : Set G) ≤
      normalizer (D.L : Set G)) :
    let R := (D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2
    let Q := (D.L ⊔ ChapterB.baumann R).pCoreIn 2
    let C := ChapterB.baumann R ⊓ centralizer (D.L : Set G)
    Q = D.V ⊔ C ∧ Disjoint D.V C ∧ frattini C = ⊥ ∧ IsElementaryAbelian 2 Q ∧
      ∃ x ∈ normalizer (ChapterB.baumann R : Set G),
        let A := D.V.map (MulAut.conj x⁻¹).toMonoidHom
        ¬ A ≤ Q ∧ C ≤ centralizer (A : Set G) ∧ ChapterB.baumann R = A ⊔ Q := by
  intro R Q C
  let Y := D.L ⊔ ChapterB.baumann R
  obtain ⟨_,_,_,_,_,_,_,rho,E,eq,hn,he,hz,hu,heq,hpre⟩ :=
    unitary_original_baumann_pushingUp_of_escape D h chosen hmax eL structural
      e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hout
  obtain ⟨hQB,hQC⟩ := unitary_original_baumann_core_of_escape D h chosen hmax eL structural
      e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hout
  have hb := unitary_original_g2_block_of_escape D h chosen hmax eL structural
      e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hout

  have hTN := (unitary_original_module_normalizers h hmax eL chosen structural).1
  let P := D.L₁ ⊔ (D.T : Subgroup G)
  have hRT : R ≤ (D.T : Subgroup G) := by
    have hh := pCoreIn_le_sylow P (D.T.subtype le_sup_right)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (D.T : Subgroup G) ≤ P from le_sup_right)] using hh
  have hTR : (D.T : Subgroup G) ≤ normalizer (R : Set G) :=
    le_sup_right.trans (P.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image P (pCore 2 P)))
  have hBN : ChapterB.baumann R ≤ normalizer (D.V : Set G) := le_sup_right.trans hn
  have hVB : D.V ≤ ChapterB.baumann R := by
    obtain ⟨_,_,_,_,_,_,hv,_⟩ := unitary_original_offender_images_of_escape
      D h chosen hmax eL structural e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB
      hout
    exact hv
  let q : Y →* Atlas.G2.Model F := eq.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Y))
  have hq : Function.Surjective q := eq.surjective.comp (QuotientGroup.mk'_surjective _)
  have hmap (A : Subgroup G) (hAY : A ≤ Y) :
      (A.subgroupOf Y).map q = (inducedAutomizer D.V A).map rho := by
    ext a
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨_,⟨⟨y,hn y.property⟩,hy,rfl⟩,(heq y).symm⟩
    · rintro ⟨_,⟨n,hnA,rfl⟩,rfl⟩
      exact ⟨⟨n.val,hAY hnA⟩,hnA,heq ⟨n.val,hAY hnA⟩⟩
  have hBI : (inducedAutomizer D.V (ChapterB.baumann R)).map rho =
      Atlas.G2.BinaryCore.elementary := by
    rw [←hmap (ChapterB.baumann R) le_sup_right,hpre,map_comap_eq,MonoidHom.range_eq_top.mpr hq,top_inf_eq]
  obtain ⟨x,hx,hext⟩ := unitary_baumann_exists_escaping_conjugate_of_short h chosen hmax eL
    R hRT hTR hQB hb.short hout
  let A := D.V.map (MulAut.conj x⁻¹).toMonoidHom
  have hBa : (ChapterB.baumann R).map (MulAut.conj x⁻¹).toMonoidHom = ChapterB.baumann R :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hx)
  have hAB : A ≤ ChapterB.baumann R := (map_mono hVB).trans_eq hBa
  have hne : ¬ A ≤ centralizer (D.V : Set G) := by
    intro hh
    exact hext ((le_inf hAB hh).trans hQC.ge)
  have hp : (inducedAutomizer D.V (ChapterB.baumann R)).map rho ≤
      Atlas.G2.LieParabolicSetup.radical₂ := by
    rw [hBI]
    rintro _ ⟨t,ht,rfl⟩
    exact ⟨Atlas.G2.BinaryCore.parameters t,by simpa [Atlas.G2.BinaryCore.parameters] using ht.2,rfl⟩
  have hi := unitary_baumann_moving_conjugate_image D.V (ChapterB.baumann R) rho E he
    hVB hBN hp x hx hne
  have hindex : Q.relIndex (ChapterB.baumann R) = 8 := by
    change ((D.L ⊔ ChapterB.baumann R).pCoreIn 2).relIndex (ChapterB.baumann R) = 8
    rw [hQC]
    exact unitary_root_eight_centralizer_index D.V (ChapterB.baumann R) rho E he hBN hBI
  have hs := unitary_baumann_conjugate_core_product chosen hb.short (ChapterB.baumann R) hVB
    (inf_le_left.trans (hRT.trans chosen.sylow_normalizes_component)) rho E hn eq heq hQC
    (unitary_component_fixed_points_eq_bot D.L e E0 he0) x hx hi hindex
  have hspan : ChapterB.baumann R = A ⊔ Q := by
    have hh : (A.subgroupOf Y).map q = Atlas.G2.BinaryCore.elementary :=
      (hmap A (hAB.trans le_sup_right)).trans hi
    have hk : q.ker = pCore 2 Y := by
      ext y
      change eq (QuotientGroup.mk' (pCore 2 Y) y) = 1 ↔ _
      rw [←eq.map_one,eq.injective.eq_iff]
      exact QuotientGroup.eq_one_iff y
    rw [←hh,comap_map_eq,hk] at hpre
    have hm := congrArg (map Y.subtype) hpre
    rwa [map_subgroupOf_eq_of_le (show ChapterB.baumann R ≤ Y from le_sup_right),
      Subgroup.map_sup,map_subgroupOf_eq_of_le (hAB.trans le_sup_right)] at hm
  have hf := unitary_baumann_core_elementary_of_conjugate_product h chosen hmax eL R hRT hTR
    hb.short hQC hs.1 x hx hext hs.2.2 hspan
  exact ⟨hs.1,hs.2.1,hf.1,hf.2,x,hx,hext,hs.2.2,hspan⟩
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
