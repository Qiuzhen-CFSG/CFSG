module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.ConjugateImages
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.ConjugateEscape
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.InitialModule
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.BaumannCore

/-!
# The page-888 conjugate geometry on the original unitary flag

The exact exceptional Frattini containment supplies the block, whose chosen
module is the intrinsic moving core. Original maximal-local uniqueness and
the established Baumann-core containment give a normalizer conjugate outside
the actual product core. The natural action identifies its image with the
root eight and identifies both its intersection and commutator with V₃.
The literal core centralizer has index eight, and its conjugate is exactly
the centralizer of the conjugate module.

The Frattini containment remains explicit. It and the remaining core-product,
Frattini and elementary-family normalizer argument are owned by
qt-d-13316-noncentrality. Final qt-d-13316-source discharges the independent
plane-centralizer and earlier universal statements. This does not yet prove
plane noncentrality. Source: Aschbacher--Smith 13.3.10(2), p.888.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Noncentrality
universe u
variable {G : Type u} [Group G] [Finite G]
theorem unitary_original_baumann_conjugate_of_frattini_small
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
    (hHfull : D.H = normalizer (D.V₁ : Set G))
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G)))
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
    (fixed : OriginalFixedModule1332At D.T D.L)
    (five : OriginalAlternatingFiveModules1332At D.T D.L)
    (hc : ⁅D.QH,B⁆ = ⊥)
    (hsmall : let R := (D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2
      let Y := D.L ⊔ ChapterB.baumann R
      ⁅pCore 2 Y,D.L.subgroupOf Y⁆ ≤
        (frattini (pCore 2 Y)).map (pCore 2 Y).subtype ⊔ omegaCenterIn (pCore 2 Y)) :
    let R := (D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2
    ∃ (rho : Automizer D.V →* Atlas.G2.Model F) (E : Additive D.V ≃ₗ[F] W),
      (∀ a v, E (automizerRepresentation D.V a v) =
        Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v)) ∧
      pointCoordinateSubspace E D.V₁ = pointLine ∧
      pointCoordinateSubspace E D.Vplus = seed ∧
      ∃ x ∈ normalizer (ChapterB.baumann R : Set G),
        let A := D.V.map (MulAut.conj x⁻¹).toMonoidHom
        A ≤ ChapterB.baumann R ∧
        ¬ A ≤ (D.L ⊔ ChapterB.baumann R).pCoreIn 2 ∧
        (inducedAutomizer D.V A).map rho = Atlas.G2.BinaryCore.elementary ∧
        D.V ⊓ centralizer (A : Set G) = D.Vplus ∧
        ⁅D.V,A⁆ = D.Vplus ∧ D.V ⊓ A = D.Vplus ∧
        ((D.L ⊔ ChapterB.baumann R).pCoreIn 2).relIndex (ChapterB.baumann R) = 8 ∧
        ((D.L ⊔ ChapterB.baumann R).pCoreIn 2).map (MulAut.conj x⁻¹).toMonoidHom =
          ChapterB.baumann R ⊓ centralizer (A : Set G) := by
  intro R
  obtain ⟨rho,E,he,hz,hu,_,hVB,_,hBI,_,_⟩ :=
    unitary_original_offender_images_of_plane_centrality D h chosen hmax eL structural
      e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes h1332 fixed five hc
  obtain ⟨hQB,hQC⟩ := unitary_original_baumann_core_of_plane_centrality D h chosen hmax eL structural
      e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes h1332 fixed five hc
  have hb := unitary_original_g2_block_of_frattini_small D h chosen hmax eL structural
      e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes h1332 fixed five hc hsmall
  have hout := unitary_original_baumann_escape D h chosen hmax eL structural
      e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes h1332 fixed five hc
  have hTN := (unitary_original_module_normalizers h hmax eL chosen structural).1
  let P := D.L₁ ⊔ (D.T : Subgroup G)
  have hRT : R ≤ (D.T : Subgroup G) := by
    have hh := pCoreIn_le_sylow P (D.T.subtype le_sup_right)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (D.T : Subgroup G) ≤ P from le_sup_right)] using hh
  have hTR : (D.T : Subgroup G) ≤ normalizer (R : Set G) :=
    le_sup_right.trans (P.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image P (pCore 2 P)))
  obtain ⟨x,hx,hext⟩ := unitary_baumann_exists_escaping_conjugate_of_short h chosen hmax eL
    R hRT hTR hQB hb.short hout
  let A := D.V.map (MulAut.conj x⁻¹).toMonoidHom
  have hAB : A ≤ ChapterB.baumann R := (map_mono hVB).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hx))
  have hne : ¬ A ≤ centralizer (D.V : Set G) := by
    intro hh
    exact hext (hQC ▸ le_inf hAB hh)
  have hBN : ChapterB.baumann R ≤ normalizer (D.V : Set G) :=
    inf_le_left.trans (hRT.trans hTN)
  have hp : (inducedAutomizer D.V (ChapterB.baumann R)).map rho ≤
      Atlas.G2.LieParabolicSetup.radical₂ := by
    rw [hBI]
    rintro _ ⟨t,ht,rfl⟩
    exact ⟨Atlas.G2.BinaryCore.parameters t,by simpa [Atlas.G2.BinaryCore.parameters] using ht.2,rfl⟩
  have hi := unitary_baumann_moving_conjugate_intersection D.V (ChapterB.baumann R) D.Vplus
    rho E he hVB hBN hp hUV hu x hx hne
  have hindex : ((D.L ⊔ ChapterB.baumann R).pCoreIn 2).relIndex (ChapterB.baumann R) = 8 := by
    rw [hQC]
    exact unitary_root_eight_centralizer_index D.V (ChapterB.baumann R) rho E he hBN hBI
  have hconj : ((D.L ⊔ ChapterB.baumann R).pCoreIn 2).map
      (MulAut.conj x⁻¹).toMonoidHom = ChapterB.baumann R ⊓ centralizer (A : Set G) := by
    have hBa : (ChapterB.baumann R).map (MulAut.conj x⁻¹).toMonoidHom = ChapterB.baumann R :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hx)
    have hQ : (D.L ⊔ ChapterB.baumann R).pCoreIn 2 =
        ChapterB.baumann R ⊓ centralizer (D.V : Set G) := hQC
    rw [hQ,map_inf _ _ _ (MulAut.conj x⁻¹).injective,hBa,
      Theory.GroupTheory.map_centralizer_equiv]
    rfl
  exact ⟨rho,E,he,hz,hu,x,hx,hAB,hext,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2,hindex,hconj⟩
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
