module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersThompsonSourceFive
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.QuotientKernel
public import Theory.GroupTheory.NormalQuotientActionSylowSupplement
public import Theory.Alternating.FivePairOuterTwo

/-!
# The literal KTY cover of the weight-two centralizer

Once K=C_L(e)∞ is normal in H=C_G(e), the proved K/O₂(K)≅A₅ marking
makes its outer automorphism group a two-group. A Sylow supplement to the
quotient-action kernel gives H=KTY. Transport from the subgroup K inside H
retains the original embedded two-core, so Y is exactly the original
section centralizer C_H(K/O₂(K)).

Source: Aschbacher--Smith, Lemma 12.3.8, printed p.810. Only the component
normality remains explicit here; its producer and final point-centralizer
assembly are qt-d-1236-1238-point-centralizers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
variable {E : S.NaturalCoordinates}
namespace SylowNormalizer.Points
variable (P : Points E)

/-- Relative normality and the actual A₅ quotient give the original cover. -/
theorem two_centralizer_cover
    (hn : centralizer ({(P.two : G)} : Set G) ≤ normalizer (P.five : Set G)) :
    centralizer ({(P.two : G)} : Set G) ≤ P.five ⊔ (T : Subgroup G) ⊔
      twoSectionCentralizer P.five (centralizer ({(P.two : G)} : Set G)) := by
  let C := centralizer ({(P.two : G)} : Set G)
  let K := P.five
  have hKC : K ≤ C := (pointResidual_le L (P.two : G)).trans inf_le_right
  have hTC : (T : Subgroup G) ≤ C := fun t ht =>
    mem_centralizer_singleton_iff.mpr (P.two_central t ht)
  let B := K.subgroupOf C
  let : B.Normal := normal_subgroupOf_of_le_normalizer hn
  let e : B ≃* K := subgroupOfEquivOfLe hKC
  let eQ := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans P.fiveCoreEquiv
  have ho : IsPGroup 2 (MulAut.Outer (B ⧸ pCore 2 B)) :=
    Theory.AlternatingFive.outer_isPGroup_two.of_equiv (MulAut.outerCongr eQ).symm
  let a := normalQuotientAction B (pCore 2 B)
  have hgen := normalQuotientAction_sup_sylow_ker (T.subtype hTC) B (pCore 2 B) ho
  have hm := congrArg (map C.subtype) hgen
  rw [Subgroup.map_sup,Subgroup.map_sup,Sylow.coe_subtype,
    map_subgroupOf_eq_of_le hKC,map_subgroupOf_eq_of_le hTC,
    ← MonoidHom.range_eq_map,range_subtype] at hm
  change C ≤ _
  rw [← hm]
  apply sup_le le_sup_left
  apply le_trans ?_ le_sup_right
  change a.ker.map C.subtype ≤ twoSectionCentralizer K C
  have hcore : (B.pCoreIn 2).map C.subtype = K.pCoreIn 2 := by
    change ((pCore 2 B).map B.subtype).map C.subtype = (pCore 2 K).map K.subtype
    rw [← pCore_map_iso 2 e,map_map,map_map]
    rfl
  rintro _ ⟨x,hx,rfl⟩
  have hx' := (normalQuotientAction_ker B).le hx
  refine ⟨x.property,hn x.property,?_⟩
  intro k hk
  have hc := hx'.2.2 (⟨k,hKC hk⟩ : C) hk
  have hg := mem_map_of_mem C.subtype hc
  rw [hcore] at hg
  exact hg

end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
