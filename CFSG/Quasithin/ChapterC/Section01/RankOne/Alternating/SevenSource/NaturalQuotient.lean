module
public import Theory.SpecificGroups.AlternatingSeven.CubicLift.SymmetricExtension
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The selected cubic in the original two-core quotient

The image of the original normal component in G/O₂(G) is identified with
L/O₂(L). Its central quotient is the actual alternating image of the given
permutation action. Its center is odd because the ambient two-core quotient
has trivial two-core. The proved ordinary/triple-cover cubic lifting theorem
therefore supplies a genuine invariant cubic in this image, retaining all
original quotient maps and the selected natural-module cubic.

Source: Aschbacher–Smith C.1.24(a), printed pp.130–131.
-/

public section

open Subgroup Theory.GroupTheory Equiv
namespace CFSG.Quasithin.ChapterC.RankOne.SevenSource.Natural
open Theory.SpecificGroups.SymmetricSeven.ThreePairsCubic
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry
open Theory.SpecificGroups.AlternatingSeven.CubicLift

variable {G : Type*} [Group G] [Finite G]
theorem exists_quotient_cubic (L R : Subgroup G) [L.Normal]
    [IsQuasisimple (L ⧸ pCore 2 L)] (q : G →* Sym)
    (hQ : pCore 2 G ≤ q.ker) (hLq : L.map q = alternatingGroup (Fin 7))
    (hpR : IsPGroup 2 R) (hR : R.map q=pairElementary) :
    ∃ M : Subgroup (G ⧸ pCore 2 G),
      M ≤ L.map (QuotientGroup.mk' (pCore 2 G)) ∧ Nat.card M=3 ∧
      R.map (QuotientGroup.mk' (pCore 2 G)) ≤ normalizer (M : Set (G ⧸ pCore 2 G)) ∧
      M.map (QuotientGroup.lift (pCore 2 G) q hQ)=zpowers cubic := by
  let π := QuotientGroup.mk' (pCore 2 G)
  let qb := QuotientGroup.lift (pCore 2 G) q hQ
  let B := L.map π
  let : B.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  let eB : (L ⧸ pCore 2 L) ≃* B := (inferInstance : L.Normal).isSubnormal.quotientCoreImageEquiv 2
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv eB
  have hBq : B.map qb=alternatingGroup (Fin 7) := by
    rw [map_map]
    exact hLq
  let f : B →* alternatingGroup (Fin 7) := (qb.comp B.subtype).codRestrict _
    (fun x => hBq ▸ mem_map_of_mem qb x.property)
  have hf : Function.Surjective f := by
    intro y
    have hy : (y:Sym)∈B.map qb := by rw [hBq]; exact y.property
    obtain ⟨x,hx,he⟩ := hy
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let := alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 7))
  let cover : Covering B (alternatingGroup (Fin 7)) := ⟨f,hf⟩
  have hk : f.ker=center B := cover.ker_eq_center_of_isSimple
  let e : B ⧸ center B ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he : ∀ x : B, qb x=(GLS3.Chapter5.alternatingQuotientHom e x : Sym) := by
    intro x
    rfl
  have ho : Odd (Nat.card (center B)) :=
    GLS3.Chapter5.OddCentralCovers.component_center_odd (pCore_quotient_pCore_eq_bot (G := G) 2)
      B ⟨(inferInstance : B.Normal).isSubnormal,inferInstance⟩
  have hRq : (R.map π).map qb=pairElementary := by
    rw [map_map]
    exact hR
  exact exists_pair_cubic B e ho qb he (R.map π) (hpR.map π) hRq.le

/-- The selected cubic stays noncentral in the component's literal two-core quotient. -/
theorem cubic_not_central_in_component (L Y : Subgroup G) (hL : L.IsSubnormal)
    (hYL : Y ≤ L) (q : G →* Sym) (hQ : pCore 2 G ≤ q.ker)
    (hLq : L.map q=alternatingGroup (Fin 7)) (hY : Y.map q=zpowers cubic) :
    ¬(Y.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L)) ≤ center (L ⧸ pCore 2 L) := by
  have hk : pCore 2 L ≤ (q.comp L.subtype).ker := by
    rw [←hL.pCore_subgroupOf 2]
    intro x hx
    exact hQ hx
  let f := QuotientGroup.lift (pCore 2 L) (q.comp L.subtype) hk
  have hcY : cubic∈Y.map q := by rw [hY];exact mem_zpowers cubic
  obtain ⟨y,hy,hyc⟩ := hcY
  let z : L := ⟨y,hYL hy⟩
  have hca : cubic∈alternatingGroup (Fin 7) := by
    rw [←hLq];exact ⟨y,hYL hy,hyc⟩
  intro hcent
  have hz := hcent (mem_map_of_mem (QuotientGroup.mk' (pCore 2 L)) (show z∈Y.subgroupOf L from hy))
  have hcc : (⟨cubic,hca⟩ : alternatingGroup (Fin 7))∈center (alternatingGroup (Fin 7)) := by
    rw [mem_center_iff]
    intro a
    have ha : (a:Sym)∈L.map q := by rw [hLq];exact a.property
    obtain ⟨l,hl,hla⟩ := ha
    have he := congrArg f (mem_center_iff.mp hz (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩))
    simp only [map_mul] at he
    change q l*q y=q y*q l at he
    apply Subtype.ext
    change (a:Sym)*cubic=cubic*(a:Sym)
    rw [←hla,←hyc]
    exact he
  rw [alternatingGroup.center_eq_bot (by simp)] at hcc
  have he : cubic=1 := congrArg Subtype.val (mem_bot.mp hcc)
  have hc := cubic_order
  rw [he,orderOf_one] at hc
  omega
end CFSG.Quasithin.ChapterC.RankOne.SevenSource.Natural
