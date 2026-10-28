module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.FittingProduct
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Fitting-preimage containment from the original moved A₃ exclusion

Apply the solvable ordered-block theorem inside O₂,F(G)R. Its blocks are
two-perfect, so lie in O₂,F(G), and their subnormality lifts to G. Retaining
their actual commutator equality with J(R) lets the source A₃ exclusion
eliminate every outside factor. Hence the full Fitting preimage lies in the
original characteristic-normalizer control subgroup.

Source: Aschbacher–Smith C.2.6 and the application in 14.1.13, pp.145,979.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section02Source
variable {G : Type*} [Group G] [Finite G]

theorem fittingCore_le_of_no_moved_alternatingThree
    {κ : GroupClass} (hG : IsSQTK κ G) (R M : Subgroup G)
    (hr : IsPRadical 2 R) (hcontrol : R.characteristicNormalizerClosure ≤ M)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hno : ∀ X : Subgroup G, IsBlock X →
      X = ⁅X,elementaryAbelianMaxJ R⁆ → ¬ IsAlternatingBlock X 3) :
    twoFittingCore G ≤ M := by
  let F := twoFittingCore G
  let D := F ⊔ R
  have hFD : F ≤ D := le_sup_left
  have hRD : R ≤ D := le_sup_right
  let : Group.IsSolvable D := twoFittingCore_sup_solvable R hr.isPGroup
  have hcF : centralizer (pCore 2 F : Set F) ≤ pCore 2 F :=
    subnormal_core_selfCentralizing hc F (inferInstance : F.Normal).isSubnormal
  have hfD : generalizedFitting D = pCore 2 D :=
    (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      (twoFittingCore_sup_characteristicTwo R hr.isPGroup hcF)
  have hs := twoFittingCore_sup_sylow R hr
  change ∃ S : Sylow 2 D, (S : Subgroup D).map D.subtype = R at hs
  obtain ⟨S,hS⟩ := hs
  have hSM : (S : Subgroup D) = R.subgroupOf D := by
    apply map_injective D.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le hRD]
  have hcpu : (S : Subgroup D).characteristicNormalizerClosure ≤ M.subgroupOf D := by
    rw [hSM]
    exact characteristicNormalizerClosure_subgroupOf_le hRD hcontrol
  obtain ⟨n,_,B,hB,hout,hmove,hprod⟩ := ordered_alternatingThree_product
    (inferInstance : Group.IsSolvable D) (hG.subgroup D) hfD S (M.subgroupOf D) hcpu
  let FD := F.subgroupOf D
  let : FD.Normal := inferInstance
  have hgen : FD ⊔ R.subgroupOf D = ⊤ := by
    rw [←subgroupOf_sup hFD hRD,subgroupOf_self]
  have hquot : IsPGroup 2 (D ⧸ FD) :=
    isPGroup_quotient_of_sup_eq_top FD (R.subgroupOf D) hr.isPGroup.comap_subtype hgen
  have hBF (i) : B i ≤ FD := by
    have ht := (hB i).1.short.twoPerfect.hom_eq_one_of_isPGroup hquot
      ((QuotientGroup.mk' FD).comp (B i).subtype)
    intro b hb
    exact (QuotientGroup.eq_one_iff b).mp (DFunLike.congr_fun ht ⟨b,hb⟩)
  have hfalse (i : Fin n) : False := by
    let X := (B i).map D.subtype
    let e : B i ≃* X := equivMapOfInjective (B i) D.subtype D.subtype_injective
    have hXF : X ≤ F := by
      rintro x ⟨b,hb,rfl⟩
      exact hBF i hb
    have ha : IsAlternatingBlock X 3 :=
      RankOne.Solvable.isAlternatingBlock_of_equiv e (hB i).2
    have hsub : (X.subgroupOf F).IsSubnormal := by
      have he : (B i).comap (inclusion hFD) = X.subgroupOf F := by
        ext x
        exact (mem_map_iff_mem D.subtype_injective).symm
      rw [←he]
      exact (hB i).1.subnormal.comap (inclusion hFD)
    have hb : IsBlock X := ⟨inferInstance,ha.2.1,
      Subgroup.IsSubnormal.trans hXF hsub (inferInstance : F.Normal).isSubnormal⟩
    have hm : X = ⁅X,elementaryAbelianMaxJ R⁆ := by
      have hh := congrArg (map D.subtype) (hmove i)
      rw [map_commutator,←elementaryAbelianMaxJ_map_injective
        D.subtype D.subtype_injective,hS] at hh
      exact hh
    exact hno X hb hm ha
  have hn : n = 0 := by
    by_contra hn
    exact hfalse ⟨0,Nat.pos_of_ne_zero hn⟩
  subst n
  intro x hx
  obtain ⟨m,b,he⟩ := hprod ⟨x,hFD hx⟩
  have hh : x = ((m : D) : G) := by
    simpa only [List.ofFn_zero,List.prod_nil,mul_one,Subgroup.subtype_apply] using
      congrArg D.subtype he
  rw [hh]
  exact m.property
end CFSG.Quasithin.ChapterC.Section02Source
