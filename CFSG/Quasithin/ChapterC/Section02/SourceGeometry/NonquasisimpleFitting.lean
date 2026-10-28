module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ThreeRadical
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.Setup
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.MovedFittingProduct
public import Theory.GroupTheory.PRadical.NormalizerRestriction
public import Theory.GroupTheory.Fitting.TwoCoreMonotonicity
public import Theory.GroupTheory.SolvableRadical.NormalTwoExtensionThreeFree

/-!
# C.2.6 containment for a nonquasisimple normal component

For a normal C-component L, A.3.6 makes its solvable radical prime to three
when L/O₂(L) is not quasisimple. Put D=LR. Radicality restricts because
N(R) normalizes D, and D remains characteristic two. Its radical is still
prime to three, since D/L is a two-group. Every outside A₃ factor in the
C.2.6 decomposition would divide that radical's order, so there are none.
The Fitting preimage of L lies in that of D and consequently lies in M.

The final theorem applies to the literal C.2.3 setup and component of the
original 15.2.4 nonquasisimple branch, printed p.1107. It uses the existing
A.3.6 theorem and adds no source premise.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section02Source
variable {G : Type*} [Group G] [Finite G]

/-- C.2.6 excludes every outside A₃ factor when the normal component radical is three-free. -/
theorem fittingCore_le_of_normal_threeFree_radical {κ : GroupClass}
    (hG : IsSQTK κ G) (K R M : Subgroup G) [K.Normal]
    (hK : generalizedFitting K = pCore 2 K)
    (hK3 : ¬ 3 ∣ Nat.card (solvableRadical K))
    (hr : IsPRadical 2 R) (hcontrol : R.characteristicNormalizerClosure ≤ M) :
    (twoFittingCore K).map K.subtype ≤ M := by
  let D := K ⊔ R
  let K₀ := K.subgroupOf D
  let R₀ := R.subgroupOf D
  let M₀ := M.subgroupOf D
  have hKD : K ≤ D := le_sup_left
  have hRD : R ≤ D := le_sup_right
  let : K₀.Normal := inferInstance
  let e : K₀ ≃* K := subgroupOfEquivOfLe hKD
  have hrD : IsPRadical 2 R₀ := hr.subgroupOf_of_normalizer_normalizes D hRD
    ((le_inf le_normalizer_of_normal le_rfl).trans
      (normalizer_inf_normalizer_le_normalizer_sup K R))
  have hcontrolD : R₀.characteristicNormalizerClosure ≤ M₀ :=
    characteristicNormalizerClosure_subgroupOf_le hRD hcontrol
  have hcD : centralizer (pCore 2 D : Set D) ≤ pCore 2 D :=
    centralizer_pCore_sup_le 2 K R
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hK) hr.isPGroup le_normalizer_of_normal
  have hgen : K₀ ⊔ R₀ = ⊤ := by
    rw [←subgroupOf_sup hKD hRD,subgroupOf_self]
  have hquot : IsPGroup 2 (D ⧸ K₀) :=
    isPGroup_quotient_of_sup_eq_top K₀ R₀ hr.isPGroup.comap_subtype hgen
  have hK03 : ¬ 3 ∣ Nat.card (solvableRadical K₀) := by
    have hh := Nat.card_congr ((solvableRadical K₀).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
    rw [map_solvableRadical_equiv e] at hh
    exact hh.symm ▸ hK3
  have hD3 : ¬ 3 ∣ Nat.card (solvableRadical D) := radical_primeTo_three_of_normal_two_quotient K₀ hK03 hquot
  have hfit : twoFittingCore D ≤ M₀ := by
    obtain ⟨n,hn,B,hB,hprod⟩ := ChapterC.Section02Source.fitting_ordered_moved_product
      (hG.subgroup D) R₀ M₀ hrD hcontrolD hcD
    have hfalse (i : Fin n) : False := by
      have ha := (hB i).2.2.2.1
      have h3 : 3 ∣ Nat.card (B i) := by
        obtain ⟨ei⟩ := ha.2.2.quotient_iso
        have hc : Nat.card ((B i) ⧸ pCore 2 (B i)) = 3 := by
          rw [Nat.card_congr ei.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
          rfl
        exact hc ▸ card_quotient_dvd_card (pCore 2 (B i))
      have hfR : twoFittingCore D ≤ solvableRadical D :=
        le_solvableRadical _ inferInstance twoFittingCore_solvable
      exact hD3 (h3.trans (card_dvd_of_le ((hB i).1.trans hfR)))
    have hn0 : n = 0 := by
      by_contra h
      exact hfalse ⟨0,Nat.pos_of_ne_zero h⟩
    subst n
    intro x hx
    obtain ⟨m,hm,l,hl,rfl⟩ := (hprod x).mp hx
    simpa using hm.1
  rintro _ ⟨k,hk,rfl⟩
  have hk0 : e.symm k ∈ twoFittingCore K₀ :=
    twoFittingCore_map_equiv_le e.symm (mem_map_of_mem _ hk)
  exact hfit (twoFittingCore_map_subtype_le_of_normal K₀ (mem_map_of_mem K₀.subtype hk0))

/-- The original C.2.6(2) containment for the nonquasisimple component in 15.2.4. -/
theorem fittingCore_le_of_nonquasisimple_component_setup {W L R M : Subgroup G}
    (hsetup : Chapter1.RadicalExclusions.PushingUpSetup CFSG.KnownSimple.IsKnownSimple W R M)
    (hL : L ∈ Chapter1.cComponentsIn W)
    (hf : generalizedFitting L = pCore 2 L)
    (hnorm : W ≤ normalizer (L : Set G))
    (hn : ¬ IsQuasisimple (L ⧸ pCore 2 L)) :
    (twoFittingCore L).map L.subtype ≤ M := by
  let K := L.subgroupOf W
  let e : K ≃* L := subgroupOfEquivOfLe hL.1
  let : K.Normal := normal_subgroupOf_of_le_normalizer hnorm
  have hKfit : generalizedFitting K = pCore 2 K := by
    apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf)
  have hnK : ¬ IsQuasisimple (K ⧸ pCore 2 K) := by
    intro h
    let := h
    exact hn (IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr (pCore 2 K) (pCore 2 L) e (pCore_map_iso 2 e)))
  have hK3 := ChapterA.Section03.cComponent_radical_primeTo_three_of_not_quasisimple
    hsetup.sqtk hL.2 hnK
  have hfit := fittingCore_le_of_normal_threeFree_radical hsetup.sqtk K (R.subgroupOf W)
    (M.subgroupOf W) hKfit hK3 hsetup.radical hsetup.characteristic_control
  rintro _ ⟨l,hl,rfl⟩
  have hlK : e.symm l ∈ twoFittingCore K :=
    twoFittingCore_map_equiv_le e.symm (mem_map_of_mem _ hl)
  exact hfit (mem_map_of_mem K.subtype hlK)
end CFSG.Quasithin.ChapterC.Section02Source
