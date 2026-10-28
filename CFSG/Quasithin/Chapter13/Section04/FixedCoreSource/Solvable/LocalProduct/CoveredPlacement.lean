module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.OrdinaryOriginal
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.GroupTheory.PResidual.SimpleActionCore

/-!
# Normal residuals and the original first action core

In either covering row the original R₁ contains O₂(C_G(z)) and is
T-normalized. A nontrivial normal two-perfect subgroup Y of C_G(z)
inside L cannot centralize V: the literal marking puts such a subgroup
in O₂,Z(L), and residual normalizer lifting would force C_G(z) into M.
If Y/O₂(Y) has order three, its nontrivial V-action has two-group kernel.
The original action-core definition then gives [Y,R₁]≤O₂(Y), and Y
normalizes R₁. These conclusions do not identify R₁ with O₂(L₁T).

CoveredSelection applies this to the residuals supplied by13.3.9 to
exclude the covered row. Its earlier-source premises retain discharge
with qt-d-1341-fixed-core-source and its existing producers; the complete
solvable geometry and fusion remain with qt-d-1341-solvable-source.
Source: Aschbacher--Smith13.2.1,13.3.9,13.4.8, pp.877,887,904--905.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem marking_centralizer_le (D : ChosenModule T L V) (m : CoreMarking D) :
    (centralizer (V : Set G)).subgroupOf L ≤ centralCore L := by
  intro l hl
  have he : BinaryPermutation.coreRepresentation (Fin 6)
      (m.quotient (QuotientGroup.mk' (centralCore L) l)).val = 1 := by
    apply LinearMap.ext
    intro w
    obtain ⟨v,hv⟩ := m.coordinate.surjective (Multiplicative.ofAdd w)
    have he := m.equivariant l v
    have hc : V.normalizerMonoidHom ⟨l.val,D.normalizes l.property⟩ v = v := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hl v.val v.property).symm
    rw [hc,hv] at he
    exact he.symm
  have hn : BinaryPermutation.naturalRepresentation (Fin 6)
      (m.quotient (QuotientGroup.mk' (centralCore L) l)).val = 1 := by
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := BinaryPermutation.coreToNatural_surjective w
    rw [← BinaryPermutation.coreToNatural_equivariant,he]
    rfl
  have hperm : (m.quotient (QuotientGroup.mk' (centralCore L) l)).val = 1 :=
    BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide) (hn.trans (map_one _).symm)
  have hq : QuotientGroup.mk' (centralCore L) l = 1 :=
    m.quotient.injective (by rw [map_one]; exact Subtype.ext hperm)
  exact (QuotientGroup.eq_one_iff l).mp hq

/-- A nontrivial normal two-perfect subgroup of the escaping centralizer,
contained in L, cannot centralize the original module. -/
theorem normal_residual_not_centralizing_core
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (m : CoreMarking D)
    {z : G} (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hout : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (Y : Subgroup G) (hYL : Y ≤ L) (hnY : centralizer ({z} : Set G) ≤ normalizer (Y : Set G))
    (hpY : IsPPerfect 2 Y) (hne : Y ≠ ⊥) : ¬ Y ≤ centralizer (V : Set G) := by
  intro hc
  let A := Y.subgroupOf L
  let q := QuotientGroup.mk' (pCore 2 L)
  have hTA : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    (original_sylow_le_centralizer hz).trans hnY
  have hQT : L.pCoreIn 2 ≤ T := by
    have hQ : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
      pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer D.sylow_normalizes_component)
    have ht := pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)] at ht
    exact hQ.trans ht
  have hQA : q.ker ≤ normalizer (A : Set L) := by
    rw [QuotientGroup.ker_mk',← subgroupOf_normalizer_eq hYL]
    intro a ha
    exact hTA (hQT (mem_map_of_mem L.subtype ha))
  have hAc : A.map q ≤ center (L ⧸ pCore 2 L) := by
    rintro _ ⟨a,ha,rfl⟩
    exact marking_centralizer_le D m (hc ha)
  let : (A.map q).Normal := ⟨by
    intro x hx g
    have hc := (mem_center_iff.mp (hAc hx)) g
    simpa only [hc,mul_inv_cancel_right] using hx⟩
  have hpA : IsPPerfect 2 A := hpY.of_surjective
    (subgroupOfEquivOfLe hYL).symm.toMonoidHom (subgroupOfEquivOfLe hYL).symm.surjective
  have he := comap_normalizer_map_of_pPerfect q A hpA
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) hQA
  rw [normalizer_eq_top,comap_top] at he
  have hLA : L ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYL).mp (normalizer_eq_top_iff.mp he.symm)
  exact hout (hnY.trans (h.normal_subgroup_normalizer_le D.sylow_normalizes_component
    (hYL.trans le_sup_left) hne (sup_le hLA hTA)))

/-- Core containment holds for the original action preimage in both covering rows. -/
theorem firstFlagCore_local_data
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    firstFlagCore h structural D m ≤ T ∧
      (T : Subgroup G) ≤ normalizer (firstFlagCore h structural D m : Set G) ∧
      (centralizer ({z.val} : Set G)).pCoreIn 2 ≤ firstFlagCore h structural D m := by
  let P := firstFlagNormalizer T L V
  let f := (firstFlagAction h structural D m).rangeRestrict
  let a := f.comp (inclusion (sylow_le_firstFlagNormalizer (L := L) (V := V)))
  have hR : firstFlagCore h structural D m = ((pCore 2 _).comap a).map (T : Subgroup G).subtype := rfl
  have hPH : P ≤ centralizer ({z.val} : Set G) := by
    change firstFlagNormalizer T L V ≤ _
    exact (first_flag_normalizer_eq_centralizer h structural D m z hz hzL).le.trans inf_le_right
  have hQP : (centralizer ({z.val} : Set G)).pCoreIn 2 ≤ P.pCoreIn 2 := by
    have hQT : (centralizer ({z.val} : Set G)).pCoreIn 2 ≤ T := by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (original_sylow_le_centralizer hz)]
        using pCoreIn_le_sylow _ (T.subtype (original_sylow_le_centralizer hz))
    exact (le_inf (hQT.trans sylow_le_firstFlagNormalizer) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 hPH)
  have hPT : P.pCoreIn 2 ≤ T := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ P from sylow_le_firstFlagNormalizer)]
      using pCoreIn_le_sylow P (T.subtype sylow_le_firstFlagNormalizer)
  refine ⟨map_subtype_le _,?_,hQP.trans ?_⟩
  · rw [hR]
    have hh := (map_mono (show (⊤ : Subgroup T) ≤ normalizer ((pCore 2 _).comap a : Set T)
        from le_normalizer_of_normal)).trans
        (((pCore 2 _).comap a).le_normalizer_map (T : Subgroup G).subtype)
    simpa only [← MonoidHom.range_eq_map,range_subtype] using hh
  · have him : (pCore 2 P).map f ≤ pCore 2 _ :=
      le_sSup ⟨Normal.map inferInstance f (firstFlagAction h structural D m).rangeRestrict_surjective,
        pCore_isPGroup.map f⟩
    rintro _ ⟨p,hp,rfl⟩
    refine ⟨⟨p.val,hPT (mem_map_of_mem P.subtype hp)⟩,?_,rfl⟩
    exact him (mem_map_of_mem f hp)
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Stellmacher
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original first action-core is normalized by every nontrivial normal
cubic residual inside L. This includes the covered-row residual selected
by13.3.9, without assuming the ordinary row or full action-kernel faithfulness. -/
theorem normal_cubic_firstFlagCore_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (Y : Subgroup G) (hYL : Y ≤ L) (hYH : Y ≤ centralizer ({z.val} : Set G))
    (hnY : centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G))
    (hpY : IsPPerfect 2 Y) (hc : Nat.card (Y ⧸ pCore 2 Y) = 3) :
    ⁅Y,firstFlagCore h structural D m⁆ ≤ Y.pCoreIn 2 ∧
      Y ≤ normalizer (firstFlagCore h structural D m : Set G) := by
  let P := firstFlagNormalizer T L V
  let f := (firstFlagAction h structural D m).rangeRestrict
  have hP : P = (L ⊔ (T : Subgroup G)) ⊓ centralizer ({z.val} : Set G) :=
    first_flag_normalizer_eq_centralizer h structural D m z hz hzL
  have hYP : Y ≤ P := hP.symm ▸ le_inf (hYL.trans le_sup_left) hYH
  let A := Y.subgroupOf P
  let e : A ≃* Y := subgroupOfEquivOfLe hYP
  let : A.Normal := normal_subgroupOf_of_le_normalizer ((hP.le.trans inf_le_right).trans hnY)
  have hpA : IsPPerfect 2 A := hpY.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hcA : Nat.card (A ⧸ pCore 2 A) = 3 :=
    (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).trans hc
  let : IsSimpleGroup (A ⧸ pCore 2 A) := isSimpleGroup_of_prime_card hcA
  have hne : Y ≠ ⊥ := by
    intro he
    rw [he] at hc
    have hh : Nat.card ((⊥ : Subgroup G) ⧸ pCore 2 (⊥ : Subgroup G)) = 1 := Nat.card_unique
    omega
  have hfne : f.comp A.subtype ≠ 1 := by
    intro hf
    apply normal_residual_not_centralizing_core h.toHypothesis1221 D m hz hout
      Y hYL hnY hpY hne
    intro y hy v hv
    have he := congrArg (fun g : A →* (firstFlagAction h structural D m).range => g ⟨⟨y,hYP hy⟩,hy⟩) hf
    have ha : V.normalizerMonoidHom ⟨y,_⟩ = 1 := congrArg Subtype.val he
    have hb := congrArg (fun g : MulAut V => (g ⟨v,hv⟩).val) ha
    exact (mul_inv_eq_iff_eq_mul.mp hb).symm
  have hk := hpA.kernel_isPGroup_of_simple_core_quotient (f.comp A.subtype) hfne
  let S := T.subtype (sylow_le_firstFlagNormalizer (L := L) (V := V))
  have hn := normalizes_sylow_action_core f A S hk
  have hmap : ((S : Subgroup P) ⊓ (pCore 2 (firstFlagAction h structural D m).range).comap f).map P.subtype =
      firstFlagCore h structural D m := by
    apply le_antisymm
    · rintro _ ⟨p,hp,rfl⟩
      exact ⟨⟨p.val,hp.1⟩,hp.2,rfl⟩
    · rintro _ ⟨t,ht,rfl⟩
      exact ⟨⟨t.val,sylow_le_firstFlagNormalizer t.property⟩,⟨t.property,ht⟩,rfl⟩
  have hh := (map_mono (f := P.subtype) hn).trans
    (((S : Subgroup P) ⊓ (pCore 2 (firstFlagAction h structural D m).range).comap f).le_normalizer_map P.subtype)
  rw [map_subgroupOf_eq_of_le hYP,hmap] at hh
  have hb := map_mono (f := P.subtype) (commutator_sylow_action_core_le f A S hk)
  rw [map_commutator,map_subgroupOf_eq_of_le hYP,hmap,
    map_pCoreIn_of_injective 2 A P.subtype P.subtype_injective,
    map_subgroupOf_eq_of_le hYP] at hb
  exact ⟨hb,hh⟩
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Stellmacher
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
theorem selectedFirstResidual_le_component (D : ChosenModule T L V) (z : G) :
    selectedFirstResidual T L V z ≤ L := by
  classical
  unfold selectedFirstResidual
  split_ifs with ho
  · exact (firstCentralizerResidual_le L z).trans inf_le_left
  · let X := L ⊔ (T : Subgroup G)
    let N := L.subgroupOf X
    let : N.Normal := normal_subgroupOf_of_le_normalizer
      (sup_le L.le_normalizer D.sylow_normalizes_component)
    have hgen : N ⊔ (T : Subgroup G).subgroupOf X = ⊤ := by
      rw [← subgroupOf_sup (show L ≤ X from le_sup_left)
        (show (T : Subgroup G) ≤ X from le_sup_right)]
      exact subgroupOf_self X
    have hquot : IsPGroup 2 (X ⧸ N) :=
      isPGroup_quotient_of_sup_eq_top N ((T : Subgroup G).subgroupOf X)
        T.isPGroup'.comap_subtype hgen
    have hres : (pResidual 2 X).map X.subtype ≤ L := by
      have hh := map_mono (f := X.subtype) (show pResidual 2 X ≤ N from sInf_le ⟨inferInstance,hquot⟩)
      rwa [map_subgroupOf_eq_of_le (show L ≤ X from le_sup_left)] at hh
    apply le_trans (plus_le_one L (T : Subgroup G) _ ?_) ((embedded_pResidual_mono 2 inf_le_left).trans hres)
    exact (sylow_le_firstFlagNormalizer (L := L) (V := V)).trans inf_le_right


end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
