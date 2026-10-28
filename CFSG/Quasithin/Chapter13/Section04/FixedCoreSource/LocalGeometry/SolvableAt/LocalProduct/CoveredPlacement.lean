module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.FirstFlagNormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.FirstFlagCore
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CoveredPlacement
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.OrdinaryOriginal
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.GroupTheory.PResidual.SimpleActionCore

/-!
# Normal residuals and the original first action core: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/LocalProduct/CoveredPlacement` proof for the local step.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Core containment holds for the original action preimage in both covering rows. -/
theorem firstFlagCore_local_data_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    firstFlagCore_at h structural D m ≤ T ∧
      (T : Subgroup G) ≤ normalizer (firstFlagCore_at h structural D m : Set G) ∧
      (centralizer ({z.val} : Set G)).pCoreIn 2 ≤ firstFlagCore_at h structural D m := by
  let P := firstFlagNormalizer T L V
  let f := (firstFlagAction_at h structural D m).rangeRestrict
  let a := f.comp (inclusion (sylow_le_firstFlagNormalizer (L := L) (V := V)))
  have hR : firstFlagCore_at h structural D m = ((pCore 2 _).comap a).map (T : Subgroup G).subtype := rfl
  have hPH : P ≤ centralizer ({z.val} : Set G) := by
    change firstFlagNormalizer T L V ≤ _
    exact (LocalGeometry.first_flag_normalizer_eq_centralizer_at h structural D m z hz hzL).le.trans inf_le_right
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
      le_sSup ⟨Normal.map inferInstance f (firstFlagAction_at h structural D m).rangeRestrict_surjective,
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
theorem normal_cubic_firstFlagCore_action_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (Y : Subgroup G) (hYL : Y ≤ L) (hYH : Y ≤ centralizer ({z.val} : Set G))
    (hnY : centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G))
    (hpY : IsPPerfect 2 Y) (hc : Nat.card (Y ⧸ pCore 2 Y) = 3) :
    ⁅Y,firstFlagCore_at h structural D m⁆ ≤ Y.pCoreIn 2 ∧
      Y ≤ normalizer (firstFlagCore_at h structural D m : Set G) := by
  let P := firstFlagNormalizer T L V
  let f := (firstFlagAction_at h structural D m).rangeRestrict
  have hP : P = (L ⊔ (T : Subgroup G)) ⊓ centralizer ({z.val} : Set G) :=
    LocalGeometry.first_flag_normalizer_eq_centralizer_at h structural D m z hz hzL
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
    have he := congrArg (fun g : A →* (firstFlagAction_at h structural D m).range => g ⟨⟨y,hYP hy⟩,hy⟩) hf
    have ha : V.normalizerMonoidHom ⟨y,_⟩ = 1 := congrArg Subtype.val he
    have hb := congrArg (fun g : MulAut V => (g ⟨v,hv⟩).val) ha
    exact (mul_inv_eq_iff_eq_mul.mp hb).symm
  have hk := hpA.kernel_isPGroup_of_simple_core_quotient (f.comp A.subtype) hfne
  let S := T.subtype (sylow_le_firstFlagNormalizer (L := L) (V := V))
  have hn := normalizes_sylow_action_core f A S hk
  have hmap : ((S : Subgroup P) ⊓ (pCore 2 (firstFlagAction_at h structural D m).range).comap f).map P.subtype =
      firstFlagCore_at h structural D m := by
    apply le_antisymm
    · rintro _ ⟨p,hp,rfl⟩
      exact ⟨⟨p.val,hp.1⟩,hp.2,rfl⟩
    · rintro _ ⟨t,ht,rfl⟩
      exact ⟨⟨t.val,sylow_le_firstFlagNormalizer t.property⟩,⟨t.property,ht⟩,rfl⟩
  have hh := (map_mono (f := P.subtype) hn).trans
    (((S : Subgroup P) ⊓ (pCore 2 (firstFlagAction_at h structural D m).range).comap f).le_normalizer_map P.subtype)
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

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
