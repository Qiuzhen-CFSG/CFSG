module
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceSylow
public import Theory.GroupAction.PPerfectFixedCentralizer
public import Theory.ElementaryAbelian.Quotient
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.FrattiniQuotient
public import Theory.GroupTheory.ReducedNormal.Defs

-- The proof uses the defining normal-core containment from B.6.8.
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The original residual commutator module in D.1.4

Let I=[U,O²(G₂)] in the centralizing core-closure branch. The residual
commutator calculation makes O²(G₂) commute with O₂(G₂) on I. Thompson's
A×B lemma forces C_I(O₂(G₂)) to be moved by O²(G₂). The actual unique
chief-layer dichotomy then makes that fixed subgroup all of I, proving
I≤Z(O₂(G₂)). The minimal-parabolic kernel theorem B.6.8(6c) proves that
this same intrinsic I is a reduced normal module with its literal
centralizer quotient. No FF or Thompson conclusion is assumed.
Source: Aschbacher–Smith, D.1.4, printed p.176.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}

theorem residual_module_le_span (_d : QRCConfiguration G₁ G₂ T V) :
    ⁅conjugateSpan G₂ V,(pResidual 2 G₂).map G₂.subtype⁆ ≤ conjugateSpan G₂ V :=
  le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans (conjugateSpan_normalized G₂ V))

theorem residual_module_normalized (_d : QRCConfiguration G₁ G₂ T V) :
    G₂ ≤ normalizer ((⁅conjugateSpan G₂ V,(pResidual 2 G₂).map G₂.subtype⁆ : Subgroup G) : Set G) := by
  have hK : G₂ ≤ normalizer ((pResidual 2 G₂).map G₂.subtype : Set G) := by
    have hn := (pResidual 2 G₂).le_normalizer_map G₂.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hn
    exact hn
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (conjugateSpan_normalized G₂ V hg),
    mem_normalizer_iff_map_conj_eq.mp (hK hg)]

theorem residual_module_elementary (d : QRCConfiguration G₁ G₂ T V)
    (hV : V ≤ twoCoreIn G₂)
    (hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G)) :
    IsElementaryAbelian 2 (⁅conjugateSpan G₂ V,(pResidual 2 G₂).map G₂.subtype⁆ : Subgroup G) := by
  let U := conjugateSpan G₂ V
  let I := ⁅U,(pResidual 2 G₂).map G₂.subtype⁆
  let := span_elementary_of_centralizes d hV hc
  have hIU : I ≤ U := residual_module_le_span d
  exact
    { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (congrArg (fun z : U => (z : G))
        (mul_comm (inclusion hIU x) (inclusion hIU y)))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        (fun x => Subtype.ext (elemPow_eq_one_of_isElementaryAbelian
          (p := 2) (A := U) (x : G) (hIU x.property))) }

theorem source_residual_module_centralizes_core
    (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
    (hu : HasUniqueNoncentralChiefFactor G₂ V)
    (hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G)) :
    ⁅conjugateSpan G₂ V,(pResidual 2 G₂).map G₂.subtype⁆ ≤
      (center (twoCoreIn G₂)).map (twoCoreIn G₂).subtype := by
  let := d.finite_right
  let U := conjugateSpan G₂ V
  let K := (pResidual 2 G₂).map G₂.subtype
  let I := ⁅U,K⁆
  let X := I ⊓ centralizer (twoCoreIn G₂ : Set G)
  have hKH : K ≤ G₂ := map_subtype_le _
  have hKU : K ≤ normalizer (U : Set G) := hKH.trans (conjugateSpan_normalized G₂ V)
  have hIU : I ≤ U := le_normalizer_iff_commutator_le_left.mp hKU
  have hUR₂ : U ≤ twoCoreIn G₂ := span_le_right_core d hV
  have hIH : I ≤ G₂ := hIU.trans (hUR₂.trans (twoCore_le G₂))
  have hHK : G₂ ≤ normalizer (K : Set G) := by
    have hn := (pResidual 2 G₂).le_normalizer_map G₂.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hn
    exact hn
  have hHI : G₂ ≤ normalizer (I : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change I.map (MulAut.conj g).toMonoidHom = I
    have hu : U.map (MulAut.conj g).toMonoidHom = U :=
      mem_normalizer_iff_map_conj_eq.mp (conjugateSpan_normalized G₂ V hg)
    have hk : K.map (MulAut.conj g).toMonoidHom = K :=
      mem_normalizer_iff_map_conj_eq.mp (hHK hg)
    rw [map_commutator,hu,hk]
  have hHX : G₂ ≤ normalizer (X : Set G) :=
    (le_inf hHI ((twoCore_normalized G₂).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hIX : I ≤ X := by
    rcases (source_chiefLayerGeometry d hV hu).normal_subgroup_dichotomy X
      (inf_le_left.trans hIU) hHX with hz | hle
    · let := span_elementary_of_centralizes d hV hc
      let : IsElementaryAbelian 2 I :=
        { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (congrArg (fun z : U => (z : G))
            (mul_comm (inclusion hIU x) (inclusion hIU y)))⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
            (fun x => Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) (x : G) (hIU x.property))) }
      let I0 := I.subgroupOf G₂
      let : IsElementaryAbelian 2 I0 := IsElementaryAbelian.subgroupOf hIH
      have hn : G₂ ≤ normalizer (I : Set G) := hHI
      let : I0.Normal := normal_subgroupOf_of_le_normalizer hn
      have hRK : ⁅twoCoreIn G₂,K⁆ ≤ twoCoreIn G₁ ⊓ twoCoreIn G₂ :=
        core_residual_commutator_le_intersection d
          (intersection_normalized_of_centralizes d hc)
          (source_residual_eq_commutator_of_coreClosure_centralizes d (module_ne_bot hu) hc)
      have hUI : U ≤ centralizer ((twoCoreIn G₁ ⊓ twoCoreIn G₂ : Subgroup G) : Set G) :=
        span_centralizes_intersection_of_centralizes d hc
      have hcomm : ⁅pCore 2 G₂,pResidual 2 G₂⁆ ≤ centralizer (I0 : Set G₂) := by
        intro c hc0 i hi
        have hm := mem_map_of_mem G₂.subtype hc0
        rw [map_commutator] at hm
        have hb := hRK hm
        apply Subtype.ext
        exact (hUI (hIU hi) c hb).symm
      have hfix : ⁅I0 ⊓ centralizer (pCore 2 G₂ : Set G₂),pResidual 2 G₂⁆ = ⊥ := by
        apply commutator_eq_bot_iff_le_centralizer.mpr
        intro x hx r hr
        have hxr : (x : G) ∈ centralizer (twoCoreIn G₂ : Set G) := by
          rintro q ⟨q,hq,rfl⟩
          exact congrArg G₂.subtype (hx.2 q hq)
        apply Subtype.ext
        exact (commutator_eq_bot_iff_le_centralizer.mp hz) ⟨hx.1,hxr⟩ r (mem_map_of_mem G₂.subtype hr)
      have hzI := (isPPerfect_pResidual (G := G₂) 2).centralizes_of_commuting_fixed
        (pResidual 2 G₂) (pCore 2 G₂) I0 pCore_isPGroup
        le_normalizer_of_normal le_normalizer_of_normal hcomm hfix
      have hm := congrArg (map G₂.subtype) hzI
      rw [map_commutator, Subgroup.map_bot] at hm
      change ⁅I0.map G₂.subtype,K⁆ = ⊥ at hm
      have hIm : I0.map G₂.subtype = I := map_subgroupOf_eq_of_le hIH
      rw [hIm] at hm
      have hid : ⁅I,K⁆ = I := residual_commutator_idempotent d hV
      exact ((residual_commutator_ne_bot d (module_ne_bot hu)) (hid.symm.trans hm)).elim
    · exact hle
  intro i hi
  refine ⟨⟨i,hUR₂ (hIU hi)⟩,?_,rfl⟩
  apply mem_center_iff.mpr
  intro q
  exact Subtype.ext ((hIX hi).2 q q.property)
theorem source_residual_module_reduced
    (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
    (hu : HasUniqueNoncentralChiefFactor G₂ V)
    (hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G)) :
    Theory.GroupTheory.IsPReduced 2
      ((⁅conjugateSpan G₂ V,(pResidual 2 G₂).map G₂.subtype⁆ : Subgroup G).subgroupOf G₂) := by
  let := d.finite_right
  let U := conjugateSpan G₂ V
  let K := (pResidual 2 G₂).map G₂.subtype
  let I := ⁅U,K⁆
  let I0 := I.subgroupOf G₂
  have hIH : I ≤ G₂ := (residual_module_le_span d).trans
    ((span_le_right_core d hV).trans (twoCore_le G₂))
  let : I0.Normal := normal_subgroupOf_of_le_normalizer (residual_module_normalized d)
  let : IsElementaryAbelian 2 I := residual_module_elementary d hV hc
  let : IsElementaryAbelian 2 I0 := IsElementaryAbelian.subgroupOf hIH
  obtain ⟨S,hS⟩ := d.sylow_right
  have hP := intrinsic_minimalParabolic_of_coreClosure_centralizes d (module_ne_bot hu) hc S hS
  have hnot : ¬ pResidual 2 G₂ ≤ centralizer (I0 : Set G₂) := by
    intro hz
    have hiK : I ≤ centralizer (K : Set G) := by
      intro i hi r hr
      obtain ⟨r,hr,rfl⟩ := hr
      exact congrArg G₂.subtype ((hz hr) ⟨i,hIH hi⟩ hi).symm
    have he := commutator_eq_bot_iff_le_centralizer.mpr hiK
    have hid : ⁅I,K⁆ = I := residual_commutator_idempotent d hV
    exact residual_commutator_ne_bot d (module_ne_bot hu) (hid.symm.trans he)
  have hM : centralizer (I0 : Set G₂) ≤ ChapterB.minimalParabolicMax S hP :=
    (ChapterB.minimalParabolic_normal_le_core_of_residual_not_le S hP _ hnot).trans
      (by change (ChapterB.minimalParabolicMax S hP).normalCore ≤ _; exact normalCore_le _)
  have hQC : pCore 2 G₂ ≤ centralizer (I0 : Set G₂) := by
    intro r hr i hi
    obtain ⟨z,hz,he⟩ := source_residual_module_centralizes_core d hV hu hc hi
    have hrR : (r : G) ∈ twoCoreIn G₂ := mem_map_of_mem G₂.subtype hr
    have hh := congrArg (fun z : twoCoreIn G₂ => (z : G))
      (mem_center_iff.mp hz ⟨r,hrR⟩)
    change (r : G) * (z : G) = (z : G) * (r : G) at hh
    change (z : G) = (i : G) at he
    rw [he] at hh
    exact Subtype.ext hh.symm
  exact ⟨inferInstance,inferInstance,
    ChapterB.minimalParabolic_quotient_twoCore_eq_bot_of_kernel S hP _ hM hQC⟩

theorem source_dualFF_or_reduced_residual
    (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
    (hu : HasUniqueNoncentralChiefFactor G₂ V) :
    DualFF d ∨
      (⁅conjugateSpan G₂ V,(pResidual 2 G₂).map G₂.subtype⁆ ≤
          (center (twoCoreIn G₂)).map (twoCoreIn G₂).subtype ∧
        Theory.GroupTheory.IsPReduced 2
          ((⁅conjugateSpan G₂ V,(pResidual 2 G₂).map G₂.subtype⁆ : Subgroup G).subgroupOf G₂)) := by
  rcases source_dualFF_or_coreClosure_centralizes d hV hu with hf | hc
  · exact Or.inl hf
  · exact Or.inr ⟨source_residual_module_centralizes_core d hV hu hc,
      source_residual_module_reduced d hV hu hc⟩

end CFSG.Quasithin.ChapterD.UniqueFactor
