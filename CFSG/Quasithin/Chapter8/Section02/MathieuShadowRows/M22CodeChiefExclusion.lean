module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeChiefHomogeneous
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourChiefNormalizer
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourBinaryExclusion
public import Theory.Representation.CommutingTwoCoreKernel
public import Theory.GroupTheory.PResidual.SylowJoin

/-!
# Excluding the original M22 nonsolvable chief action

The actual selected chief supplies homogeneous natural SL₂(4) coordinates.
On A=O²(H)V the scalar commutant constructs the multiplicity action; its
original V-involution has rank-one displacement over the field of four
elements. The two-core of A is killed by irreducibility and the commuting
supplement, allowing descent through its entire two-core. The literal
embedding A/O₂(A) into H/O₂(H) retains the marked residual and involution.
The original outer actor supplies a semilinear coefficient map, contradicting
the intrinsic binary PSL₃ transvection theorem.

The final theorem constructs every chief, natural and homogeneous input
from the same selected pair. Its only model data are the earlier-source
binary residual and outer actor. The companion original Chapter12 consumer
discharges these from the original source catalogue. No full H-action
kernel premise is needed. Source: Aschbacher--Smith 8.2.9, printed p.721,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open NoncentralChiefRefinement Representation.HermitianTensorThree
open scoped IsMulCommutative commutatorElement MonoidAlgebra MatrixGroups Matrix
open Sporadic.Mathieu MathieuCode MathieuCode.M22Quintet MathieuCode.M22Quintet.CocodeTransfer
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE HermitianSource Offenders.Parabolic.Construction
  Normalizer.SmallOvergroups Normalizer.ParabolicReduction.RankSieve
open MathieuCode.NormalizedShadowRows.M22CodeSection
set_option backward.isDefEq.respectTransparency false

private theorem natural_chief_binary_residual_false
    {G Z : Type*} [Group G] [Finite G] [AddCommGroup Z] [Module (ZMod 2) Z]
    [FiniteDimensional (ZMod 2) Z]
    {V H M I R U : Subgroup G} {T : Sylow 2 G}
    [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hHR : H ≤ normalizer (R : Set G))
    (hIC : I ≤ centralizer (U : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hcomm : ⁅R,centralizer (U : Set G)⁆ ≤ R.pCoreIn 2)
    (ρ : Representation (ZMod 2) (R ⊔ H : Subgroup G) Z) [IsIrreducible ρ]
    (r : R →* alternatingGroup (Fin 5))
    (hcoord : M22NaturalHomogeneousCoordinates ρ (inclusion le_sup_left) r)
    (v : V)
    (hv4 : Module.finrank (ZMod 2) (LinearMap.range
      (ρ (inclusion ((show V ≤ I from s.generate ▸ le_sup_left).trans (s.family.le_ambient.trans le_sup_right)) v)-1))=4)
    (K : Subgroup (H ⧸ pCore 2 H)) (hmodel : ClassicalGroup.IsPSL K 3 2)
    (hres : pResidual 2 (H ⧸ pCore 2 H) = K)
    (hVK : (V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) ≤ K)
    (t : H) (α : MulAut K) (hα : α ∉ MulAut.innerSubgroup K)
    (hαt : ∀ k : K, (α k : H ⧸ pCore 2 H) =
      QuotientGroup.mk' (pCore 2 H) t * (k : H ⧸ pCore 2 H) *
        (QuotientGroup.mk' (pCore 2 H) t)⁻¹) : False := by
  let J := R ⊔ H
  let A := (pResidual 2 H).map H.subtype ⊔ V
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hVH : V ≤ H := hVI.trans s.family.le_ambient
  have hAH : A ≤ H := sup_le (map_subtype_le _) hVH
  have hAJ : A ≤ J := hAH.trans le_sup_right
  have hAN : (A.subgroupOf H).Normal := by
    rw [subgroupOf_sup (map_subtype_le _) hVH]
    rw [show ((pResidual 2 H).map H.subtype).subgroupOf H = pResidual 2 H from
      comap_map_eq_self_of_injective H.subtype_injective _]
    apply pResidual_sup_normal_of_sylow_normalizes (T.subtype hH.1.1.2)
    rw [←subgroupOf_normalizer_eq hVH]
    exact fun _ ht => hTV ht
  have hHA : H ≤ normalizer (A : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hAH).mp hAN
  have hAC : A ≤ centralizer (U : Set G) :=
    sup_le (Normalizer.residual_centralizes H I T U (selected_generates_hstar s hH)
      T.isPGroup' hIC hTU) (hVI.trans hIC)
  have hC : ⁅R,A⁆ ≤ R.pCoreIn 2 := (commutator_mono le_rfl hAC).trans hcomm
  have hRcore : R.pCoreIn 2 ≤ J.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le R.le_normalizer hHR)
  have hkill : pCore 2 J ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  have hAR (a : A) (x : R) : Commute (ρ (inclusion hAJ a)) (ρ (inclusion le_sup_left x)) := by
    have hc : Commute (ρ.asGroupHom (inclusion le_sup_left x)) (ρ.asGroupHom (inclusion hAJ a)) := by
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [←map_commutatorElement]
      apply Units.ext
      apply hkill
      apply (mem_map_iff_mem J.subtype_injective).mp
      exact hRcore (hC (commutator_mem_commutator x.property a.property))
    exact (congrArg Units.val hc.eq).symm
  obtain ⟨m,hm,eR,e,heR,he,hd⟩ := hcoord
  obtain ⟨μ,hμ,hμker⟩ := natural_coordinates_multiplicity (ρ := ρ) le_sup_left hAJ m eR e he hAR
  have hHQ : H ≤ normalizer (A.pCoreIn 2 : Set G) := hHA.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hQJ : A.pCoreIn 2 ≤ J := (pCoreIn_le 2 A).trans hAJ
  have hkillA := twoGroup_kernel_of_commuting_supplement ρ
    (R.subgroupOf J) (H.subgroupOf J) ((A.pCoreIn 2).subgroupOf J)
    (by
      rw [←subgroupOf_sup (show R ≤ J from le_sup_left) (show H ≤ J from le_sup_right)]
      exact subgroupOf_self _)
    (isPGroup_pCoreIn 2 A).comap_subtype
    (by
      rw [←subgroupOf_normalizer_eq hQJ]
      exact fun _ hh => hHQ hh)
    (by
      intro x a
      exact (hAR ⟨a,(pCoreIn_le 2 A) a.property⟩ ⟨x,x.property⟩).symm)
  have hμN : pCore 2 A ≤ μ.ker := by
    intro a ha
    have hh : a ∈ μ.asGroupHom.ker := by
      rw [hμker]
      apply Units.ext
      exact hkillA (mem_map_of_mem A.subtype ha)
    exact congrArg Units.val hh
  let fA : A →* (H ⧸ pCore 2 H) :=
    (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hAH)
  have hfA : fA.ker = pCore 2 A := by
    ext a
    change inclusion hAH a ∈ (QuotientGroup.mk' (pCore 2 H)).ker ↔ a ∈ pCore 2 A
    rw [QuotientGroup.ker_mk']
    constructor
    · intro ha
      have hh : (a : G) ∈ A.pCoreIn 2 :=
        pCoreIn_inf_le_of_normalizes (hAH.trans H.le_normalizer)
          ⟨mem_map_of_mem H.subtype ha,a.property⟩
      exact (mem_map_iff_mem A.subtype_injective).mp hh
    · intro ha
      have hh : (a : G) ∈ H.pCoreIn 2 :=
        pCoreIn_mono_of_normalizes hAH hHA (mem_map_of_mem A.subtype ha)
      exact (mem_map_iff_mem H.subtype_injective).mp hh
  let j : (A ⧸ pCore 2 A) →* (H ⧸ pCore 2 H) :=
    QuotientGroup.lift (pCore 2 A) fA hfA.ge
  have hj : Function.Injective j := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_lift,hfA]
    exact QuotientGroup.map_mk'_self _
  have hje (a : A) : j (QuotientGroup.mk' (pCore 2 A) a) =
      QuotientGroup.mk' (pCore 2 H) (inclusion hAH a) := rfl
  have hresj : pResidual 2 (H ⧸ pCore 2 H) ≤ j.range := by
    rw [←map_pResidual_of_surjective 2 (QuotientGroup.mk' (pCore 2 H))
      (QuotientGroup.mk'_surjective _)]
    rintro _ ⟨x,hx,rfl⟩
    let a : A := ⟨x,mem_sup_left (mem_map_of_mem H.subtype hx)⟩
    exact ⟨QuotientGroup.mk' (pCore 2 A) a,rfl⟩
  let a : A := inclusion (show V ≤ A from le_sup_right) v
  have ha2 : a^2=1 := by
    rw [←map_pow,Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) v,map_one]
  have harank : Module.finrank (ZMod 2) (LinearMap.range (ρ (inclusion hAJ a)-1))=4 := hv4
  obtain ⟨_,hr⟩ := natural_multiplicity_transvection (ρ := ρ) hAJ m e μ hμ a ha2 harank
  obtain ⟨τ,s₀,f,hs₀,hsemis,hpure,hsemif,hf⟩ :=
    natural_coordinates_normalizer (ρ := ρ) le_sup_left hAJ le_sup_right hHR hHA
      m eR e he μ hμ t
  let μq := μ.quotientOfLEKer (pCore 2 A) hμN
  let aq := QuotientGroup.mk' (pCore 2 A) a
  have hrq : Module.finrank (E 1) (LinearMap.range (μq aq-1))=1 := hr
  have haK : j aq ∈ K := hVK ⟨inclusion hVH v,v.property,rfl⟩
  have hane : j aq ≠ 1 := by
    intro hh
    have hz : aq=1 := hj (hh.trans j.map_one.symm)
    rw [hz,map_one,sub_self,LinearMap.range_zero,finrank_bot] at hrq
    contradiction
  let γ := pCoreNormalizerAction 2 A (inclusion hHA t)
  have hγ (b : A ⧸ pCore 2 A) : j (γ b)=
      QuotientGroup.mk' (pCore 2 H) t * j b * (QuotientGroup.mk' (pCore 2 H) t)⁻¹ := by
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) b
    change j (pCoreNormalizerAction 2 A (inclusion hHA t) (QuotientGroup.mk' (pCore 2 A) b)) = _
    rw [pCoreNormalizerAction_mk,hje,hje,←map_inv,←map_mul,←map_mul]
    apply congrArg (QuotientGroup.mk' (pCore 2 H))
    apply Subtype.ext
    rfl
  have hfq (b : A ⧸ pCore 2 A) (z : Fin m → E 1) :
      f (μq b z)=μq (γ b) (f z) := by
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) b
    change f (μ b z)=μq (pCoreNormalizerAction 2 A (inclusion hHA t)
      (QuotientGroup.mk' (pCore 2 A) b)) (f z)
    rw [pCoreNormalizerAction_mk]
    exact hf b z
  exact embedded_binary_residual_transvection_false K hmodel
    (by
      rw [card_E]
      norm_num) j hj (hres ▸ hresj) μq aq haK
    (by rw [←map_pow,ha2,map_one]) hane hrq (QuotientGroup.mk' (pCore 2 H) t)
      α hα hαt γ hγ f hfq

private theorem local_natural_chief_lift
    {G Z : Type*} [Group G] [AddCommGroup Z] [Module (ZMod 2) Z]
    (V I R H U : Subgroup G) (hVI : V ≤ I) (hIH : I ≤ H)
    (hRU : R ≤ normalizer (U : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (ρ₀ : Representation (ZMod 2) (SmallRows.localImage U (R ⊔ H)) Z) [IsIrreducible ρ₀]
    (a : R →* SmallRows.localImage U (R ⊔ H))
    (t : I →* SmallRows.localImage U (R ⊔ H))
    (ha : ∀ x, (a x : normalizer (U : Set G) ⧸ U.subgroupOf (normalizer (U : Set G))) =
      QuotientGroup.mk' (U.subgroupOf (normalizer (U : Set G))) ⟨x.val,hRU x.property⟩)
    (ht : ∀ x, (t x : normalizer (U : Set G) ⧸ U.subgroupOf (normalizer (U : Set G))) =
      QuotientGroup.mk' (U.subgroupOf (normalizer (U : Set G))) ⟨x.val,hHU (hIH x.property)⟩)
    (r : R →* alternatingGroup (Fin 5))
    (hcoords : M22NaturalHomogeneousCoordinates ρ₀ a r)
    (v : V) (hv4 : Module.finrank (ZMod 2) (LinearMap.range (ρ₀ (t (inclusion hVI v))-1))=4) :
    ∃ ρ : Representation (ZMod 2) (R ⊔ H : Subgroup G) Z,
      IsIrreducible ρ ∧ M22NaturalHomogeneousCoordinates ρ (inclusion le_sup_left) r ∧
      Module.finrank (ZMod 2) (LinearMap.range
        (ρ (inclusion (hVI.trans (hIH.trans le_sup_right)) v)-1))=4 := by
  let N := normalizer (U : Set G)
  let J := R ⊔ H
  let Jq := SmallRows.localImage U J
  let q := QuotientGroup.mk' (U.subgroupOf N)
  have hJN : J ≤ N := sup_le hRU hHU
  let π : J →* Jq := (q.comp (inclusion hJN)).codRestrict Jq
    (fun x => ⟨inclusion hJN x,x.property,rfl⟩)
  have hπ : Function.Surjective π := by
    intro z
    obtain ⟨x,hx,hxz⟩ := z.property
    exact ⟨⟨x.val,hx⟩,Subtype.ext hxz⟩
  let ρ := ρ₀.comp π
  have hirr : IsIrreducible ρ := (irreducible_comp_surjective_iff π hπ ρ₀).mpr inferInstance
  have hpa (x : R) : π (inclusion (show R ≤ J from le_sup_left) x)=a x :=
    Subtype.ext (ha x).symm
  have hpt (x : I) : π (inclusion (hIH.trans (show H ≤ J from le_sup_right)) x)=t x :=
    Subtype.ext (ht x).symm
  refine ⟨ρ,hirr,?_,?_⟩
  · obtain ⟨m,hm,eR,e,heR,he,hd⟩ := hcoords
    refine ⟨m,hm,eR,e,heR,?_,hd⟩
    intro x z
    change e (ρ₀ (π (inclusion le_sup_left x)) z) = _
    rw [hpa]
    exact he x z
  · have hpv : ρ (inclusion (hVI.trans (hIH.trans le_sup_right)) v) = ρ₀ (t (inclusion hVI v)) :=
      congrArg ρ₀ (hpt (inclusion hVI v))
    exact (congrArg (fun f : Module.End (ZMod 2) Z =>
      Module.finrank (ZMod 2) (LinearMap.range (f-1))) hpv).trans hv4

/-- The original selected M22 chief excludes the binary residual and its
actual outer actor. No natural, homogeneous, chief or multiplicity premise
is assumed; all are constructed from the unchanged selected pair. -/
theorem selected_m22_binary_residual_false
    {G : Type*} [Group G] [Finite G]
    {V H M I R U : Subgroup G} {T : Sylow 2 G}
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 U]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hHR : H ≤ normalizer (R : Set G))
    (hRP : R ≤ normalizer (I.pCoreIn 2 : Set G))
    (hPH : I.pCoreIn 2 ≤ H.pCoreIn 2)
    (hHU : H ≤ normalizer (U : Set G))
    (hIC : I ≤ centralizer (U : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hinter : V ⊓ I.pCoreIn 2 = V ⊓ H.pCoreIn 2)
    (hcomm : ⁅R,centralizer (U : Set G)⁆ ≤ R.pCoreIn 2)
    {fq : R →* MathieuCode.M22Quintet.Q}
    (hs : M22FiveSection R (V ⊓ I.pCoreIn 2) U fq)
    (hm : M22CodePairMultiplicityAction R I V U i fq)
    (hc : Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2)))
    (K : Subgroup (H ⧸ pCore 2 H)) (hmodel : ClassicalGroup.IsPSL K 3 2)
    (hres : pResidual 2 (H ⧸ pCore 2 H) = K)
    (hVK : (V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) ≤ K)
    (t₀ : H) (α : MulAut K) (hα : α ∉ MulAut.innerSubgroup K)
    (hαt : ∀ k : K, (α k : H ⧸ pCore 2 H) =
      QuotientGroup.mk' (pCore 2 H) t₀ * (k : H ⧸ pCore 2 H) *
        (QuotientGroup.mk' (pCore 2 H) t₀)⁻¹) : False := by
  have hcommI : ⁅R,I⁆ ≤ R.pCoreIn 2 := (commutator_mono le_rfl hIC).trans hcomm
  obtain ⟨t,ht,A,C,hφA,hAC,hCE,hCcore,hactive,hWC,hWA,hEl,hRU,a,r,ha,hrs,hrker,hrval,
    v,hy2,hnat,hstable,hcoords⟩ :=
    selected_m22_active_chief_homogeneous s hH hTV hHR hRP hPH hHU hinter hcommI hs hm hc
  let := hEl
  let ρ₀ := binarySectionRepresentation A C
  let : IsIrreducible ρ₀ := binarySection_irreducible A C hAC
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  obtain ⟨ρ,hirr,hcoords',hv4⟩ := local_natural_chief_lift V I R H U hVI
    s.family.le_ambient hRU hHU ρ₀ a t ha ht r hcoords v hnat.choose_spec.2.2.1
  let := hirr
  exact natural_chief_binary_residual_false s hH hTV hHR hIC hTU hcomm
    ρ r hcoords' v hv4 K hmodel hres hVK t₀ α hα hαt

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
