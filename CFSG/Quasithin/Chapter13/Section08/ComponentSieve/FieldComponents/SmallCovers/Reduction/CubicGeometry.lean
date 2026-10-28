module
public import Theory.Representation.CubicComponentFaithfulness
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSixDegree.ActorGeometry
public import Theory.Representation.BinaryOffender.NormalThree
public import Theory.Representation.BinaryOffender.InvolutionRatio
public import Theory.Representation.BinaryOffender.RankOneCentralizer
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.CriticalSubspace

/-!
# Cubic-center geometry for the triple-six source action

A fixed-free cubic center forces binary degree divisible by six, by restriction
to the extraspecial Sylow three-group. It also excludes transvections. Every
small quadratic actor centralizes that center; the concrete cover automorphism
theorem and component-centralizer bound then place it in the component.
Three conjugate involutions generate the component, so a critical displacement
line bounds the degree by nine. Divisibility forces six, and the same divisibility
on submodules proves irreducibility on the component.

No homogeneous invariance or module classification is assumed. The original
13.8.21 consumer constructs the critical subspace from F.9.13--16.
Source: Aschbacher--Smith G.7.1, K.1.3 and 13.8.21, printed pp.347,453,956;
GLS3 5.2.3 and 5.2.7 for the triple-cover involutions.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.CubicGeometry
open ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover
variable {D E : Type*} [Group D] [Finite D] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]
  (ρ : Representation (ZMod 2) D E) (K : Subgroup D)
  (e : K ≃* Atlas.Codes.HexEvenAutomorphisms)
  (z : D) (hz : z ∈ K) (hzc : zpowers z = (center K).map K.subtype)
  (hp : CubicPolynomial ρ z)

include ρ K e z hz hzc hp in
/-- The extraspecial Sylow center forces divisibility without irreducibility. -/
theorem six_dvd_finrank : 6 ∣ Module.finrank (ZMod 2) E := by
  let : IsQuasisimple Atlas.Codes.HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv e.symm
  let P : Sylow 3 K := Classical.choice inferInstance
  let f := (QuotientGroup.congr (center K) (center Atlas.Codes.HexEvenAutomorphisms) e (by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (centerCongr e ⟨y,hy⟩).property
    · intro hx
      exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩)).trans
      Hexacode.even_quotient_center_equiv
  have hc : Nat.card (center K) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans Hexacode.even_center_card
  have hP := sylow_three_structure f hc P
  let : IsExtraspecial 3 (P : Subgroup K) := hP.2.1
  apply Representation.BinaryCoprimeDegree.six_dvd_finrank_of_extraspecial_twentySeven
    ((ρ.comp K.subtype).comp (P : Subgroup K).subtype) hP.1
  apply bot_unique
  intro v hv
  have hz' : (⟨z,hz⟩ : K) ∈ center K := by
    have hh := mem_zpowers z
    rw [hzc] at hh
    obtain ⟨w,hw,he⟩ := hh
    exact (Subtype.ext he : w = ⟨z,hz⟩) ▸ hw
  have hh : (⟨z,hz⟩ : K) ∈ (center (P : Subgroup K)).map (P : Subgroup K).subtype := by
    rw [hP.2.2]
    exact hz'
  obtain ⟨w,hw,he⟩ := hh
  apply hp.fixed_eq_zero
  have h := hv ⟨w,hw⟩
  change ρ (((w : P) : K) : D) v = v at h
  change (w : K) = ⟨z,hz⟩ at he
  rwa [he] at h

include hp in
omit [Finite D] in
/-- A fixed-free cubic operator moves the whole binary space. -/
theorem moved_by_cubic : subspaceCommutator ρ ⊤ (zpowers z) = ⊤ := by
  have hi : Function.Injective (ρ z - 1 : E →ₗ[ZMod 2] E) := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    exact hp.fixed_eq_zero (sub_eq_zero.mp hv)
  apply top_unique
  intro v _
  obtain ⟨w,rfl⟩ := LinearMap.surjective_of_injective hi v
  exact Submodule.subset_span ⟨z,mem_zpowers z,w,Submodule.mem_top,rfl⟩

include K e hz hzc hp in
/-- A primitive cubic center excludes rank-one displacements. -/
theorem no_transvections [Nontrivial E]
    (hf : Function.Injective ρ) (ho : orderOf z = 3) (hn : (zpowers z).Normal) :
    ∀ t, Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≠ 1 := by
  intro t hr
  have hd := six_dvd_finrank ρ K e z hz hzc hp
  have hpos := Module.finrank_pos (R := ZMod 2) (M := E)
  by_cases htz : Commute t z
  · have hh : ρ t - LinearMap.id = 0 := by
      ext v
      exact hp.fixed_eq_zero (fixes_displacement_of_commute_rank_one ρ t z hr htz v)
    rw [hh,LinearMap.range_zero,finrank_bot] at hr
    omega
  · have ht2 : t ^ 2 = 1 := by
      apply hf
      rw [map_one]
      ext v
      have h := fixes_displacement_of_commute_rank_one ρ t t hr (Commute.refl t) v
      rw [map_sub,ZModModule.sub_eq_add,ZModModule.sub_eq_add] at h
      have he : ρ t (ρ t v) = v := add_right_cancel (h.trans (add_comm _ _))
      simpa only [pow_two,map_mul,Module.End.mul_apply,Module.End.one_apply] using he
    have ht1 : t ≠ 1 := by
      intro he
      rw [he,map_one,Module.End.one_eq_id,sub_self,LinearMap.range_zero,finrank_bot] at hr
      omega
    obtain ⟨ha,_,hq,_⟩ := involution_actor_rank_and_fixedCodim ρ t (orderOf_eq_prime ht2 ht1)
    have hnot : ¬ zpowers t ≤ centralizer (zpowers z : Set D) := by
      intro hc
      exact htz (show Commute t z from ((mem_centralizer_iff.mp (hc (mem_zpowers t))) z (mem_zpowers z)).symm)
    have hh := normalThree_quadratic_rank_fixedCodim ρ hf (zpowers z) hn
      (by rw [Nat.card_zpowers,ho]) (moved_by_cubic ρ z hp) (zpowers t) ha hq hnot
    rw [fixedCodim_zpowers_eq_displacement_rank,hr] at hh
    omega

include e hz hzc in
omit [Finite D] in
/-- An involution centralizing the cubic center is inner and lies in the component. -/
theorem involution_mem_of_centralizes [K.Normal]
    (hc : centralizer (K : Set D) ≤ K) (ho : orderOf z = 3)
    (t : D) (ht : t ^ 2 = 1) (hcomm : Commute t z) : t ∈ K := by
  let tN : normalizer (K : Set D) := ⟨t, by rw [normalizer_eq_top]; trivial⟩
  let α := K.normalizerMonoidHom tN
  let x := MulAut.congr e α
  have hx : x ^ 2 = 1 := by
    have htN : tN ^ 2 = 1 := Subtype.ext ht
    change (MulAut.congr e (K.normalizerMonoidHom tN)) ^ 2 = 1
    rw [←map_pow,←map_pow,htN,map_one,map_one]
  by_contra hnot
  have hout : ∀ a : Atlas.Codes.HexEvenAutomorphisms, x ≠ MulAut.conj a := by
    intro a ha
    obtain ⟨b,hb⟩ := (MulAut.congr_inner_iff e α).mp ⟨a,ha⟩
    have hcent : (b : D)⁻¹ * t ∈ centralizer (K : Set D) := by
      apply mem_centralizer_iff.mpr
      intro k hk
      have hh := congrArg (fun a : MulAut K => ((a ⟨k,hk⟩ : K) : D)) hb
      change t * k * t⁻¹ = (b : D) * k * (b : D)⁻¹ at hh
      calc
        k * ((b : D)⁻¹ * t) = (b : D)⁻¹ * ((b : D) * k * (b : D)⁻¹) * t := by group
        _ = (b : D)⁻¹ * (t * k * t⁻¹) * t := by rw [hh]
        _ = ((b : D)⁻¹ * t) * k := by group
    exact hnot (by simpa only [mul_inv_cancel_left] using K.mul_mem b.property (hc hcent))
  have hz' : (⟨z,hz⟩ : K) ∈ center K := by
    have hh := mem_zpowers z
    rw [hzc] at hh
    obtain ⟨w,hw,he⟩ := hh
    exact (Subtype.ext he : w = ⟨z,hz⟩) ▸ hw
  have hi := GLS3.Chapter5.TripleSixActorInversion.hexEven_center_inverted x hx hout
    (e ⟨z,hz⟩) ((centerCongr e ⟨⟨z,hz⟩,hz'⟩).property)
  have he : α ⟨z,hz⟩ = (⟨z,hz⟩ : K)⁻¹ := by
    apply e.injective
    simpa only [x,MulAut.congr_apply,MulEquiv.trans_apply,e.symm_apply_apply,map_inv] using hi
  have he' : t * z * t⁻¹ = z⁻¹ := congrArg (fun a : K => (a : D)) he
  have hz2 : z ^ 2 = 1 := by
    have hh : z = z⁻¹ := by simpa only [hcomm.eq,mul_inv_cancel_right] using he'
    rw [pow_two]
    exact inv_eq_iff_mul_eq_one.mp hh.symm
  have hd := orderOf_dvd_of_pow_eq_one hz2
  rw [ho] at hd
  omega

include e hz hzc hp in
/-- Small quadratic actors lie in the actual component. -/
theorem quadratic_actor_le_component [K.Normal] [Nontrivial E]
    (hf : Function.Injective ρ) (hc : centralizer (K : Set D) ≤ K)
    (ho : orderOf z = 3) (A : Subgroup D) (hA : IsElementaryTwo A)
    (hq : IsQuadratic ρ A) (hb : fixedCodim ρ A ≤ 2 * rank A) : A ≤ K := by
  have hn : (zpowers z).Normal := by rw [hzc]; infer_instance
  have hcent : A ≤ centralizer (zpowers z : Set D) := by
    by_contra hnot
    have hh := normalThree_quadratic_rank_fixedCodim ρ hf (zpowers z) hn
      (by rw [Nat.card_zpowers,ho]) (moved_by_cubic ρ z hp) A hA hq hnot
    have hd := six_dvd_finrank ρ K e z hz hzc hp
    have hpos := Module.finrank_pos (R := ZMod 2) (M := E)
    omega
  let : IsElementaryAbelian 2 A := hA.2
  intro t ht
  exact involution_mem_of_centralizes K e z hz hzc hc ho t
    (elemPow_eq_one_of_isElementaryAbelian t ht)
    (((mem_centralizer_iff.mp (hcent ht)) z (mem_zpowers z)).symm)

include e hz hzc hp in
/-- The original critical-line inequalities force binary degree six. -/
theorem degree_six_of_critical [K.Normal] [Nontrivial E]
    (hf : Function.Injective ρ) (hc : centralizer (K : Set D) ≤ K)
    (ho : orderOf z = 3) (A : Subgroup D) (hA : IsElementaryTwo A)
    (hq : IsQuadratic ρ A) (hb : fixedCodim ρ A ≤ 2 * rank A)
    (U S : Submodule (ZMod 2) E)
    (hU : Module.finrank (ZMod 2) (E ⧸ U) ≤ rank A)
    (hS : Module.finrank (ZMod 2) S ≤ 1)
    (hdisp : ∀ a ∈ A, ∀ v ∈ U, ρ a v - v ∈ S) :
    Module.finrank (ZMod 2) E = 6 := by
  have hAK := quadratic_actor_le_component ρ K e z hz hzc hp hf hc ho A hA hq hb
  obtain ⟨t,ht,_,⟨hr,g,hg⟩ | hi⟩ :=
    ChapterK.Alternating.TripleSixReduction.actorGeometry_of_le e hA hAK
  · have hfix : fixedSpace ρ K = ⊥ := by
      apply bot_unique
      intro v hv
      exact hp.fixed_eq_zero (hv ⟨z,hz⟩)
    have hd := finrank_le_mul_fixedCodim_of_conjugate_generation ρ K hfix t g hg
    have htbound := Components.Swapped.displacement_rank_le_of_critical_line ρ U S t (hdisp t ht)
    rw [←fixedCodim_zpowers_eq_displacement_rank] at htbound
    have hdiv := six_dvd_finrank ρ K e z hz hzc hp
    have hpos := Module.finrank_pos (R := ZMod 2) (M := E)
    have h9 : Module.finrank (ZMod 2) E ≤ 9 := by omega
    omega
  · have hz0 : ChapterK.Alternating.TripleSixReduction.centralElement e ∈ K :=
      (e.symm Atlas.Codes.hexEvenZ).property
    have hzt : Commute (ChapterK.Alternating.TripleSixReduction.centralElement e) t := by
      apply Commute.symm
      have hzcent : e.symm Atlas.Codes.hexEvenZ ∈ center K := by
        apply (centerCongr e.symm ⟨Atlas.Codes.hexEvenZ,?_⟩).property
        rw [←Hexacode.even_kernel_eq_center,Atlas.Codes.hexEvenCoordinate_kernel]
        exact mem_zpowers _
      exact ((mem_center_iff.mp hzcent) ⟨t,hAK ht⟩)
        |> congrArg (fun a : K => (a : D))
    have h2 : (ChapterK.Alternating.TripleSixReduction.centralElement e) ^ 2 = 1 := by
      rw [hzt.symm.eq,mul_inv_cancel_right] at hi
      rw [pow_two]
      exact inv_eq_iff_mul_eq_one.mp hi.symm
    have hh := orderOf_dvd_of_pow_eq_one h2
    rw [ChapterK.Alternating.TripleSixReduction.centralElement_order] at hh
    omega
include e hz hzc hp in
/-- Divisibility on every submodule makes the degree-six component action irreducible. -/
theorem component_irreducible_of_degree_six
    (hd : Module.finrank (ZMod 2) E = 6) : IsIrreducible (ρ.comp K.subtype) := by
  let σ := ρ.comp K.subtype
  let zK : K := ⟨z,hz⟩
  have hzK : zpowers zK = center K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [MonoidHom.map_zpowers]
    exact hzc
  have htop : (center (⊤ : Subgroup K)).map (⊤ : Subgroup K).subtype = center K := by
    ext k
    constructor
    · rintro ⟨l,hl,rfl⟩
      apply mem_center_iff.mpr
      intro a
      exact congrArg Subtype.val ((mem_center_iff.mp hl) ⟨a,mem_top a⟩)
    · intro hk
      refine ⟨⟨k,mem_top k⟩,mem_center_iff.mpr ?_,rfl⟩
      intro l
      exact Subtype.ext ((mem_center_iff.mp hk) l)
  have hmark : zpowers zK = (center (⊤ : Subgroup K)).map (⊤ : Subgroup K).subtype :=
    hzK.trans htop.symm
  have hpσ : CubicPolynomial σ zK := hp
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) E)
  let : Nontrivial (Subrepresentation σ) := ⟨⟨⊥,⊤,fun he =>
    bot_ne_top (congrArg Subrepresentation.toSubmodule he)⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro W hb
  have hdiv := six_dvd_finrank W.toRepresentation (⊤ : Subgroup K)
    (Subgroup.topEquiv.trans e) zK (mem_top _) hmark (hpσ.subrepresentation W)
  have hn : W.toSubmodule ≠ ⊥ := fun he => hb (Subrepresentation.toSubmodule_injective he)
  let : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hn
  have hpos := Module.finrank_pos (R := ZMod 2) (M := W.toSubmodule)
  have hle := Submodule.finrank_le W.toSubmodule
  have he : Module.finrank (ZMod 2) W.toSubmodule = Module.finrank (ZMod 2) E := by omega
  apply Subrepresentation.toSubmodule_injective
  exact Submodule.eq_top_of_finrank_eq he

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.CubicGeometry
