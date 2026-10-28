module

public import CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry.ActorParameters


/-!
# Actual paired hyperplane closure and point

For an intersecting pair of natural six-spaces, the elements with larger
centralizer generate intrinsic hyperplanes on both sides. Their commutator
is the distinguished point of the standard three-space. Computing it in
both natural charts proves that the two distinguished points agree.

Source: Aschbacher–Smith 13.3.12(4), printed p.890.
-/

public section

open Subgroup Module Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open Atlas.G2.Natural.BinaryIsotropicThree
variable {G : Type*} [Group G] {V U R : Subgroup G}
  [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 U]

def pairHyperplane (A B R : Subgroup G) : Subgroup G :=
  Subgroup.closure {a | a∈A ∧ ∃b∈B,b∉R ∧ Commute a b}

theorem pairHyperplane_le (A B R : Subgroup G) : pairHyperplane A B R≤A :=
  (Subgroup.closure_le _).mpr fun _ h=>h.1

theorem actor_pairHyperplane_eq
    (E : Additive V≃ₗ[K] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hUN : U≤normalizer (V:Set G)) (q : Additive U→ₗ[K]Three)
    (hq : ∀u : U,f (V.normalizerMonoidHom.rangeRestrict ⟨u.val,hUN u.property⟩)=
      Atlas.G2.EvenTwoRank.elementaryEmbedding K (Multiplicative.ofAdd (q (Additive.ofMul u))))
    (hR : (ambientSpace (V:=V) R).map E.toLinearMap=target false) :
    pairHyperplane U V R=ambientGroup (V:=U) ((LinearMap.proj (2:Fin 3)).comp q).ker := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro u ⟨hu,hv⟩
    have hzero := (actor_hyperplane_criterion E f he R hR ⟨u,hUN hu⟩
      (q (Additive.ofMul ⟨u,hu⟩)) (hq ⟨u,hu⟩)).mp hv
    exact ⟨⟨u,hu⟩,hzero,rfl⟩
  · rintro u ⟨a,ha,rfl⟩
    apply Subgroup.subset_closure
    refine ⟨a.property,?_⟩
    exact (actor_hyperplane_criterion E f he R hR ⟨a.val,hUN a.property⟩
      (q (Additive.ofMul a)) (hq a)).mpr ha

theorem vector_pairHyperplane_eq
    (E : Additive V≃ₗ[K] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hUN : U≤normalizer (V:Set G)) (q : Additive U→ₗ[K]Three) (hqs : Function.Surjective q)
    (hq : ∀u : U,f (V.normalizerMonoidHom.rangeRestrict ⟨u.val,hUN u.property⟩)=
      Atlas.G2.EvenTwoRank.elementaryEmbedding K (Multiplicative.ofAdd (q (Additive.ofMul u))))
    (hker : ∀u : U,q (Additive.ofMul u)=0 ↔ u.val∈R) :
    pairHyperplane V U R=ambientGroup (V:=V) ((LinearMap.proj (5:Fin 6)).comp E.toLinearMap).ker := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro v ⟨hv,u,hu,hr,hc⟩
    have hz := (vector_hyperplane_criterion E f he hUN q hqs hq R hker
      (Additive.ofMul ⟨v,hv⟩)).mp ⟨u,hu,hr,hc.symm⟩
    exact ⟨⟨v,hv⟩,hz,rfl⟩
  · rintro v ⟨a,ha,rfl⟩
    apply Subgroup.subset_closure
    refine ⟨a.property,?_⟩
    obtain ⟨u,hu,hr,hc⟩ := (vector_hyperplane_criterion E f he hUN q hqs hq R hker
      (Additive.ofMul a)).mpr ha
    exact ⟨u,hu,hr,hc.symm⟩

theorem pairHyperplane_commutator_eq_point
    (E : Additive V≃ₗ[K] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hUN : U≤normalizer (V:Set G)) (q : Additive U→ₗ[K]Three) (hqs : Function.Surjective q)
    (hq : ∀u : U,f (V.normalizerMonoidHom.rangeRestrict ⟨u.val,hUN u.property⟩)=
      Atlas.G2.EvenTwoRank.elementaryEmbedding K (Multiplicative.ofAdd (q (Additive.ofMul u))))
    (hker : ∀u : U,q (Additive.ofMul u)=0 ↔ u.val∈R)
    (hR : (ambientSpace (V:=V) R).map E.toLinearMap=target false) :
    ⁅pairHyperplane U V R,pairHyperplane V U R⁆=zpowers (E.symm firstVector).toMul.val := by
  let P := ambientGroup (V:=U) ((LinearMap.proj (2:Fin 3)).comp q).ker
  let Q := ambientGroup (V:=V) ((LinearMap.proj (5:Fin 6)).comp E.toLinearMap).ker
  rw [actor_pairHyperplane_eq E f he hUN q hq hR,
    vector_pairHyperplane_eq E f he hUN q hqs hq hker]
  change ⁅P,Q⁆=zpowers (E.symm firstVector).toMul.val
  have hcomm (u : U) (v : Additive V) :
      ⁅u.val,v.toMul.val⁆=(E.symm
        (targetEmbed false (pairCommutator (q (Additive.ofMul u)) (tailCoordinate (E v))))).toMul.val := by
    have hh := actor_parameter_displacement E f he hUN q hq u v
    have hx := congrArg (fun v : Additive V=>v.toMul.val) (E.symm_apply_eq.mpr hh.symm)
    change (E.symm _).toMul.val=(V.normalizerMonoidHom ⟨u.val,hUN u.property⟩ v.toMul / v.toMul).val at hx
    rw [Subgroup.coe_div,Subgroup.normalizerMonoidHom_apply_apply_coe,div_eq_mul_inv] at hx
    simpa only [commutatorElement_def,mul_assoc] using hx.symm
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    rintro u ⟨a,ha,rfl⟩ v ⟨b,hb,rfl⟩
    have hh : ⁅a.val,b.val⁆=(E.symm
      (targetEmbed false (pairCommutator (q (Additive.ofMul a)) (tailCoordinate (E (Additive.ofMul b)))))).toMul.val :=
        hcomm a (Additive.ofMul b)
    change ⁅a.val,b.val⁆∈_
    rw [hh]
    have hβ := pairCommutator_hyperplanes (q (Additive.ofMul a))
      (tailCoordinate (E (Additive.ofMul b))) ha hb
    rw [hβ]
    generalize hval : q (Additive.ofMul a) 0*tailCoordinate (E (Additive.ofMul b)) 1+
      q (Additive.ofMul a) 1*tailCoordinate (E (Additive.ofMul b)) 0=c
    rcases (show ∀c : K,c=0∨c=1 by decide +kernel) c with rfl|rfl
    · have hz : targetEmbed false ![0,0,0]=0 := by ext i;fin_cases i <;> rfl
      rw [hz,map_zero]
      exact (zpowers _).one_mem
    · change (E.symm firstVector).toMul.val∈zpowers (E.symm firstVector).toMul.val
      exact mem_zpowers _
  · apply zpowers_le.mpr
    obtain ⟨u,hu⟩ := hqs ![1,0,0]
    let v := E.symm ![0,0,0,0,1,0]
    have huP : u.toMul.val∈P := by
      refine ⟨u.toMul,?_,rfl⟩
      change q u 2=0
      rw [hu]
      rfl
    have hvQ : v.toMul.val∈Q := by
      refine ⟨v.toMul,?_,rfl⟩
      change E (E.symm ![0,0,0,0,1,0]) 5=0
      rw [E.apply_symm_apply]
      rfl
    have hh := Subgroup.commutator_mem_commutator huP hvQ
    rw [hcomm u.toMul v] at hh
    change (E.symm (targetEmbed false (pairCommutator (q u) (tailCoordinate (E v))))).toMul.val∈_ at hh
    rw [hu] at hh
    change (E.symm (targetEmbed false (pairCommutator ![1,0,0]
      (tailCoordinate (E (E.symm ![0,0,0,0,1,0])))))).toMul.val∈_ at hh
    rw [E.apply_symm_apply] at hh
    exact hh

variable [Finite G]

theorem pairHyperplane_point_of_marked_offender
    (E : Additive V≃ₗ[K] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hc : ⁅V,U⁆≤V⊓U) (hA : IsOffender rho ((inducedAutomizer V U).map f))
    (hU : Nat.card U=64)
    (hR : (ambientSpace (V:=V) (V⊓U)).map E.toLinearMap=target false) :
    ⁅pairHyperplane U V (V⊓U),pairHyperplane V U (V⊓U)⁆=
      zpowers (E.symm firstVector).toMul.val := by
  have hUN : U≤normalizer (V:Set G) := le_normalizer_iff_commutator_le_left.mpr (hc.trans inf_le_left)
  have himage := image_eq_elementary_of_intersection_marking E f he hA hUN hR
  obtain ⟨q,hqs,hq⟩ := exists_actor_parameters f hUN himage
  have hC := actor_centralizer_eq_intersection_of_offender E f he hA hc hU
  apply pairHyperplane_commutator_eq_point E f he hUN q hqs hq _ hR
  intro u
  rw [actor_parameter_kernel E f he hUN q hq]
  constructor
  · intro hu
    exact hC ▸ (show u.val∈U⊓centralizer (V:Set G) from ⟨u.property,hu⟩)
  · intro hu
    exact (show u.val∈U⊓centralizer (V:Set G) from hC.symm ▸ hu).2

theorem image_offender_of_two_natural_actions
    (EV : Additive V≃ₗ[K] W) (fV : Automizer V→*Atlas.G2.Model K)
    (heV : ∀a v,EV (automizerRepresentation V a v)=rho (fV a) (EV v))
    (EU : Additive U≃ₗ[K] W) (fU : Automizer U→*Atlas.G2.Model K)
    (heU : ∀a v,EU (automizerRepresentation U a v)=rho (fU a) (EU v))
    (hc : ⁅V,U⁆≤V⊓U) (hne : ⁅V,U⁆≠⊥) :
    IsOffender rho ((inducedAutomizer V U).map fV) := by
  apply image_offender_of_corank_comparison EV fV heV hc hne
  rcases le_total (subgroupCorank V (V⊓centralizer (U:Set G)))
    (subgroupCorank U (U⊓centralizer (V:Set G))) with hh|hh
  · exact hh
  · have hc' : ⁅U,V⁆≤U⊓V := by simpa only [Subgroup.commutator_comm,inf_comm] using hc
    have hn' : ⁅U,V⁆≠⊥ := by simpa only [Subgroup.commutator_comm] using hne
    have ho := image_offender_of_corank_comparison EU fU heU hc' hn' hh
    have hr : rank ((inducedAutomizer U V).map fU)=3 :=
      Atlas.G2.NaturalOffenders.natural_offender_rank (F:=K) (n:=1) (by norm_num) (by decide) _
        ((Atlas.G2.NaturalOffenders.natural_offender_iff _).mpr ho)
    have hd : fixedCodim rho ((inducedAutomizer U V).map fU)=3 := by
      have h := Atlas.G2.NaturalOffenders.natural_offender_fixedCodim (F:=K) (n:=1)
        (by norm_num) (by decide) _ ((Atlas.G2.NaturalOffenders.natural_offender_iff _).mpr ho)
      rw [Atlas.G2.NaturalOffenders.natural_fixedCodim_eq] at h
      exact h
    have hfU : Function.Injective fU := by
      intro a b hab
      apply automizerRepresentation_injective U
      apply LinearMap.ext
      intro v
      apply EU.injective
      rw [heU,heU,hab]
    have hVN : V≤normalizer (U:Set G) := le_normalizer_iff_commutator_le_right.mpr (hc.trans inf_le_right)
    rw [rank_map_injective fU hfU,rank_inducedAutomizer U V hVN] at hr
    rw [←fixedCodim_map_equivariant (automizerRepresentation U) rho fU EU heU,
      fixedCodim_inducedAutomizer U V hVN] at hd
    exact hr.trans hd.symm |>.le

theorem common_pair_point_of_two_natural_actions
    (EV : Additive V≃ₗ[K] W) (fV : Automizer V→*Atlas.G2.Model K)
    (heV : ∀a v,EV (automizerRepresentation V a v)=rho (fV a) (EV v))
    (EU : Additive U≃ₗ[K] W) (fU : Automizer U→*Atlas.G2.Model K)
    (heU : ∀a v,EU (automizerRepresentation U a v)=rho (fU a) (EU v))
    (hc : ⁅V,U⁆≤V⊓U) (hne : ⁅V,U⁆≠⊥)
    (hRV : (ambientSpace (V:=V) (V⊓U)).map EV.toLinearMap=target false)
    (hRU : (ambientSpace (V:=U) (V⊓U)).map EU.toLinearMap=target false) :
    zpowers (EV.symm firstVector).toMul.val=zpowers (EU.symm firstVector).toMul.val := by
  have hcard {A : Subgroup G} [IsElementaryAbelian 2 A]
      (E : Additive A≃ₗ[K]W) : Nat.card A=64 := by
    have hh := Nat.card_congr E.toEquiv
    change Nat.card (Additive A)=64
    simpa [W,K,Nat.card_fun,Nat.card_zmod,Nat.card_fin] using hh
  have hc' : ⁅U,V⁆≤U⊓V := by simpa only [Subgroup.commutator_comm,inf_comm] using hc
  have hn' : ⁅U,V⁆≠⊥ := by simpa only [Subgroup.commutator_comm] using hne
  have h₁ := pairHyperplane_point_of_marked_offender EV fV heV hc
    (image_offender_of_two_natural_actions EV fV heV EU fU heU hc hne) (hcard EU) hRV
  have h₂ := pairHyperplane_point_of_marked_offender EU fU heU hc'
    (image_offender_of_two_natural_actions EU fU heU EV fV heV hc' hn') (hcard EV)
    (by simpa only [inf_comm] using hRU)
  rw [←h₁,←h₂,inf_comm U V,Subgroup.commutator_comm]
end CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
