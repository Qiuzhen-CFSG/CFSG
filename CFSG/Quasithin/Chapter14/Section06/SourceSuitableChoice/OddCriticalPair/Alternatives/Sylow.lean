module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Normalizer.InH
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.NoncentralPoint
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.CubicFactorSylowPlacement

/-!
# Constructing the Sylow placement for the rank-eight contradiction

The actual nontrivial starred two-subgroup in the first cubic factor generates
an index-three subgroup of H₀ together with H₂. Its preimage therefore contains
a Sylow subgroup of H₀. Disjoint moved summands make H₂ fix the first support
modulo Z; the elementary critical span fixes its own central point. Thus this
constructed Sylow fixes the critical point modulo Z. Relative Sylow conjugacy
and the proved noncentral-point obstruction give the original contradiction.

The fitting containment and the normalizer equality from 14.6.14--16 remain
explicit. The earlier exchanged-factor setup is supplied by 14.6.12. This
module does not assert the critical-pair alternatives of 14.6.13.

Source: Aschbacher--Smith 14.6.17, printed pp.1035--1036.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open OddNormalizer Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable {H U Z : Subgroup G} [IsElementaryAbelian 2 U]

omit [Finite G] in
theorem second_factor_fixes_first_support
    (a : LocalQuotientAction H U Z) (T : Subgroup G)
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a T p H0 H1 H2) :
    ⁅firstSupport a H1,H2⁆ ≤ Z := by
  let W1 := subspaceCommutator a.representation ⊤ (actorImage H H1)
  let W2 := subspaceCommutator a.representation ⊤ (actorImage H H2)
  have hn : actorImage H H2 ≤ subspaceStabilizer a.representation W1 := by
    apply subspaceCommutator_invariant_normalizer a.representation
      (le_subspaceStabilizer _ ⊤ (by intros; trivial))
    exact actorImage_normalizes H1 H2 (d.first_le.trans d.zero_le)
      (d.second_le.trans d.normalizes_first)
  have hf : W1 ≤ fixedSpace a.representation (actorImage H H2) := by
    intro v hv b
    apply sub_eq_zero.mp
    apply Submodule.disjoint_def.mp d.disjoint _
    · exact W1.sub_mem ((hn b.property v).mpr hv) hv
    · exact Submodule.subset_span ⟨b,b.property,v,Submodule.mem_top,rfl⟩
  rw [commutator_comm,commutator_le]
  intro b hb u hu
  have huU := supportPreimage_le a W1 hu
  let v := Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) ⟨u,huU⟩)
  let bH : H := ⟨b,d.zero_le (d.second_le hb)⟩
  have hv : v ∈ W1 := (mem_supportPreimage a W1 ⟨u,huU⟩).mp hu
  have hh := hf hv ⟨QuotientGroup.mk' (pCore 2 H) bH,mem_map_of_mem _ hb⟩
  change a.representation (QuotientGroup.mk' (pCore 2 H) bH) v = v at hh
  rw [a.conjugation] at hh
  have hc := QuotientGroup.eq_iff_div_mem.mp (congrArg Additive.toMul hh)
  change b * u * b⁻¹ / u ∈ Z at hc
  simpa only [div_eq_mul_inv,commutatorElement_def] using hc

omit [Finite G] in
private theorem actorImage_join (A B : Subgroup G) (hA : A ≤ H) (hB : B ≤ H) :
    actorImage H (A ⊔ B) = actorImage H A ⊔ actorImage H B := by
  unfold actorImage
  rw [subgroupOf_sup hA hB,Subgroup.map_sup]

/-- A nontrivial two-actor in the first cubic factor, together with the
second factor, has odd index in the original factor-preserving subgroup. -/
theorem critical_join_index
    (a : LocalQuotientAction H U Z) (T : Subgroup G)
    (H0 H1 H2 A : Subgroup G)
    (d : ExchangedFactorSetup a T 3 H0 H1 H2)
    (hAH : A ≤ H) (hp : IsPGroup 2 A)
    (hfirst : actorImage H A ≤ actorImage H H1)
    (hne : actorImage H A ≠ ⊥) :
    A ⊔ H2 ≤ H0 ∧ (A ⊔ H2).relIndex H0 = 3 := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hQ1 : q.ker ≤ H1.subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact d.core_le_first (mem_map_of_mem H.subtype hx)
  have hA1 : A ≤ H1 := by
    have hh := map_le_iff_le_comap.mp hfirst
    change A.subgroupOf H ≤ (H1.subgroupOf H |>.map q).comap q at hh
    rw [comap_map_eq_self hQ1] at hh
    intro x hx
    exact hh (show (⟨x,hAH hx⟩ : H) ∈ A.subgroupOf H from hx)
  have hE : A ⊔ H2 ≤ H0 := sup_le (hA1.trans d.first_le) d.second_le
  have hc : actorImage H H1 ≤ centralizer (actorImage H H2 : Set _) := by
    intro x hx y hy
    exact (d.actors_commute x hx y hy).symm
  have hcard1 : Nat.card (actorImage H H1) = 6 := by
    rw [Nat.card_congr d.first_model.some.toEquiv,DihedralGroup.nat_card]
  have hcard2 : Nat.card (actorImage H H2) = 6 := by
    rw [Nat.card_congr d.second_model.some.toEquiv,DihedralGroup.nat_card]
  have hi := cubic_factor_join_relIndex (actorImage H H1) (actorImage H H2)
    (actorImage H A) d.actors_disjoint hc hcard1 hcard2 hfirst
      (hp.comap_subtype.map q) hne
  have he0 : actorImage H H0 = actorImage H H1 ⊔ actorImage H H2 := by
    rw [← actorImage_join H1 H2 (d.first_le.trans d.zero_le)
      (d.second_le.trans d.zero_le),d.join_eq]
  rw [← he0, ← actorImage_join A H2 hAH (d.second_le.trans d.zero_le)] at hi
  have hQE : q.ker ≤ (A ⊔ H2).subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact (show H2 ≤ A ⊔ H2 from le_sup_right)
      (d.core_le_second (mem_map_of_mem H.subtype hx))
  have hQ0 : q.ker ≤ H0.subgroupOf H := hQE.trans (subgroupOf_mono H hE)
  change ((A ⊔ H2).subgroupOf H |>.map q).relIndex ((H0.subgroupOf H).map q) = 3 at hi
  rw [relIndex_map_map, sup_of_le_left hQE, sup_of_le_left hQ0,
    relIndex_subgroupOf d.zero_le] at hi
  exact ⟨hE,hi⟩

/-- The literal N_T(H₁), rather than an abstract quotient Sylow, is Sylow in H₀. -/
theorem exchanged_support_sylow
    (a : LocalQuotientAction H U Z) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (H1 : Set G)) H0 := by
  have he := exchanged_factor_normalizer_eq a T hTH p H0 H1 H2 d
  have hS : (T : Subgroup G) ⊓ normalizer (H1 : Set G) = (T : Subgroup G) ⊓ H0 := by
    rw [← he, ← inf_assoc, inf_of_le_left hTH]
  let : (H0.subgroupOf H).Normal := normal_of_index_eq_two d.index
  obtain ⟨P,hP⟩ := (T.subtype hTH).exists_subgroupOf_eq_of_normal (H0.subgroupOf H)
  let f := (subgroupOfEquivOfLe d.zero_le).toMonoidHom
  have hf : Function.Surjective f := (subgroupOfEquivOfLe d.zero_le).surjective
  refine ⟨P.mapSurjective hf,?_⟩
  change ((P : Subgroup (H0.subgroupOf H)).map f).map H0.subtype = _
  rw [hP,hS]
  ext x
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨hz,z.property⟩
  · intro hx
    exact ⟨⟨x,hx.2⟩,⟨⟨⟨x,d.zero_le hx.2⟩,hx.2⟩,hx.1,rfl⟩,rfl⟩

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (J : Subgroup G) (hJ : J ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))

include hG hempty hM hunique hmany hcard e hab hJ

/-- Original 14.6.17 excludes the rank-eight critical placement, conditionally
on the fitting containment and local normalizer supplied by 14.6.14--16.
Both relative Sylow subgroups and the fixed-point placement are constructed. -/
theorem source_critical_point_not_le_first_support
    (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (hF : residual J ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hN : Mc ⊓ normalizer
      (((T : Subgroup G) ⊓ normalizer (H1 : Set G) : Subgroup G) : Set G) =
        (T : Subgroup G))
    (g : G) (hout : g ∉ Mc)
    (hγJ : (conjugateSpanBy (localModule T M) J).map (MulAut.conj g).toMonoidHom ≤ J)
    (hfirst : actorImage J
      ((conjugateSpanBy (localModule T M) J).map (MulAut.conj g).toMonoidHom) ≤
        actorImage J H1)
    (hD : ((conjugateSpanBy (localModule T M) J).map (MulAut.conj g).toMonoidHom) ⊓
        J.pCoreIn 2 < (conjugateSpanBy (localModule T M) J).map (MulAut.conj g).toMonoidHom) :
    ¬ (centralInvolutions T).map (MulAut.conj g).toMonoidHom ≤ firstSupport a H1 := by
  let U := conjugateSpanBy (localModule T M) J
  let A := U.map (MulAut.conj g).toMonoidHom
  let Z := centralInvolutions T
  let W := firstSupport a H1
  let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
  let E := A ⊔ H2
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab J hJ
  have hp : IsPGroup 2 A :=
    (IsElementaryAbelian.isPGroup 2 U).map (MulAut.conj g).toMonoidHom
  have hne : actorImage J A ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he
    rw [QuotientGroup.ker_mk'] at hk
    apply hD.not_ge
    refine le_inf le_rfl ?_
    intro x hx
    exact mem_map_of_mem J.subtype (hk (show (⟨x,hγJ hx⟩ : J) ∈ A.subgroupOf J from hx))
  obtain ⟨hE0,hi⟩ := critical_join_index a (T : Subgroup G) H0 H1 H2 A d hγJ hp hfirst hne
  obtain ⟨P,hPE⟩ := exists_sylow_map_le_of_odd_relIndex E H0 hE0 (by rw [hi]; decide)
  let Q := (P : Subgroup H0).map H0.subtype
  have hQ : Chapter1.IsSylowIn 2 Q H0 := ⟨P,rfl⟩
  have hS := exchanged_support_sylow a T hJ.1.2 3 H0 H1 H2 d
  have h0W : H0 ≤ normalizer (W : Set G) := by
    apply supportPreimage_normalized a _ H0 d.zero_le
    apply subspaceCommutator_invariant_normalizer a.representation
      (le_subspaceStabilizer _ ⊤ (by intros; trivial))
    exact actorImage_normalizes H1 H0 (d.first_le.trans d.zero_le) d.normalizes_first
  obtain ⟨hWU,hZW,hKW,_hSW,hindex,hsep,hfree⟩ := source_exchanged_support_premises
    hG T hempty hM hunique hmany hcard e hab J hJ a 3 H0 H1 H2 d
  intro hpoint
  have hZγA : Z.map (MulAut.conj g).toMonoidHom ≤ A := map_mono a.kernel_le
  have hAZ : ⁅A,Z.map (MulAut.conj g).toMonoidHom⁆ ≤ Z := by
    have hc : A ≤ centralizer (A : Set G) :=
      le_centralizer_iff_isMulCommutative.mpr
        (IsElementaryAbelian.map (p := 2) (MulAut.conj g).toMonoidHom).toIsMulCommutative
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (hc.trans (centralizer_le hZγA))).le.trans bot_le
  have h2Z : ⁅H2,Z.map (MulAut.conj g).toMonoidHom⁆ ≤ Z := by
    rw [commutator_comm]
    exact (commutator_mono hpoint le_rfl).trans
      (second_factor_fixes_first_support a (T : Subgroup G) 3 H0 H1 H2 d)
  have hEZ : E ≤ normalizer (Z : Set G) :=
    (hE0.trans d.zero_le).trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  have hEc : ⁅E,Z.map (MulAut.conj g).toMonoidHom⁆ ≤ Z := by
    have he : E ≤ commutatorPreimage E (Z.map (MulAut.conj g).toMonoidHom) Z :=
      sup_le (le_commutatorPreimage le_sup_left hAZ) (le_commutatorPreimage le_sup_right h2Z)
    exact (commutator_mono he le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hEZ)
  have hfixed : ∀ w ∈ Z.map (MulAut.conj g).toMonoidHom, ∀ q ∈ Q, ⁅w,q⁆ ∈ Z := by
    intro w hw q hq
    have hh : ⁅Z.map (MulAut.conj g).toMonoidHom,E⁆ ≤ Z := by
      rwa [commutator_comm]
    exact hh (commutator_mem_commutator hw (hPE hq))
  exact source_critical_point_not_le_support_of_sylow
    hG T hempty hM hunique hmany hcard e hab J hJ
    (residual J) W S hF hWU hZW.le hKW inf_le_left hindex hN hsep hfree
    H0 Q d.zero_le h0W hS hQ g hout hfixed hpoint

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
