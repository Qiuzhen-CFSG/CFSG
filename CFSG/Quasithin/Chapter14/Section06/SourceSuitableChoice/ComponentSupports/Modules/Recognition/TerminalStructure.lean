module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.TerminalSupports
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.Factorization

/-!
# Complete terminal products, fixed supplement and suitable factorizations

The actual diagram action swaps the only two proper non-two-group
parabolics above the component Sylow. Since M contains T, its component
intersection is invariant and cannot be a parabolic. This gives M ∩ Mc=T
and the literal products M=LT and Mc=Mc∞T. Gaschütz supplies the fixed
supplement on every original U/Z coordinate section. The same constructed
suitable involution feeds both source residual factorizations at every IStar.

MixedSizeInput is the sole retained component-classification input, with
final instantiation in qt-e-suitable-existence. Original14.6.18 is hsolv,
owned by qt-e-14625-source. The factorization application retains its
original rank and core-index hypotheses. No local support, action, marking,
normalizer, decomposition or vector callback remains.

Source: Aschbacher--Smith14.6.9,14.6.20--24, pp.1025--1028,1037--1041.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement Pointwise
open Representation.BinaryOffender.Homogeneous Representation.OneCohomology
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Subgroup.NormalSylowQuotientAction
open Chapter13.Section08.CriticalGeometry.Reorientation
variable {G : Type*} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv

/-- The original intersection is Sylow: its component image is either a
two-group or one of the two parabolics, and the actual diagram swap excludes
the latter. Both original group products are retained. -/
theorem terminal_products_of_mixed_size
    (size : Chapter10.MixedZeroCore.MixedSizeInput G) :
    M ⊓ Mc = (T : Subgroup G) ∧
      (M : Set G) = (sourceResidual M Mc : Set G) * ((T : Subgroup G) : Set G) ∧
      (Mc : Set G) = ((solvableResidual Mc).map Mc.subtype : Set G) *
        ((T : Subgroup G) : Set G) := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  obtain ⟨_,K,hKM,hK,_⟩ := terminal_exists_component
    hG T hempty hM hunique hmany hcard e hab hsolv
  obtain ⟨⟨eK⟩,_,hn,hr,hgen,_,_⟩ := terminal_component_linear_three_of_mixed_size
    hG T hempty hM hunique hmany hcard e hab hsolv size K hKM hK
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hout.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKM).mp hn)
  let eP := eK.trans Matrix.PSL3Two.equiv
  let q := eP.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eP.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨P,hP,J,L,hJ,hL,hne,hi,hall,s,hsJ,hsL⟩ := source_normal_l3_parabolic_swap
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK hn eP
  let Pq := P.mapSurjective (f := q) hq
  let N := (M.subgroupOf K).map q
  have hPN : (Pq : Subgroup Matrix.PSL3Two.PSL) ≤ N := by
    apply map_mono
    rw [hP]
    exact fun x hx => hM.1.2 hx
  have hker : q.ker ≤ (P : Subgroup K) := by
    rw [MonoidHom.ker_comp_of_injective _ _ eP.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  have hNtop : N ≠ ⊤ := by
    intro hh
    have hnM : M.subgroupOf K = ⊤ := by
      have hc := congrArg (Subgroup.comap q) hh
      rwa [comap_map_eq,sup_eq_left.mpr (hker.trans (by rw [hP]; exact fun _ hx => hM.1.2 hx)),comap_top] at hc
    exact source_normal_component_not_le hG T hempty hM hunique hmany hcard e hab
      Mc hout K hKM hK hn (fun k hk => show (⟨k,hk⟩ : K) ∈ M.subgroupOf K from hnM ▸ mem_top _)
  let α := markedCoreAction 2 K eP ⟨s,hTK s.property⟩
  have hfix : N.map α.toMonoidHom = N := by
    have hle : N.map α.toMonoidHom ≤ N := by
      rintro _ ⟨y,⟨k,hk,rfl⟩,rfl⟩
      change α (eP (QuotientGroup.mk' (pCore 2 K) k)) ∈ N
      rw [markedCoreAction_mk]
      apply mem_map_of_mem q
      change (s:G)*k*(s:G)⁻¹ ∈ M
      exact M.mul_mem (M.mul_mem (hM.1.2 s.property) hk) (M.inv_mem (hM.1.2 s.property))
    exact eq_of_le_of_card_ge hle (card_map_of_injective α.injective).symm.le
  have hNP : N = (Pq : Subgroup Matrix.PSL3Two.PSL) := by
    by_cases hp : IsPGroup 2 N
    · exact Pq.is_maximal' hp hPN
    have hc := (Matrix.PSL3Two.exists_compatible_parabolic_marking
      (MulEquiv.refl _) Pq N hPN hNtop hp).1
    rcases (hall N hc).mp hPN with he | he
    · rw [he,show J.map α.toMonoidHom = L from hsJ] at hfix
      exact (hne hfix.symm).elim
    · rw [he,show L.map α.toMonoidHom = J from hsL] at hfix
      exact (hne hfix).elim
  have hMK : M.subgroupOf K = (T : Subgroup G).subgroupOf K := by
    have hh := congrArg (Subgroup.comap q) hNP
    change ((M.subgroupOf K).map q).comap q = ((P : Subgroup K).map q).comap q at hh
    rw [comap_map_eq,comap_map_eq,sup_eq_left.mpr hker,
      sup_eq_left.mpr (hker.trans (by rw [hP]; exact fun _ hx => hM.1.2 hx)),hP] at hh
    exact hh
  have hprod : (Mc : Set G) = (K : Set G) * ((T : Subgroup G) : Set G) := by
    rw [←hgen]
    exact coe_mul_of_right_le_normalizer_left K (T : Subgroup G) hTK
  have hinter : M ⊓ Mc = (T : Subgroup G) := by
    apply le_antisymm _ (le_inf hM.1.2 hout.1.2)
    intro x hx
    obtain ⟨k,hk,t,ht,rfl⟩ := show x ∈ (K : Set G)*((T : Subgroup G):Set G) from hprod ▸ hx.2
    have hkM : k ∈ M := by
      simpa only [mul_inv_cancel_right] using M.mul_mem hx.1 (M.inv_mem (hM.1.2 ht))
    have hkT : k ∈ (T : Subgroup G) := show (⟨k,hk⟩ : K) ∈ (T : Subgroup G).subgroupOf K from
      hMK ▸ (show (⟨k,hk⟩ : K) ∈ M.subgroupOf K from hkM)
    exact (T : Subgroup G).mul_mem hkT ht
  have hZ := plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨_,hnot,_,_⟩ := plane_ordering_and_overgroups hG T hempty hM hunique hmany hcard hZ
  obtain ⟨_,hnoncentral,_⟩ := plane_intersection_core_inputs hG T hempty hM.1 hunique hmany hZ hnot
  have hC : M ⊓ centralizer (localModule T M : Set G) ≤ (T : Subgroup G) := by
    rw [←hinter]
    exact le_inf inf_le_left (inf_le_right.trans (Chapter15.Section03.InitialSource.localModule_centralizer_le_partner T M hunique))
  have hm : M = sourceResidual M Mc ⊔ (T : Subgroup G) :=
    (decomposition_of_intersectionCore_not_centralizing M Mc (localModule T M)
      T hM.1.2 ⟨e⟩ hnoncentral).trans (sup_eq_left.mpr (hC.trans le_sup_right))
  refine ⟨hinter,?_,?_⟩
  · exact (congrArg (fun X : Subgroup G => (X : Set G)) hm).trans
      (coe_mul_of_right_le_normalizer_left _ _ (hM.1.2.trans
        ((normal_subgroupOf_iff_le_normalizer (sourceResidual_le M Mc)).mp (residualY_normal M Mc))))
  · rw [hr]
    exact hprod

/-- The original whole quotient is the full component support plus its
fixed part. The component and its supplement are constructed from the
catalogue; the section may be any coordinates on the literal U/Z. -/
theorem terminal_fixed_supplement_of_mixed_size
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (ρ : Representation (ZMod 2) Mc X)
    (c : BinaryConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) ρ) :
    c.imageSpace ⁅conjugateSpanBy (localModule T M) Mc,K⁆ ⊔ fixed ρ = ⊤ := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  obtain ⟨_,_,hn,_,hgen,_,_⟩ := terminal_component_linear_three_of_mixed_size
    hG T hempty hM hunique hmany hcard e hab hsolv size K hKM hK
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hout.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKM).mp hn)
  have hh := source_component_sum_sup_fixed hG T hempty hM hunique hmany hcard e hab
    ρ c (fun (_ : Unit) => K) (fun _ => hKM) (by
      intro x
      have hx : (x:G) ∈ (K : Set G)*((T : Subgroup G) : Set G) := by
        rw [←coe_mul_of_right_le_normalizer_left K (T : Subgroup G) hTK,hgen]
        exact x.property
      obtain ⟨k,hk,t,ht,heq⟩ := hx
      refine ⟨⟨k,hKM hk⟩,?_,⟨t,hout.1.2 ht⟩,ht,Subtype.ext heq⟩
      simpa only [iSup_const] using (show (⟨k,hKM hk⟩ : Mc) ∈ K.subgroupOf Mc from hk))
  simpa only [iSup_const] using hh

/-- The same constructed suitable involution feeds every original IStar
factorization; the earlier source rank bounds are retained literally. -/
theorem terminal_exists_suitable_factorizations_of_mixed_size
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (hcoreIndex : 4 < (Mc.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (Mc.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) Mc))) :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    ∃ u : G, u ^ 2 = 1 ∧ u ≠ 1 ∧ Suitable h Mc u ∧
      ∀ I : Subgroup G, I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
        ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M) →
        let L := sourceResidual M Mc
        let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
        (L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
          (L ⊔ (T : Subgroup G) : Subgroup G) =
            (R : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
              ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) := by
  obtain ⟨K,_,_,_,_,_,_,_,_,j,A,B,_,_,_,_,_,_,_,_,_,u,_,hu2,hune,_,_,_,hu⟩ :=
    terminal_exists_full_supports_suitable_of_mixed_size
      hG T hempty hM hunique hmany hcard e hab hsolv size
  refine ⟨u,hu2,hune,hu,?_⟩
  intro I hI
  exact source_factorizations hG T hempty hM hunique hmany hcard e hab Mc
    (terminal_outside hG T hempty hM hunique hmany hcard e) u
    hu.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2.1 hu.2.2.2.2.2 hu.2.1 hcoreIndex hrank I hI

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
