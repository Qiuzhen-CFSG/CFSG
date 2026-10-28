module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.PrimeActor
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.OddCharacteristic
public import Theory.GroupTheory.ElementarySylowQuinticAction
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms

/-!
# The original quintic actor on an ordinary central quotient

The original prime-five actor fully moves W = [V,O²(M ∩ G₁)]. Its
faithful action on the perfect central quotient preserves nontriviality.
Every quintic automorphism is inner when the model's outer group is a
two-group. Thus the moved elementary image is an actual subgroup of the
specified quotient, normalized by its original full Sylow, and has order
at least sixteen. The actual inner five-subgroup and its displacement
identity are retained for finer normalizer arguments. Neither an exchanged plane nor a rank assumption on an
unidentified model is used.

The Quintic extension applies this to the concrete sporadic bounds. The
remaining Ordinary22 geometry and exclusions stay with
qt-e-15122-ordinary-pre-exclusion, with final source-premise discharge by
qt-e-15122-pre-exclusion-catalogue.
Source: Aschbacher--Smith 15.1.19(7), 15.1.21(ii), 15.1.22,
printed pp.1094,1098--1100, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The original quintic actor and its large displacement descend to the same
centerless quotient. The original Sylow normalizes the displacement. -/
theorem PreExclusionSource.quintic_normal_elementary_pair_quotient
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {X : Type*} [Group X] (e : (d.L ⧸ pCore 2 d.L) ≃* X)
    (hz : center X = ⊥) (ho : IsPGroup 2 (MulAut.Outer X)) :
    ∃ (P : Sylow 2 X) (E D : Subgroup X), IsElementaryAbelian 2 E ∧
      E ≤ (P : Subgroup X) ∧ (P : Subgroup X) ≤ normalizer (E : Set X) ∧
      IsPGroup 5 D ∧ ⁅E,D⁆ = E ∧ E ≠ ⊥ ∧ 16 ≤ Nat.card E := by
  let := h.elementary
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  let : Finite X := Finite.of_equiv (d.L ⧸ pCore 2 d.L) e.toEquiv
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center d.L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk',
      ←(s.ordinary hL).center_eq]
  let c : PerfectCentralCovering.Cover d.L X := ⟨q,hq,inferInstance,hker.le⟩
  let C := M ⊓ d.G1
  let R := (pResidual 2 C).map C.subtype
  let W := ⁅V,R⁆
  let N := normalizer (d.L : Set G)
  let f := (c.autMap hker).comp d.L.normalizerMonoidHom
  obtain ⟨Y,hY,hYR⟩ := s.rankOne_prime_actor (h := h) hG hM hJ
  have hRC : R ≤ C := map_subtype_le _
  have hRN : R ≤ N := le_sup_left.trans s.residual_normalizes
  have hYN : Y ≤ N := hYR.trans hRN
  have hWN : W ≤ N := le_sup_right.trans s.residual_normalizes
  have hRV : R ≤ normalizer (V : Set G) := (hRC.trans inf_le_left).trans h.normalized
  have hWV : W ≤ V := le_normalizer_iff_commutator_le_left.mp hRV
  have hVC : V ≤ C := le_inf h.le_selected
    (V.le_centralizer.trans (centralizer_le (d.Z1_le_fixed.trans inf_le_left)))
  have hWC : W ≤ C := hWV.trans hVC
  have hCW : C ≤ normalizer (W : Set G) := by
    have hnV : (V.subgroupOf C).Normal :=
      normal_subgroupOf_of_le_normalizer (inf_le_left.trans h.normalized)
    have hR : R.subgroupOf C = pResidual 2 C := by
      apply map_injective C.subtype_injective
      rw [map_subgroupOf_eq_of_le hRC]
    have he : W.subgroupOf C = ⁅V.subgroupOf C,pResidual 2 C⁆ := by
      change ⁅V,R⁆.subgroupOf C = _
      rw [SubgroupTransport.subgroupOf_commutator V R hVC hRC,hR]
    have hn : (W.subgroupOf C).Normal := he ▸ inferInstance
    exact (normal_subgroupOf_iff_le_normalizer hWC).mp hn
  let A := (W.subgroupOf N).map f
  let B := (Y.subgroupOf N).map f
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
  let : IsElementaryAbelian 2 (W.subgroupOf N) := IsElementaryAbelian.subgroupOf hWN
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map f
  have hB : IsPGroup 5 B :=
    (hY.prime_group.of_equiv (subgroupOfEquivOfLe hYN).symm).map f
  obtain ⟨P,hP⟩ := s.component_sylow
  let Q := P.mapSurjective (f := q) hq
  have hPC : ((P : Subgroup d.L).map d.L.subtype) ≤ C := by
    rw [hP]
    exact le_inf ((inf_le_left.trans d.S_le_T).trans hM.1.2)
      (inf_le_right.trans d.L_component.1)
  have hPA : (Q : Subgroup X).map (MulAut.conj : X →* MulAut X) ≤
      normalizer (A : Set (MulAut X)) := by
    rintro _ ⟨x,⟨l,hl,rfl⟩,rfl⟩
    let xn : N := ⟨l,d.L.le_normalizer l.property⟩
    have hxW : xn ∈ normalizer (W.subgroupOf N : Set N) := by
      rw [←subgroupOf_normalizer_eq hWN]
      exact hCW (hPC (mem_map_of_mem d.L.subtype hl))
    have hfx : f xn = MulAut.conj (q l) := by
      ext z
      obtain ⟨w,rfl⟩ := hq z
      change c.autMap hker (d.L.normalizerMonoidHom xn) (q w) = _
      rw [c.autMap_apply hker]
      change q (l*w*l⁻¹) = _
      simp only [map_mul,map_inv,MulAut.conj_apply]
    rw [←hfx]
    exact (W.subgroupOf N).le_normalizer_map f (mem_map_of_mem f hxW)
  have hAB : ⁅A,B⁆ = A := by
    dsimp only [A,B]
    rw [←map_commutator,←SubgroupTransport.subgroupOf_commutator W Y hWN hYN,hY.moves]
  have hAne : A ≠ ⊥ := by
    intro he
    have hcW : W ≤ centralizer (d.L : Set G) := by
      intro w hw l hl
      have hh : f ⟨w,hWN hw⟩ = 1 := mem_bot.mp (he ▸ mem_map_of_mem f hw)
      have hh' : d.L.normalizerMonoidHom ⟨w,hWN hw⟩ = 1 :=
        (c.autMap_injective hker) (hh.trans (map_one (c.autMap hker)).symm)
      have ha := congrArg Subtype.val (DFunLike.congr_fun hh' (⟨l,hl⟩ : d.L))
      change w*l*w⁻¹=l at ha
      exact (mul_inv_eq_iff_eq_mul.mp ha).symm
    exact s.moving_noncentral (by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hcW)
  obtain ⟨E,D,hE,hEP,hPE,hD,hED,hEn,hcE⟩ :=
    exists_normal_elementary_pair_of_quintic_movement hz ho Q A B hB hPA hAB hAne
  exact ⟨Q,E,D,hE,hEP,hPE,hD,hED,hEn,hcE⟩

/-- The original quintic actor produces a large normal elementary subgroup in
any actual centerless quotient with two-group outer automorphisms. -/
theorem PreExclusionSource.quintic_normal_elementary_quotient
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {X : Type*} [Group X] (e : (d.L ⧸ pCore 2 d.L) ≃* X)
    (hz : center X = ⊥) (ho : IsPGroup 2 (MulAut.Outer X)) :
    ∃ (P : Sylow 2 X) (E : Subgroup X), IsElementaryAbelian 2 E ∧
      E ≤ (P : Subgroup X) ∧ (P : Subgroup X) ≤ normalizer (E : Set X) ∧
      16 ≤ Nat.card E := by
  obtain ⟨P,E,D,hE,hEP,hPE,_,_,_,hc⟩ :=
    s.quintic_normal_elementary_pair_quotient (h := h) hG hM hJ hL e hz ho
  exact ⟨P,E,hE,hEP,hPE,hc⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
