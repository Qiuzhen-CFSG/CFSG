module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SmallAlternating
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.G2Geometry
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.CentralSylow
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.AlternatingSix
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowFixedLine
import all CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.G2Geometry
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.SourceGeometry.Source

/-!
# The ordinary A₆ faithful omega-center and seed centralizer

The natural six-letter module has a unique Sylow-fixed line. A block
automorphism fixing its Sylow modulo the center is inner by a vector
on that line, so the faithful normalizer omega-center has order at most
two. The original central seed makes its order exactly two. Its nontrivial
automorphism fixes a maximal point parabolic modulo the center; the proved
source lifting theorem removes that central error. Thus the literal M_L
is the maximal centralizer of the original central-involution seed.

The whole ordinary block is an explicit hypothesis here. In particular,
this geometry does not supply the unfinished A₆ whole-core reconstruction.
The full central attachment in U(L) and either original source prime are
retained. The internal faithful-action proofs reuse hidden bodies from
AutomorphismAction, G2Geometry and SourceGeometry.Source without changing
their public boundaries.

Source: Aschbacher--Smith 15.1.20(2b), 15.1.22(**),(2), printed
pp.1094--1099; A.1.39 and the six-letter natural geometry of B.3.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open CFSG.Quasithin ChapterC Representation Representation.BinaryOffender
open BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.SixGeometry

private theorem natural_fixed_card (P : Sylow 2 (alternatingGroup (Fin 6))) :
    Nat.card (fixedSpace ((naturalRepresentation (Fin 6)).comp
      (alternatingGroup (Fin 6)).subtype) (P : Subgroup _)) ≤ 2 := by
  let W := fixedSpace ((naturalRepresentation (Fin 6)).comp
      (alternatingGroup (Fin 6)).subtype) (P : Subgroup _)
  obtain ⟨g,hg⟩ := fixed_vectors_span_eq (alternatingGroup (Fin 6)) le_rfl P
  have hW : W ≤ move g canonicalLine := by
    intro w hw
    by_cases h0 : w = 0
    · rw [h0]; exact Submodule.zero_mem _
    · have he := hg w h0 (by rintro _ ⟨x,hx,rfl⟩; exact hw ⟨x,hx⟩)
      rw [←he]
      exact Submodule.subset_span (by simp)
  have hcard : Nat.card (move g canonicalLine) = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_eq_fintype_card,ZMod.card,
      move_finrank,canonicalLine_finrank,pow_one]
  exact (Nat.card_le_card_of_injective (Submodule.inclusion hW)
    (Submodule.inclusion_injective hW)).trans hcard.le

private theorem six_sylow_fixers
    {A : Type*} [Group A] [Finite A] (hb : IsAlternatingBlock A 6)
    (P : Sylow 2 A) (B : Subgroup (MulAut A))
    (hB : ∀ a ∈ B, ∀ x ∈ P, a x * x⁻¹ ∈ center A) : Nat.card B ≤ 2 := by
  obtain ⟨ρ,⟨m⟩,hρ⟩ := hb.2.2
  have hρi : Function.Injective ρ := by
    intro g j he
    apply Subtype.ext
    apply naturalRepresentation_injective (Fin 6) (by decide)
    apply LinearMap.ext
    intro w
    have hh := congrArg (fun k : MulAut (Multiplicative (natural (Fin 6))) =>
      (k (Multiplicative.ofAdd w)).toAdd) he
    simp only [hρ] at hh
    exact hh
  have hk : IsPGroup 2 m.actor.ker := by
    rw [BlockModuleModel.actor,MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,
      QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect A := hb.2.1.twoPerfect.isPerfect_of_surjective_pGroup_kernel
    m.actor m.actor_surjective hk
  let Q := P.mapSurjective m.actor_surjective
  let W := {w : Multiplicative (natural (Fin 6)) // ∀ x ∈ P, ρ (m.actor x) w = w}
  let f : W → fixedSpace ((naturalRepresentation (Fin 6)).comp
      (alternatingGroup (Fin 6)).subtype) (Q : Subgroup _) :=
    fun w => ⟨w.val.toAdd,by
      rintro ⟨_,x,hx,rfl⟩
      exact (hρ _ _).symm.trans (congrArg Multiplicative.toAdd (w.property x hx))⟩
  have hfi : Function.Injective f := by
    intro x y hh
    have he : (f x).val = (f y).val := congrArg (fun z => z.val) hh
    change x.val.toAdd = y.val.toAdd at he
    exact Subtype.ext (show x.val = y.val from Multiplicative.toAdd.injective he)
  exact (hb.2.1.central_sylow_fixers_card_le m hρi P B hB).trans
    ((Nat.card_le_card_of_injective f hfi).trans (natural_fixed_card Q))

private theorem line_coatom (P : Sylow 2 (alternatingGroup (Fin 6)))
    (v : natural (Fin 6)) (hv : v ≠ 0)
    (hf : ∀ x ∈ P, naturalRepresentation (Fin 6) (x : Equiv.Perm (Fin 6)) v = v) :
    IsCoatom ((flagStabilizer (Submodule.span (ZMod 2) {v})).comap
      (alternatingGroup (Fin 6)).subtype) := by
  let A := alternatingGroup (Fin 6)
  have transport (g : A) (W : Submodule (ZMod 2) (natural (Fin 6))) :
      (flagStabilizer (move g W)).comap A.subtype =
        ((flagStabilizer W).comap A.subtype).map (MulAut.conj g).toMonoidHom := by
    rw [flagStabilizer_move]
    ext x
    simp only [mem_comap,mem_map_equiv]
    rfl
  have hstd : IsCoatom ((flagStabilizer canonicalLine).comap A.subtype) := by
    let g : A := ⟨flagRelabel,flagRelabel_even⟩
    have he : (flagStabilizer canonicalLine).comap A.subtype =
        Theory.SpecificGroups.SymmetricSix.a6DuadStabilizer.map (MulAut.conj g).toMonoidHom := by
      rw [flagStabilizer_line,←flagRelabel_duad]
      ext x
      simp only [mem_comap,mem_map_equiv]
      rfl
    rw [he]
    exact ((MulAut.conj g).mapSubgroup.isCoatom_iff _).mpr
      Theory.SpecificGroups.SymmetricSix.a6DuadStabilizer_isCoatom
  obtain ⟨g,hg⟩ := fixed_vectors_span_eq A le_rfl P
  rw [hg v hv (by rintro _ ⟨x,hx,rfl⟩; exact hf x hx),transport]
  exact ((MulAut.conj g).mapSubgroup.isCoatom_iff _).mpr hstd

private theorem six_fixer_parabolic
    {A : Type*} [Group A] [Finite A] (hb : IsAlternatingBlock A 6)
    (P : Sylow 2 A) (a : MulAut A) (ha : a ≠ 1)
    (hP : ∀ x ∈ P, a x * x⁻¹ ∈ center A) :
    ∃ J : Subgroup A, IsCoatom J ∧ ∀ x ∈ J, a x * x⁻¹ ∈ center A := by
  obtain ⟨ρ,⟨m⟩,hρ⟩ := hb.2.2
  have hρi : Function.Injective ρ := by
    intro g j he
    apply Subtype.ext
    apply naturalRepresentation_injective (Fin 6) (by decide)
    apply LinearMap.ext
    intro w
    have hh := congrArg (fun k : MulAut (Multiplicative (natural (Fin 6))) =>
      (k (Multiplicative.ofAdd w)).toAdd) he
    simp only [hρ] at hh
    exact hh
  have hk : IsPGroup 2 m.actor.ker := by
    rw [BlockModuleModel.actor,MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,
      QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect A := hb.2.1.twoPerfect.isPerfect_of_surjective_pGroup_kernel
    m.actor m.actor_surjective hk
  obtain ⟨u,hu,hfix⟩ := hb.2.1.automorphism_eq_conj_of_central_sylow m hρi P a hP
  let w := m.moduleIso (QuotientGroup.mk' (blockFixed A) u)
  have hw : w ≠ 1 := by
    intro hh
    have hz : (u : A) ∈ center A := (QuotientGroup.eq_one_iff u).mp
      (m.moduleIso.map_eq_one_iff.mp hh)
    apply ha
    rw [hu]
    ext x
    change (u : A) * x * (u : A)⁻¹ = x
    rw [←mem_center_iff.mp hz x,mul_inv_cancel_right]
  have hw0 : w.toAdd ≠ 0 := fun hh => hw (Multiplicative.toAdd.injective hh)
  let Q := P.mapSurjective m.actor_surjective
  let C := (flagStabilizer (Submodule.span (ZMod 2) {w.toAdd})).comap
    (alternatingGroup (Fin 6)).subtype
  have hmax : IsCoatom C := line_coatom Q w.toAdd hw0 (by
    rintro _ ⟨x,hx,rfl⟩
    exact (hρ _ _).symm.trans (congrArg Multiplicative.toAdd (hfix x hx)))
  refine ⟨C.comap m.actor,isCoatom_comap_of_surjective m.actor_surjective hmax,?_⟩
  intro x hx
  have hmem : naturalRepresentation (Fin 6) (m.actor x).val w.toAdd ∈
      Submodule.span (ZMod 2) {w.toAdd} := by
    exact (hx w.toAdd).mpr (Submodule.subset_span (by simp))
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hc1 : c = 1 := by
    fin_cases c
    · change (0 : ZMod 2) • w.toAdd = _ at hc
      rw [zero_smul] at hc
      exact (hw0 (((naturalRepresentation (Fin 6)).apply_bijective _).injective
        (hc.symm.trans (map_zero _).symm))).elim
    · rfl
  have hf : ρ (m.actor x) w = w := by
    apply Multiplicative.toAdd.injective
    rw [hρ]
    rw [hc1,one_smul] at hc
    exact hc.symm
  have hh : QuotientGroup.mk' (blockFixed A) (blockConjugate A x u) =
      QuotientGroup.mk' (blockFixed A) u :=
    m.moduleIso.injective ((m.intertwining x u).trans hf)
  have hz : x * (u : A) * x⁻¹ * (u : A)⁻¹ ∈ center A := by
    have hh' := QuotientGroup.eq_iff_div_mem.mp hh
    simp only [div_eq_mul_inv] at hh'
    exact hh'
  have hz' := (center A).inv_mem hz
  rw [hu]
  simpa only [MulAut.conj_apply,mul_inv_rev,inv_inv,mul_assoc] using hz'
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.SixGeometry

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open SixGeometry
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The full original local family is normalized in the ordinary A₆ block row. -/
theorem localFamily_six_normalizes (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hb : IsAlternatingBlock K 6) :
    d.S ≤ normalizer (K : Set G) := by
  obtain ⟨ρ,⟨m⟩,_⟩ := hb.2.2
  apply d.localFamily_normalizes_of_oddRank hG h hK hq Nat.prime_three (by decide)
  rw [primeRank_equiv 3 m.quotientIso,
    GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 Nat.prime_three (by decide)]

/-- The faithful omega-center fixes the original Sylow modulo the center,
so the ordinary A₆ fixed-line calculation bounds its order. -/
theorem constrained_six_plusOmega_bound (d : CaseIComponentData T M Mc V)
    (hb : IsAlternatingBlock d.L 6) (hs : Chapter1.IsSylowIn 2 d.SL d.L) :
    Nat.card d.plusOmega ≤ 2 := by
  obtain ⟨P,hP⟩ := hs
  let B := d.plusOmega.map d.plusAction
  have hB : ∀ a ∈ B, ∀ y ∈ P, a y * y⁻¹ ∈ center d.L := by
    rintro a ⟨x,hx,rfl⟩ y hy
    have hyS : (y : G) ∈ d.S := (hP ▸ mem_map_of_mem d.L.subtype hy).1
    have hyN : (y : G) ∈ d.sylowNormalizer := ⟨hyS,d.L.le_normalizer y.property⟩
    have hyplus : d.componentPlusHom y ∈ d.plus d.sylowNormalizer :=
      mem_map_of_mem d.plusMap hyN
    have hc := (mem_omegaOneCenterAmbient_iff _ _).mp hx |>.2.2
    have he : d.componentPlusHom (d.plusAction x y * y⁻¹) = 1 := by
      rw [map_mul,map_inv,d.plusAction_component,←hc _ hyplus,mul_inv_cancel_right,mul_inv_cancel]
    have hh : d.plusAction x y * y⁻¹ ∈ d.componentPlusHom.ker := he
    rwa [d.componentPlusHom_ker] at hh
  have hh := six_sylow_fixers hb P B hB
  rwa [card_map_of_injective d.plusAction_injective] at hh


/-- The actual original seed makes the faithful omega-center nontrivial. -/
theorem PreExclusionSource.constrained_six_plusOmega_card
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hb : IsAlternatingBlock d.L 6) : Nat.card d.plusOmega = 2 := by
  have hn := d.localFamily_six_normalizes hG h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple hb
  have hZ1T := d.marked_le_sylow h hTM
  have hZS : centralInvolutions T ≤ d.S := fun z hz =>
    ⟨centralInvolutions_le_sylow T hz,
      centralizer_le hZ1T (centralInvolutions_le_centralizer_sylow T hz)⟩
  have hZne := d.central_seed_plus_ne_bot hu hZ1T (hZS.trans hn)
  have hne : d.plusOmega ≠ ⊥ := by
    intro he
    exact hZne (bot_unique (he ▸ d.central_seed_plus_le_omega hZ1T (hZS.trans hn)))
  have hlo := (one_lt_card_iff_ne_bot _).mpr hne
  have hhi := d.constrained_six_plusOmega_bound hb s.component_sylow
  omega

/-- The marked intersection is the maximal centralizer of the original seed. -/
theorem PreExclusionSource.constrained_six_centralizing
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    (hb : IsAlternatingBlock d.L 6) :
    d.ML = d.L ⊓ centralizer (centralInvolutions T : Set G) ∧
      IsCoatom (d.ML.subgroupOf d.L) := by
  have hc := s.constrained_six_plusOmega_card (h := h) hG hTM hu hb
  obtain ⟨w,hw,hunique⟩ := (Nat.card_eq_two_iff' (1 : d.plusOmega)).mp hc
  have hw' : (w : d.ComponentPlus) ≠ 1 := fun hh => hw (Subtype.ext hh)
  have ha : d.plusAction w ≠ 1 := fun hh => hw'
    (d.plusAction_injective (hh.trans (map_one d.plusAction).symm))
  obtain ⟨P,hP⟩ := s.component_sylow
  have hfix : ∀ x ∈ P, d.plusAction w x * x⁻¹ ∈ center d.L := by
    intro x hx
    have hxS : (x : G) ∈ d.S := (hP ▸ mem_map_of_mem d.L.subtype hx).1
    have hxplus : d.componentPlusHom x ∈ d.plus d.sylowNormalizer :=
      mem_map_of_mem d.plusMap ⟨hxS,d.L.le_normalizer x.property⟩
    have hc := (mem_omegaOneCenterAmbient_iff _ _).mp w.property |>.2.2
    have he : d.componentPlusHom (d.plusAction w x * x⁻¹) = 1 := by
      rw [map_mul,map_inv,d.plusAction_component,←hc _ hxplus,mul_inv_cancel_right,mul_inv_cancel]
    have hh : d.plusAction w x * x⁻¹ ∈ d.componentPlusHom.ker := he
    rwa [d.componentPlusHom_ker] at hh
  obtain ⟨J,hJmax,hJfix⟩ := six_fixer_parabolic hb P _ ha hfix
  have hJC : J ≤ (centralizer (centralInvolutions T : Set G)).comap d.L.subtype := by
    intro x hx
    apply s.source_plus_centralizer_lifts (h := h) hfull hTM
    intro z hz
    have hz' : z ∈ d.plusOmega :=
      (s.source_central_seed_plus (h := h) hfull hTM hu hc) ▸ hz
    by_cases hz1 : z = 1
    · rw [hz1,one_mul,mul_one]
    · have he : (⟨z,hz'⟩ : d.plusOmega) = w :=
        hunique _ (fun he => hz1 (congrArg Subtype.val he))
      have hzW : z = w := congrArg Subtype.val he
      rw [hzW]
      have hh : d.componentPlusHom (d.plusAction w x * x⁻¹) = 1 := by
        change d.plusAction w x * x⁻¹ ∈ d.componentPlusHom.ker
        rw [d.componentPlusHom_ker]
        exact hJfix x hx
      rw [map_mul,map_inv,mul_inv_eq_one] at hh
      rw [d.plusAction_component] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
  have hloc := s.local_intersections (h := h) hG hu hTM
  have hnot : d.ML.subgroupOf d.L ≠ ⊤ := by
    intro he
    apply hloc.2.2.1.ne
    have hh := congrArg (Subgroup.map d.L.subtype) he
    rw [map_subgroupOf_eq_of_le (show d.ML ≤ d.L from inf_le_right),
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hJM : J ≤ d.ML.subgroupOf d.L := fun x hx =>
    hloc.2.2.2.2.2 ⟨x.property,hJC hx⟩
  have he : d.ML.subgroupOf d.L = J := (hJmax.le_iff_eq hnot).mp hJM
  refine ⟨le_antisymm ?_ hloc.2.2.2.2.2,he ▸ hJmax⟩
  intro x hx
  exact ⟨hx.2,hJC (he ▸ (show (⟨x,hx.2⟩ : d.L) ∈ d.ML.subgroupOf d.L from hx))⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
