module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalNormalJankoField
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryModule
public import Theory.SpecificGroups.SL2.OddFixedVectors

/-!
# The original normal J₁ container moves the Sylow omega-center

The source seven-subgroup has order seven and the original left degree is
multiple of three. If the containing component centralized omega, the
original input would supply a noncentral chosen constituent with zero fixed
space. A moved constituent would force degree two, so it is invariant.
The actual natural model has no nonzero seven-fixed vector. The Hermitian
model has half-degree divisible by three, whereas a seven-element fixing
a nonzero Sylow-fixed vector would require seven to divide 2^s+1.
Thus both actual module alternatives contradict centralization.

The original W and full Sylow are retained. Neither invariant constituents
nor module coordinates are assumed; both are derived from the original input.
Source: Aschbacher--Smith 5.1.13, printed p.637 (`refs/quasithin.pdf`).
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Matrix
open CFSG.Quasithin.Chapter12.Section02
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Representation.OrthogonalFourMinus
variable {G : Type*} [Group G] [Finite G]
local instance (s : ℕ) : Algebra (ZMod 2) (FiniteModel.fixedField s) := ZMod.algebra _ 2
local instance (s : ℕ) [NeZero s] : Module (ZMod 2) (FiniteModel.Space s) :=
  Module.compHom (FiniteModel.Space s) (algebraMap (ZMod 2) (FiniteModel.fixedField s))

variable {L U : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem natural_seven_fixed_eq_one (h : IsNaturalModule L U n)
    {d : G} (hdL : d ∈ L) (hd : orderOf d = 7)
    {v : G} (hv : v ∈ U) (hfix : d * v * d⁻¹ = v) : v = 1 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := h
  let q : L →* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let dL : L := ⟨d,hdL⟩
  have hdLorder : orderOf dL = 7 := (Subgroup.orderOf_mk d hdL).trans hd
  have hqne : q dL ≠ 1 := by
    intro hq
    have hm : QuotientGroup.mk' (pCore 2 L) dL = 1 :=
      e.injective (hq.trans (map_one e).symm)
    have hdcore : dL ∈ pCore 2 L := (QuotientGroup.eq_one_iff dL).mp hm
    have hc := (pCore_isPGroup (p := 2) (G := L)).orderOf_coprime
      (by decide : Nat.Coprime 2 7) (⟨dL,hdcore⟩ : pCore 2 L)
    rw [Subgroup.orderOf_mk, hdLorder] at hc
    norm_num at hc
  have hqorder : orderOf (q dL) = 7 := orderOf_eq_prime
    (by rw [← map_pow, ← hdLorder, pow_orderOf_eq_one, map_one]) hqne
  have hvfix : toLin' (q dL) (f ⟨v,hv⟩).toAdd = (f ⟨v,hv⟩).toAdd := by
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply U.subtype_injective
    change (f.symm (Multiplicative.ofAdd (toLin' (q dL) (f ⟨v,hv⟩).toAdd)) : G) =
      (f.symm (f ⟨v,hv⟩) : G)
    rw [f.symm_apply_apply]
    exact (hf dL ⟨v,hv⟩).trans hfix
  have hz := Matrix.SL2.odd_power_fixed_eq_zero (q dL) 7 (by decide)
    (by rw [←hqorder,pow_orderOf_eq_one]) hqne (f ⟨v,hv⟩).toAdd hvfix
  have hvone : f ⟨v,hv⟩ = 1 := Multiplicative.toAdd.injective hz
  exact congrArg (fun x : U => (x : G))
    (f.injective (hvone.trans (map_one f).symm))

private theorem not_natural_of_seven_centralizes_omega
    {T : Sylow 2 G} {L U D : Subgroup G} {m : ℕ}
    (hU : IsElementaryAbelian 2 U) (hUT : U ≤ (T : Subgroup G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G)) (hU0 : U ≠ ⊥)
    (hDL : D ≤ L) (hDc : Nat.card D = 7) (hDC : D ≤ omegaCentralizer T) :
    ¬ IsNaturalModule L U m := by
  intro hn
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hU0 hUT hTU)
  have hzU : (z : G) ∈ U := z.property.1
  have hzZ : (z : G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    let := hU
    exact ⟨hUT hzU,elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) hzU,
      z.property.2.2⟩
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := D) 7 (by rw [hDc])
  have hc : (a : G) * (z : G) = (z : G) * (a : G) :=
    ((hDC a.property) z hzZ).symm
  have hz := natural_seven_fixed_eq_one hn (hDL a.property)
    ((orderOf_injective D.subtype D.subtype_injective a).trans ha) hzU
    (by rw [hc,mul_inv_cancel_right])
  exact hz1 (Subtype.ext hz)

private theorem hermitian_seven_fixed_divides
    {T : Sylow 2 G} {L U D : Subgroup G} (s : ℕ) [NeZero s]
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hU : IsElementaryAbelian 2 U) (hUT : U ≤ (T : Subgroup G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G)) (hU0 : U ≠ ⊥)
    (hDB : D ≤ localBorel T L) (hDc : Nat.card D = 7)
    (hDC : D ≤ omegaCentralizer T)
    (hm : IsConjugationModel L U (Representation.SL2.BinarySmall.hermitian s)) :
    7 ∣ 2^s+1 := by
  obtain ⟨e,f,hf⟩ := hm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  let S := P.mapSurjective hq
  have hfixed (l : L) (u : U) :
      Representation.SL2.BinarySmall.hermitian s (q l) (f u).toAdd = (f u).toAdd ↔
        (l : G)*(u : G)*(l : G)⁻¹ = (u : G) := by
    constructor
    · intro he
      have hh := hf l u
      change (f.symm (Multiplicative.ofAdd
        (Representation.SL2.BinarySmall.hermitian s (q l) (f u).toAdd)) : G) = _ at hh
      rw [he] at hh
      change (f.symm (f u) : G) = _ at hh
      rw [f.symm_apply_apply] at hh
      exact hh.symm
    · intro he
      apply Multiplicative.ofAdd.injective
      apply f.symm.injective
      apply U.subtype_injective
      change (f.symm (Multiplicative.ofAdd
        (Representation.SL2.BinarySmall.hermitian s (q l) (f u).toAdd)) : G) = (f.symm (f u) : G)
      rw [f.symm_apply_apply]
      exact (hf l u).trans he
  have hnorm (l : L) (hl : (l : G) ∈ localBorel T L) :
      q l ∈ normalizer (S : Set SL(2,FiniteModel.Field s)) := by
    have hN : l ∈ normalizer (P : Set L) := by
      have hh : (l : G) ∈ (normalizer ((T : Subgroup G).subgroupOf L : Set L)).map L.subtype := by
        rwa [←localBorel_eq_map]
      have hh' := (mem_map_iff_mem L.subtype_injective).mp hh
      change l ∈ normalizer ((P : Subgroup L) : Set L)
      rw [hP]
      exact hh'
    exact (Subgroup.le_normalizer_map (H := (P : Subgroup L)) q) (mem_map_of_mem q hN)
  have hSylow (u : U) (hu : (u : G) ∈ omegaOneCenterAmbient (T : Subgroup G)) :
      (f u).toAdd ∈ Representation.BinaryOffender.fixedSpace
        (Representation.SL2.BinarySmall.hermitian s) S := by
    intro g
    obtain ⟨l,hl,he⟩ := g.property
    change Representation.SL2.BinarySmall.hermitian s g.val (f u).toAdd = _
    rw [←he]
    apply (hfixed l u).mpr
    have hlT : (l : G) ∈ (T : Subgroup G) := by
      change l ∈ (P : Subgroup L) at hl
      rwa [hP] at hl
    have hc := ((mem_omegaOneCenterAmbient_iff _ _).mp hu).2.2 l hlT
    rw [hc,mul_inv_cancel_right]
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hU0 hUT hTU)
  have hzU : (z : G) ∈ U := z.property.1
  have hzZ : (z : G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    let := hU
    exact ⟨hUT hzU,elemPow_eq_one_of_isElementaryAbelian (p:=2) (z:G) hzU,z.property.2.2⟩
  let zU : U := ⟨z,hzU⟩
  have hz : (f zU).toAdd ≠ 0 := by
    intro he
    have h1 : zU = 1 := f.injective (he.trans f.map_one.symm)
    exact hz1 (Subtype.ext (congrArg (fun u : U => (u : G)) h1))
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := D) 7 (by rw [hDc])
  let aL : L := ⟨a,(hDB.trans inf_le_left) a.property⟩
  have hao : orderOf aL = 7 := (Subgroup.orderOf_coe aL).symm.trans
    ((orderOf_injective D.subtype D.subtype_injective a).trans ha)
  have hqne : q aL ≠ 1 := by
    intro he
    have haQ : aL ∈ pCore 2 L := (QuotientGroup.eq_one_iff _).mp
      (e.injective (he.trans e.map_one.symm))
    have hh := (pCore_isPGroup (p:=2) (G:=L)).orderOf_coprime
      (by decide : Nat.Coprime 2 7) (⟨aL,haQ⟩ : pCore 2 L)
    rw [Subgroup.orderOf_mk,hao] at hh
    norm_num at hh
  have hqo : orderOf (q aL) = 7 := orderOf_eq_prime
    (by rw [←map_pow,←hao,pow_orderOf_eq_one,map_one]) hqne
  have hfix := (SylowTorus.odd_normalizer_fixed_iff s S (q aL)
    (hnorm aL (hDB a.property)) (by rw [hqo]; decide)
    (f zU).toAdd (hSylow zU hzZ) hz).mp (by
      apply (hfixed aL zU).mpr
      have hc : (a:G)*(z:G) = (z:G)*(a:G) := ((hDC a.property) z hzZ).symm
      change (a:G)*(z:G)*(a:G)⁻¹ = (z:G)
      rw [hc,mul_inv_cancel_right])
  exact hqo ▸ orderOf_dvd_of_pow_eq_one hfix

/-- The same normal J₁ container necessarily moves the original omega-center.
The original input selects the needed constituent; no model or invariance
hypothesis is retained. -/
theorem normal_janko_moves_omega
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) [C.Normal] (hRC : (residual H).subgroupOf Y ≤ C)
    (eC : (C ⧸ pCore 2 C) ≃* Janko1.Model) :
    ¬ C.map Y.subtype ≤ omegaCentralizer T := by
  intro hCC
  obtain ⟨_,hn,hseven,hcard,_,_⟩ := normal_janko_original_seven h hH hgen c hY hescape C hRC eC
  let D := ⁅A ⊓ Y,B⁆
  have hDA : D ≤ A := by
    change ⁅A ⊓ Y,B⁆ ≤ A
    rw [hseven]
    exact inf_le_left
  have hDC : D ≤ omegaCentralizer T := by
    change ⁅A ⊓ Y,B⁆ ≤ omegaCentralizer T
    rw [hseven]
    exact inf_le_right.trans hCC
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hRC' : residual H ≤ C.map Y.subtype := by
    rw [←map_subgroupOf_eq_of_le hRY]
    exact map_mono hRC
  have hHC : H ≤ omegaCentralizer T :=
    (residual_le_omegaCentralizer_iff hH.1.1.2).mp (hRC'.trans hCC)
  obtain ⟨V,⟨a⟩⟩ := h.original_section1221.exists_chosen_of_normalizes h.sylow_normalizes
  have hz := h.centralOmega_disjoint_of_outside_centralizes hH hHC
  have hw : RankOneModule.wholeReduced T L ⊓ centralizer (L : Set G) = ⊥ :=
    Subgroup.inf_centralizer_eq_bot_of_omega_disjoint T L _
      RankOneModule.wholeReduced_mem.2.1 RankOneModule.wholeReduced_le_sylow
      (le_sup_right.trans RankOneModule.wholeReduced_normalized) h.sylow_normalizes hz
  have hc : V ⊓ centralizer (L : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ a.le_reduced).trans_eq hw)
  have hv : a.sourceOrbit = V := by
    by_contra he
    have he2 := a.localCartan_degree_two_of_moved_seed h hc
      (lt_of_le_of_ne (le_componentOrbit V T) (fun hh => he (a.sourceOrbit_eq.trans hh.symm)))
    rw [he2] at hn
    norm_num at hn
  rcases a.localCartan_invariant_seed_models h hc hv with hm | ⟨s,he,hs,hm⟩
  · exact not_natural_of_seven_centralizes_omega
      (inferInstance : IsElementaryAbelian 2 a.sourceOrbit)
      a.sourceOrbit_weakClosure_setup.le_sylow a.sourceOrbit_weakClosure_setup.normalizes
      a.sourceOrbit_weakClosure_setup.nontrivial (hDA.trans (c.left_le.trans inf_le_left))
      hcard hDC hm
  · let : NeZero s := ⟨hs.ne'⟩
    have hdiv := hermitian_seven_fixed_divides s h.sylow_normalizes
      (inferInstance : IsElementaryAbelian 2 a.sourceOrbit)
      a.sourceOrbit_weakClosure_setup.le_sylow a.sourceOrbit_weakClosure_setup.normalizes
      a.sourceOrbit_weakClosure_setup.nontrivial (hDA.trans c.left_le) hcard hDC hm
    have hs3 : 3 ∣ s := (Nat.prime_three.dvd_mul.mp (by rwa [he] at hn)).resolve_left (by decide)
    obtain ⟨k,rfl⟩ := hs3
    have hp : (2 : ZMod 7)^(3*k) = 1 := by
      rw [pow_mul, show (2 : ZMod 7)^3 = 1 by decide, one_pow]
    have hh := (ZMod.natCast_eq_zero_iff (2^(3*k)+1) 7).mpr hdiv
    rw [Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,hp] at hh
    exact (by decide : (2 : ZMod 7) ≠ 0) (by simpa only [one_add_one_eq_two] using hh)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
