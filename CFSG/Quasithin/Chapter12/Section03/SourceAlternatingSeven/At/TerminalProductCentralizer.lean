module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductCentralizer
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductLocalFactorsThompson

/-!
# TerminalProductCentralizer at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalProductCentralizer`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Stellmacher

open scoped commutatorElement

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

private theorem fiveCore_faithful_at (g : alternatingGroup (Fin 5))
    (h : ∀ x, BinaryPermutation.alternatingCoreRepresentation (Fin 5) g x = x) : g = 1 := by
  have hn : BinaryPermutation.naturalRepresentation (Fin 5) g.val = 1 := by
    apply LinearMap.ext
    intro x
    let e := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
    have hh := congrArg e (h (e.symm x))
    change e (BinaryPermutation.coreRepresentation (Fin 5) g.val (e.symm x)) = e (e.symm x) at hh
    rw [BinaryPermutation.coreEquivNatural_equivariant,e.apply_symm_apply] at hh
    exact hh
  apply Subtype.ext
  exact (BinaryPermutation.naturalRepresentation_injective (Fin 5) (by simp))
    (hn.trans (map_one _).symm)

theorem quotient_component_card_bound_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    let := normal_subgroupOf_of_le_normalizer (P.Y_normalizes_component C)
    ∃ n, Nat.card (P.Y ⧸ P.K.subgroupOf P.Y) ∣ 3 * 2^n := by
  let K := P.K.subgroupOf P.Y
  let := normal_subgroupOf_of_le_normalizer (P.Y_normalizes_component C)
  let R := P.L2 ⊔ (T : Subgroup G)
  have hRY : R ≤ P.Y := sup_le P.second_le_Y P.sylow_le_Y
  let f := (QuotientGroup.mk' K).comp (inclusion hRY)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective K x
    have hgen : K ⊔ R.subgroupOf P.Y = ⊤ := by
      apply map_injective P.Y.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le P.component_le_Y,
        map_subgroupOf_eq_of_le hRY,←MonoidHom.range_eq_map,range_subtype]
      exact sup_assoc _ _ _ |>.symm
    have hy : y ∈ K ⊔ R.subgroupOf P.Y := hgen ▸ mem_top y
    obtain ⟨k,hk,r,hr,he⟩ := mem_sup_of_normal_left.mp hy
    have hrG : (r : G) ∈ R := hr
    refine ⟨⟨r,hrG⟩,?_⟩
    change QuotientGroup.mk' K r = QuotientGroup.mk' K y
    have hkq : QuotientGroup.mk' K k = 1 := (QuotientGroup.eq_one_iff (N := K) k).mpr hk
    rw [←he,map_mul,hkq,one_mul]
  have hRT : (T : Subgroup G) ≤ normalizer (P.L2 : Set G) :=
    (P.sylow_le_pointNormalizer_at structural).trans (P.pointNormalizer_normalizes_L2_at structural C)
  have hdR : Nat.card R ∣ Nat.card P.L2 * Nat.card (T : Subgroup G) := by
    rw [card_mul_eq_card_inf_mul_card_sup_of_normalizes P.L2 (T : Subgroup G) hRT]
    exact dvd_mul_left _ _
  obtain ⟨q,_⟩ := P.L2_seed_at structural escape C
  have hc : Nat.card (P.L2 ⧸ pCore 2 P.L2) = 3 := by
    rw [Nat.card_congr q.toEquiv,Nat.card_eq_fintype_card,card_alternatingGroup]; decide
  obtain ⟨a,ha⟩ := (pCore_isPGroup (p := 2) (G := P.L2)).exists_card_eq
  obtain ⟨b,hb⟩ := T.isPGroup'.exists_card_eq
  have hL : Nat.card P.L2 = 2^a * 3 := by
    rw [←(pCore 2 P.L2).card_mul_index,index_eq_card,ha,hc]
  refine ⟨a+b,?_⟩
  have hd := (Subgroup.card_dvd_of_surjective f hf).trans hdR
  simpa only [hL,hb,pow_add,mul_assoc,mul_left_comm] using hd

theorem U_centralizer_eq_twoCore_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.Y ⊓ centralizer (P.U : Set G) = P.Y.pCoreIn 2 := by
  let W := P.U.subgroupOf P.Y
  let := P.U_reduced.normal
  let B := centralizer (W : Set P.Y)
  let K := P.K.subgroupOf P.Y
  let := normal_subgroupOf_of_le_normalizer (P.Y_normalizes_component C)
  let f := (QuotientGroup.mk' K).comp B.subtype
  have hB : B.map P.Y.subtype = P.Y ⊓ centralizer (P.U : Set G) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨y.property,?_⟩
      intro z hz
      exact congrArg Subtype.val (hy ⟨z,P.U_le_Y hz⟩ hz)
    · rintro ⟨hx,hc⟩
      refine ⟨⟨x,hx⟩,?_,rfl⟩
      intro z hz
      exact Subtype.ext (hc z hz)
  have hBZ : B.map P.Y.subtype ≤ centralizer (P.Z : Set G) := by
    rw [hB]
    exact inf_le_right.trans (centralizer_le (le_componentOrbit P.Z P.Y))
  have hres : primeToResidual 3 B ≤ f.ker := by
    intro b hb
    let j : B →* centralizer (P.Z : Set G) :=
      (P.Y.subtype.comp B.subtype).codRestrict _ (fun x =>
        hBZ (mem_map_of_mem P.Y.subtype x.property))
    have hh := map_primeToResidual_le_of_hom 3 j (mem_map_of_mem j hb)
    have hm := mem_map_of_mem (centralizer (P.Z : Set G)).subtype hh
    rw [←P.L1_eq_ambient_residual_of_component_at C structural] at hm
    exact (QuotientGroup.eq_one_iff b.val).mpr (P.L1_le_component_at structural escape C hm)
  have hcop : Nat.Coprime 3 (Nat.card f.range) := by
    rw [←index_ker]
    exact (primeToResidual_index_coprime 3).coprime_dvd_right (index_dvd_of_le hres)
  obtain ⟨n,hn⟩ := P.quotient_component_card_bound_at structural escape C
  have hd : Nat.card f.range ∣ 3*2^n := f.range.card_subgroup_dvd_card.trans hn
  have hp : IsPGroup 2 f.range := IsPGroup.of_card_dvd_pow
    (hcop.symm.dvd_of_dvd_mul_left hd)
  have hk : IsPGroup 2 f.ker := by
    let j : f.ker →* (P.K.pCoreIn 2) :=
      (P.Y.subtype.comp (B.subtype.comp f.ker.subtype)).codRestrict _ (fun x => by
        apply (P.component_seed_centralizer C).le
        refine ⟨(QuotientGroup.eq_one_iff x.val.val).mp x.property,?_⟩
        have hx : (x.val.val : G) ∈ centralizer (P.U : Set G) :=
          (hB ▸ mem_map_of_mem P.Y.subtype x.val.property).2
        exact centralizer_le P.component_seed_le_U hx)
    exact (isPGroup_pCoreIn 2 P.K).of_injective j (by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : P.K.pCoreIn 2 => (z : G)) h)
  have hpB : IsPGroup 2 B := by
    have hh := hp.comap_of_ker_isPGroup f hk
    rw [MonoidHom.comap_range_self] at hh
    exact hh.of_equiv (topEquiv : (⊤ : Subgroup B) ≃* B)
  have hcore : B ≤ pCore 2 P.Y := le_sSup ⟨inferInstance,hpB⟩
  apply le_antisymm ?_ P.twoCore_le_U_centralizer
  rw [←hB]
  exact map_mono hcore

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

