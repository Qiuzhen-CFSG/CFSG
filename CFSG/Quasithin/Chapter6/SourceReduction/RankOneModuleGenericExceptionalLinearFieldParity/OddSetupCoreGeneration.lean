module
public import Theory.SpecificGroups.SL2.OddBorelNormalizerEscape
public import Theory.GroupTheory.CyclicHallNormalizerEscape
public import Theory.GroupTheory.PResidual.SimpleQuotientNormalGeneration
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupSolvableCore

/-!
# Generating the nonabelian core from a prime Cartan subgroup

Choose a prime subgroup C of the actual Cartan. A Weyl normalizer element
lifts through O₂(L), giving l in N_L(C) outside the point stabilizer.
Solvability of the literal residual quotient-centralizer puts Y=[S,C]
in the point-normalizer core. Since l preserves Y, both generators U and
Uˡ centralize Y modulo V. Coprime idempotence then gives Y≤V.

The nontrivial prime image normally generates the simple L/O₂(L); the
original two-perfection lifts this to L. Thus [S,L]≤V. The two-conjugate
product formula puts S in U and hence in the point-normalizer core.
The earlier collapse theorem now yields S=S₂, elementary O₂(L) and
[O₂(L),L]=V, without any additional core-containment premise.

Solvability remains original 5.1.16(2). Its proof, block exclusion and
residual-normalizer TI remain with qt-d-1222-linear-field-parity.
Source: Aschbacher–Smith, 5.1.17, printed pp.640–641 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H A B C : Subgroup G} {n p : ℕ} [Fact p.Prime]

theorem fundamental_prime_normalizer_escape
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hCA : C ≤ A) (hp : Odd p) (hC : IsPGroup p C) :
    ∃ l : G, l ∈ L ∧ l ∉ (normalizerSetup T L D.moduleSubgroup).G₁ ∧
      l ∈ normalizer (C : Set G) := by
  have hCL : C ≤ L := hCA.trans (c.left_le.trans inf_le_left)
  have hpoint := fundamental_point_normalizer (H := H) (A := A) D hTL hpsl hodd hnat
  obtain ⟨F,_,_,_,_,e,_,_⟩ := hnat
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ _
    rw [← e.map_one,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  have hN : normalizer (P : Set L) = (localBorel T L).subgroupOf L := by
    change normalizer ((P : Subgroup L) : Set L) = _
    rw [hP,←inf_subgroupOf_right,←subgroupOf_normalizer_eq (show (T : Subgroup G) ⊓ L ≤ L from inf_le_right)]
    ext x
    simp only [mem_subgroupOf,mem_inf,x.property,true_and]
  have hCN : C.subgroupOf L ≤ normalizer (P : Set L) := by
    rw [hN]
    exact subgroupOf_mono L (hCA.trans c.left_le)
  let Q := P.mapSurjective hq
  let Cq := (C.subgroupOf L).map q
  have hCq : Cq ≤ normalizer (Q : Set SL(2,F)) := (map_mono hCN).trans (le_normalizer_map q)
  have ho : Odd (Nat.card Cq) := by
    obtain ⟨k,hk⟩ := (hC.comap_subtype.map q).exists_card_eq
    change Nat.card Cq = p^k at hk
    rw [hk]
    exact hp.pow
  have hout := Matrix.SpecialLinearGroup.odd_subgroup_normalizer_not_le_sylow_normalizer Q Cq hCq ho
  have hout' : ¬ normalizer (C.subgroupOf L : Set L) ≤ normalizer (P : Set L) := by
    apply normalizer_not_le_of_two_kernel q hq (hk.symm ▸ pCore_isPGroup)
      (normalizer (P : Set L)) (C.subgroupOf L) hp hC.comap_subtype
    rwa [P.normalizer_map_surjective q hq]
  obtain ⟨l,hl,hlout⟩ := Set.not_subset.mp hout'
  refine ⟨l,l.property,?_,?_⟩
  · intro hg
    apply hlout
    rw [hN]
    exact hpoint.le ⟨l.property,hg⟩
  · have hh : l ∈ (normalizer (C : Set G)).subgroupOf L := by
      rwa [subgroupOf_normalizer_eq hCL]
    exact hh
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B C : Subgroup G} {n p : ℕ} [Fact p.Prime]

theorem prime_normalClosure_in_left
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hCL : C ≤ L) (hC : IsPGroup p C) (hp : Odd p) (hne : C ≠ ⊥) :
    normalClosure (C.subgroupOf L : Set L) = ⊤ := by
  have hperf : IsPPerfect 2 L := h.local_mem.2.2.1
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h.linear
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 2^2 ≤ 2^n from Nat.pow_le_pow_right (by decide) (show 2 ≤ n by have := h.exponent; omega))
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard
  let : IsSimpleGroup (L ⧸ pCore 2 L) := e.isSimpleGroup
  let q := QuotientGroup.mk' (pCore 2 L)
  have hk : q.ker = pCore 2 L := QuotientGroup.ker_mk' _
  apply normalClosure_eq_top_of_pPerfect_simple_image hperf q
    (QuotientGroup.mk'_surjective _) (hk.symm ▸ pCore_isPGroup)
  intro hz
  have hle : C.subgroupOf L ≤ pCore 2 L := by
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
  have hdis : Disjoint (C.subgroupOf L) (pCore 2 L) :=
    IsPGroup.disjoint_of_ne p 2 (by intro he; subst p; exact (by decide : ¬ Odd 2) hp)
      _ _ hC.comap_subtype pCore_isPGroup
  have he : C.subgroupOf L = ⊥ := eq_bot_iff.mpr (fun x hx => disjoint_def.mp hdis hx (hle hx))
  apply hne
  have hh := congrArg (map L.subtype) he
  simpa only [map_subgroupOf_eq_of_le hCL,Subgroup.map_bot] using hh
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
open ChapterG.Section02.RankOneHigherFields
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B C : Subgroup G} {n p : ℕ}

private theorem fundamental_nonabelian_core_le_of_prime
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    (hnon : ¬ IsMulCommutative (normalizerSetup T L D.moduleSubgroup).U)
    [Fact p.Prime] (hCA : C ≤ A) (hp : Odd p) (hC : IsPGroup p C) (hne : C ≠ ⊥)
    {l : G} (hl : l ∈ L) (hlout : l ∉ (normalizerSetup T L D.moduleSubgroup).G₁)
    (hlC : l ∈ normalizer (C : Set G)) :
    (normalizerSetup T L D.moduleSubgroup).S l ≤
      (normalizerSetup T L D.moduleSubgroup).QH := by
  let E := normalizerSetup T L D.moduleSubgroup
  obtain ⟨F,_,_,⟨d⟩⟩ := fundamental_nonabelian_marking h hH c hodd hK hnf D hnat hnon hl hlout
  have hg := fundamental_g2_normalizer h hH c hodd hK hnf D hnat
  change E.Hypothesis at hg
  have hut := hg.U_normal_in_T.1
  have hf := hg.frattini_U_le_point
  have hLI := d.L_le_I hut hf
  have hLS : L ≤ normalizer (E.S l : Set G) := hLI.trans Hypothesis.I_normalizes_core
  have hLV : L ≤ normalizer (E.V : Set G) := hLI.trans (d.I_normalizes hut)
  have hCL : C ≤ L := hCA.trans (c.left_le.trans inf_le_left)
  let Y := ⁅E.S l,C⁆
  have hYcore : Y ≤ E.QH :=
    (commutator_mono le_rfl hCA).trans (le_sup_left.trans
      (fundamental_nonabelian_cartan_layers_le_core h hH c hodd hK hnf hm hsolv D hnat hnon hl hlout))
  have hIg := d.g_mem_I hut hf
  have hSmap : (E.S l).map (MulAut.conj l⁻¹).toMonoidHom = E.S l :=
    mem_normalizer_iff_map_conj_eq.mp (Hypothesis.I_normalizes_core
      (D := E) (g := l) ((E.I l).inv_mem hIg))
  have hCmap : C.map (MulAut.conj l⁻¹).toMonoidHom = C :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (C : Set G)).inv_mem hlC)
  have hYmap : Y.map (MulAut.conj l⁻¹).toMonoidHom = Y := by
    dsimp only [Y]
    rw [map_commutator,hSmap,hCmap]
  have hVmap : E.V.map (MulAut.conj l⁻¹).toMonoidHom = E.V :=
    mem_normalizer_iff_map_conj_eq.mp (hLV (L.inv_mem hl))
  have hUY : ⁅E.U,Y⁆ ≤ E.V :=
    ((commutator_mono le_rfl hYcore).trans hg.commutator_U_core_le_point).trans hg.point_le
  have hUgY : ⁅ChapterG.Section02.Setup.conjugate E.U l,Y⁆ ≤ E.V := by
    have hh := map_mono (f := (MulAut.conj l⁻¹).toMonoidHom) hUY
    rwa [map_commutator,hYmap,hVmap] at hh
  have hIY : ⁅E.I l,Y⁆ ≤ E.V := by
    have hi : E.I l ≤ commutatorPreimage (E.I l) Y E.V :=
      sup_le (le_commutatorPreimage le_sup_left hUY)
        (le_commutatorPreimage le_sup_right hUgY)
    exact (commutator_mono hi le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ (d.I_normalizes hut))
  have hC2 : Nat.Coprime 2 (Nat.card C) := by
    obtain ⟨k,hk⟩ := hC.exists_card_eq
    rw [hk]
    exact hp.coprime_two_left.pow_right k
  have hCp : IsPPerfect 2 C := by
    apply (pResidual_eq_top_iff 2 C).mp
    apply top_unique
    intro x _
    exact mem_pResidual_of_orderOf_coprime (hC2.of_dvd_right (orderOf_dvd_natCard x))
  have hYV : Y ≤ E.V := by
    have he : ⁅Y,C⁆ = Y := commutator_isPPerfect_idempotent C (E.S l) hCp
      (pCore_isPGroup.map (E.I l).subtype) (hCL.trans hLS)
    rw [← he,commutator_comm]
    exact (commutator_mono (hCL.trans hLI) le_rfl).trans hIY
  let J := commutatorPreimage L (E.S l) E.V
  have hJN : L ≤ normalizer (J : Set G) :=
    commutatorPreimage_normalized _ _ _ _ hLV L.le_normalizer hLS hLV
  let : (J.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer hJN
  have hCJ : C ≤ J := le_commutatorPreimage hCL (by rwa [commutator_comm])
  have hclosure : normalClosure (C.subgroupOf L : Set L) ≤ J.subgroupOf L :=
    normalClosure_le_normal (fun x hx => hCJ hx)
  rw [prime_normalClosure_in_left h hCL hC hp hne] at hclosure
  have hLJ : L ≤ J := fun x hx => hclosure (show (⟨x,hx⟩ : L) ∈ (⊤ : Subgroup L) from trivial)
  have hLSV : ⁅L,E.S l⁆ ≤ E.V :=
    (commutator_mono hLJ le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hLV)
  have hSU : E.S l ≤ E.U := by
    rw [d.S_eq_WProduct_of_source hut hf]
    apply sup_le inf_le_left
    rintro x ⟨w,hw,rfl⟩
    change l⁻¹*w*l⁻¹⁻¹ ∈ E.U
    have hh := commutator_le.mp hLSV l⁻¹ (L.inv_mem hl) w hw.2
    have hhU : ⁅l⁻¹,w⁆ ∈ E.U := (le_conjugateSpanBy E.V E.H) hh
    simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using E.U.mul_mem hhU hw.1
  exact hSU.trans hg.U_le_core

theorem fundamental_nonabelian_core_le_of_solvable
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    (hnon : ¬ IsMulCommutative (normalizerSetup T L D.moduleSubgroup).U)
    {l : G} (hl : l ∈ L) (hlout : l ∉ (normalizerSetup T L D.moduleSubgroup).G₁) :
    (normalizerSetup T L D.moduleSubgroup).S l ≤
      (normalizerSetup T L D.moduleSubgroup).QH := by
  have hcard : 1 < Nat.card A := by
    rw [(c.left_cyclic_and_card h.sylow_normalizes h.linear).2]
    have hpow : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by decide) (show 2 ≤ n by have := h.exponent; omega)
    omega
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hcard)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨C₀,hC₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p (n := 1) (by simpa using hpd)
  let C := C₀.map A.subtype
  have hCA : C ≤ A := map_subtype_le _
  have hCcard : Nat.card C = p := by
    rw [card_map_of_injective A.subtype_injective,hC₀,pow_one]
  have hC : IsPGroup p C := IsPGroup.of_card (n := 1) (by simpa using hCcard)
  have hpo : Odd p := Nat.coprime_two_right.mp
    (((cartan_card_coprime_six_of_odd c h.sylow_normalizes h.linear hodd).of_dvd_right
      (by decide : 2 ∣ 6)).of_dvd_left hpd)
  have hne : C ≠ ⊥ := by intro he; have hh := hCcard; rw [he,card_bot] at hh; exact hp.ne_one hh.symm
  obtain ⟨r,hr,hrout,hrC⟩ := fundamental_prime_normalizer_escape D h.sylow_normalizes h.linear hnat c hodd hCA hpo hC
  have hb := fundamental_nonabelian_core_le_of_prime h hH c hodd hK hnf hm hsolv D hnat hnon hCA hpo hC hne hr hrout hrC
  have hlI := (fundamental_nonabelian_geometry h hH c hodd hK hnf D hnat hnon hl hlout).1
  have hrI := (fundamental_nonabelian_geometry h hH c hodd hK hnf D hnat hnon hr hrout).1
  have he : (normalizerSetup T L D.moduleSubgroup).S l =
      (normalizerSetup T L D.moduleSubgroup).S r := by
    change ((normalizerSetup T L D.moduleSubgroup).I l).pCoreIn 2 =
      ((normalizerSetup T L D.moduleSubgroup).I r).pCoreIn 2
    rw [hlI,hrI]
  rwa [he]
/-- Solvability alone discharges the earlier generated-core containment premise. -/
theorem fundamental_nonabelian_core_collapse_of_solvable
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    (hnon : ¬ IsMulCommutative (normalizerSetup T L D.moduleSubgroup).U)
    {l : G} (hl : l ∈ L) (hlout : l ∉ (normalizerSetup T L D.moduleSubgroup).G₁) :
    let E := normalizerSetup T L D.moduleSubgroup
    E.S l = E.S₂ l ∧ IsElementaryAbelian 2 (L.pCoreIn 2) ∧
      ⁅L.pCoreIn 2,L⁆ = D.moduleSubgroup := by
  exact fundamental_nonabelian_core_collapse h hH c hodd hK hnf D hnat hnon hl hlout
    (fundamental_nonabelian_core_le_of_solvable h hH c hodd hK hnf hm hsolv D hnat hnon hl hlout)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
