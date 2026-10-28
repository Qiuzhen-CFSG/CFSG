module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalChief
public import Theory.SpecificGroups.Alternating.SevenFiveCubicControl
public import Theory.Representation.BinaryAlternatingSevenCubicRecognition

/-!
# Excluding the original right block in the local Cartan configuration

The original cubic has at least three noncentral factors on T∩L. A right
block would force at least two on the right four-space, so the cubic acts
there without nontrivial fixed points. Its image in the actual A₇ quotient
is therefore a three-cycle outside the residual A₅. It centralizes the
image of T∩L, since it normalizes that subgroup in the A₅ normalizer.
The quotient contributes no noncentral factors, leaving at most two in
total, a contradiction.

Together with C.1.28 and the previous degree theorem, this leaves only a
degree-two left block in the noncentral branch. Its exclusion and the
postcentralization recognition and component sieve remain necessary.
Source: Aschbacher–Smith 5.1.13, printed pp.637–638, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
private theorem LocalA7Configuration.right_block_chief_comparison
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D)
    (hb : ChapterC.IsChiBlockIn (pResidual 2 H)) :
    conjugationCubicLength D ((T : Subgroup G) ⊓ L) ≤
      conjugationCubicLength D (localOmegaModule T K) + 1 := by
  let M := K ⊔ (T : Subgroup G)
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  let C := D.subgroupOf M
  let S := ((T : Subgroup G) ⊓ L).subgroupOf M
  let U := (localOmegaModule T K).subgroupOf M
  let Q := pCore 2 M
  let R := Q ⊔ S
  have hDK : D ≤ K := (d.cubic_le.trans inf_le_right).trans a.contains
  have hDM : D ≤ M := hDK.trans le_sup_left
  have hSM : (T : Subgroup G) ⊓ L ≤ M := inf_le_left.trans le_sup_right
  have hC3 : IsPGroup 3 C := IsPGroup.of_card (n := 1)
    ((Nat.card_congr (subgroupOfEquivOfLe hDM).toEquiv).trans d.cubic_card)
  have hr : IsPReduced 2 U := LocalOmega.reduced_internal a.reduced
  let := hr.normal
  let := hr.elementary
  have hUQ : U ≤ Q := le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩
  have hQP : Q ≤ (P : Subgroup M) := pCore_isPGroup.le_sylow_of_normal P
  have hRP : R ≤ (P : Subgroup M) := sup_le hQP (fun _ hx => hx.1)
  have hDN : D ≤ normalizer (((T : Subgroup G) ⊓ L) : Set G) :=
    ((d.cubic_le.trans inf_le_left).trans c.left_le).trans inf_le_right
  have hCS : C ≤ normalizer (S : Set M) := by
    apply le_normalizer_iff.mpr
    intro x hx y hy
    change (x : G) * (y : G) * (x : G)⁻¹ ∈ (T : Subgroup G) ⊓ L
    exact le_normalizer_iff.mp hDN x.val hx y.val (show y.val ∈ (T : Subgroup G) ⊓ L from hy)
  have hCR : C ≤ normalizer (R : Set M) :=
    (le_inf (show C ≤ normalizer (Q : Set M) from le_normalizer_of_normal) hCS).trans
      (normalizer_inf_normalizer_le_normalizer_sup Q S)
  have hmove := (a.right_block_layers h hH hgen c d hb).2.2
  have hQC : ⁅Q,C⁆ ≤ U := by
    apply (map_le_map_iff_of_injective M.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hDM,map_subgroupOf_eq_of_le a.reduced.1]
    exact (commutator_mono le_rfl hDK).trans_eq hmove
  have hlenQ : conjugationCubicLength C Q =
      conjugationCubicLength D (localOmegaModule T K) := by
    rw [←CubicComparison.length_eq_of_commutator_le C Q U hC3 pCore_isPGroup hUQ
      le_normalizer_of_normal le_normalizer_of_normal hQC]
    exact CubicComparison.length_subgroupOf D (localOmegaModule T K) M hDM a.reduced.1
  obtain ⟨q,hq,_,hk⟩ := a.four_action h (a.four h hH hgen c d)
  let f := q.subgroupMap R
  have hf : Function.Surjective f := q.subgroupMap_surjective R
  have hker : Q.subgroupOf R = f.ker := by
    ext r
    change r.val ∈ Q ↔ f r = 1
    rw [show Q = q.ker from hk.symm]
    constructor
    · intro hr
      exact Subtype.ext hr
    · intro hr
      exact congrArg Subtype.val hr
  let e : (R ⧸ Q.subgroupOf R) ≃* R.map q := QuotientGroup.liftEquiv _ hf hker
  have hcardP : Nat.card (P.mapSurjective hq) = 8 := by
    rw [Sylow.card_eq_multiplicity,nat_card_alternatingGroup,Nat.card_eq_fintype_card]
    norm_num [Nat.factorial]
    rw [show (2520 : ℕ).factorization 2 = 3 by
      rw [show 2520 = 2^3*315 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2 ∣ 315)]]
    norm_num
  have hcard : Nat.card (R ⧸ Q.subgroupOf R) ≤ 8 := by
    rw [Nat.card_congr e.toEquiv]
    exact (card_le_of_le (map_mono hRP)).trans_eq hcardP
  have hsection := CubicComparison.section_length_le_log_card C R Q hC3
    (P.isPGroup'.to_le hRP) le_sup_left hCR le_normalizer_of_normal
  have hlog : Nat.log 4 (Nat.card (R ⧸ Q.subgroupOf R)) ≤ 1 :=
    (Nat.log_mono_right hcard).trans (by decide : Nat.log 4 8 ≤ 1)
  have hmono := conjugationCubicLength_mono C (show S ≤ R from le_sup_right)
  rw [CubicComparison.length_subgroupOf D ((T : Subgroup G) ⊓ L) M hDM hSM] at hmono
  change conjugationCubicLength D ((T : Subgroup G) ⊓ L) ≤ conjugationCubicLength C R at hmono
  unfold sectionCubicLength at hsection
  rw [hlenQ] at hsection
  omega

/-- In the right-block branch the escaping cubic fixes no point of the
entire original right four-space. -/
private theorem LocalA7Configuration.right_block_cubic_fixed
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D)
    (hb : ChapterC.IsChiBlockIn (pResidual 2 H)) :
    localOmegaModule T K ⊓ centralizer (D : Set G) = ⊥ := by
  have hlo := (a.left_cubic_chief_lower h hH hgen c d).2.2
  have hup := a.right_block_chief_comparison h hH hgen c d hb
  let U := localOmegaModule T K
  let F := (centralizer (D : Set G)).subgroupOf U
  have hi : 2 ≤ Nat.log 4 F.index := by
    change 3 ≤ conjugationCubicLength D ((T : Subgroup G) ⊓ L) at hlo
    change conjugationCubicLength D ((T : Subgroup G) ⊓ L) ≤ Nat.log 4 F.index + 1 at hup
    omega
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (4 : ℕ)) hi
  have hp := Nat.pow_log_le_self 4 (Subgroup.FiniteIndex.index_ne_zero (H := F))
  have hcard := F.card_mul_index
  have hc : Nat.card U = 16 := a.four h hH hgen c d
  rw [hc] at hcard
  have hpos : 0 < Nat.card F := Nat.card_pos
  have he : F = ⊥ := eq_bot_of_card_eq F (by norm_num at hpow; nlinarith)
  apply bot_unique
  intro x hx
  have hh : (⟨x,hx.1⟩ : U) ∈ F := hx.2
  rw [he] at hh
  exact congrArg Subtype.val (mem_bot.mp hh)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
open Representation Representation.BinaryOffender
open scoped IsMulCommutative
/-- The original right residual cannot be a block. The apparent third
chief factor would force a three-cycle outside the marked A5, which fixes
the entire quotient of the original left Sylow intersection. -/
theorem LocalA7Configuration.not_right_block
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    ¬ ChapterC.IsChiBlockIn (pResidual 2 H) := by
  intro hb
  let M := K ⊔ (T : Subgroup G)
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  let C := D.subgroupOf M
  let S := ((T : Subgroup G) ⊓ L).subgroupOf M
  let U := (localOmegaModule T K).subgroupOf M
  let Q := pCore 2 M
  let R := Q ⊔ S
  let E := (residual H).subgroupOf M
  let J := H.subgroupOf M
  have hDK : D ≤ K := (d.cubic_le.trans inf_le_right).trans a.contains
  have hDM : D ≤ M := hDK.trans le_sup_left
  have hSM : (T : Subgroup G) ⊓ L ≤ M := inf_le_left.trans le_sup_right
  have hEM : residual H ≤ M := (d.residual_le.trans a.contains).trans le_sup_left
  have hHM : H ≤ M := by
    rw [←residual_sup_sylow T H hH.1.1.2]
    exact sup_le hEM le_sup_right
  have hC3 : Nat.card C = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hDM).toEquiv).trans d.cubic_card
  have hpC : IsPGroup 3 C := IsPGroup.of_card (n := 1) hC3
  have hr : IsPReduced 2 U := LocalOmega.reduced_internal a.reduced
  let := hr.normal
  let := hr.elementary
  have hUQ : U ≤ Q := le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩
  have hQP : Q ≤ (P : Subgroup M) := pCore_isPGroup.le_sylow_of_normal P
  have hRP : R ≤ (P : Subgroup M) := sup_le hQP (fun _ hx => hx.1)
  have hDN : D ≤ normalizer (((T : Subgroup G) ⊓ L) : Set G) :=
    ((d.cubic_le.trans inf_le_left).trans c.left_le).trans inf_le_right
  have hCS : C ≤ normalizer (S : Set M) := by
    apply le_normalizer_iff.mpr
    intro x hx y hy
    change (x : G) * (y : G) * (x : G)⁻¹ ∈ (T : Subgroup G) ⊓ L
    exact le_normalizer_iff.mp hDN x.val hx y.val hy
  have hCR : C ≤ normalizer (R : Set M) :=
    (le_inf (show C ≤ normalizer (Q : Set M) from le_normalizer_of_normal) hCS).trans
      (normalizer_inf_normalizer_le_normalizer_sup Q S)
  obtain ⟨q,hq,hk,hcore,_,e,_,_⟩ := a.four_residual_natural h hH hgen c d
  have hkerQ : q.ker = Q := hcore
  let e5 := e.trans SL2FourNatural.alternatingFiveEquiv
  let ρ := NormalElementaryQuotient.representation U q hq hk
  have hf := NormalElementaryQuotient.representation_injective U q hq hk
  have hd : Module.finrank (ZMod 2) (Additive U) = 4 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
    change Nat.card U = Nat.card (ZMod 2)^Module.finrank (ZMod 2) (Additive U) at hh
    rw [Nat.card_congr (subgroupOfEquivOfLe a.reduced.1).toEquiv,
      a.four h hH hgen c d,Nat.card_zmod] at hh
    exact hh.symm
  have hPN : (P : Subgroup M) ≤ normalizer (E : Set M) := by
    intro t ht
    exact mem_normalizer_iff.mpr (fun r => mem_normalizer_iff.mp
      (le_normalizer_residual H (hH.1.1.2 ht)) r.val)
  have hPq : ((P : Subgroup M).map q) ≤ normalizer (E.map q : Set (alternatingGroup (Fin 7))) :=
    (map_mono hPN).trans (E.le_normalizer_map q)
  have hCq3 : Nat.card (C.map q) = 3 :=
    GLS3.Chapter5.cubic_image_card_of_two_kernel q (hcore.symm ▸ pCore_isPGroup) C hC3
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := C.map q) 3 (by rw [hCq3])
  let z₀ : alternatingGroup (Fin 7) := z
  have hz3 : orderOf z₀ = 3 := (Subgroup.orderOf_coe z).trans hz
  have hgenC : zpowers z₀ = C.map q := eq_of_le_of_card_ge
    (zpowers_le.mpr z.property) (by rw [Nat.card_zpowers,hz3,hCq3])
  have hfree : ∀ v : Additive U, ρ z₀ v = v → v = 0 := by
    intro v hv
    have hfix : v ∈ fixedSpace ρ (C.map q) := hgenC ▸ (mem_fixedSpace_zpowers_iff ρ z₀ v).mpr hv
    have hh := (NormalElementaryQuotient.mem_fixedSpace_image U q hq hk C v).mp hfix
    have hc : (v.toMul.val : G) ∈ localOmegaModule T K ⊓ centralizer (D : Set G) := by
      refine ⟨v.toMul.property,?_⟩
      intro x hx
      exact congrArg M.subtype (hh (⟨x,hDM hx⟩ : M) hx)
    have he := (a.right_block_cubic_fixed h hH hgen c d hb).le hc
    exact Subtype.ext (Subtype.ext (mem_bot.mp he))
  have hzthree := Representation.binaryAlternatingSeven_threeCycle_of_fixedPointFree ρ hf hd z₀ hz3 hfree
  have hzout : z₀ ∉ E.map q := by
    intro hzE
    have hCE : C.map q ≤ E.map q := by rw [←hgenC]; exact zpowers_le.mpr hzE
    have hkerJ : q.ker ≤ J := by
      rw [hkerQ]
      exact hQP.trans (fun _ ht => hH.1.1.2 ht)
    have hCJ : C ≤ J := by
      have hh := map_le_iff_le_comap.mp (hCE.trans (map_mono (comap_mono (show residual H ≤ H from map_subtype_le _))))
      change C ≤ (J.map q).comap q at hh
      rwa [comap_map_eq_self hkerJ] at hh
    apply d.cubic_escape
    have hDH : D ≤ H := by
      have hh := map_mono (f := M.subtype) hCJ
      rwa [map_subgroupOf_eq_of_le hDM,map_subgroupOf_eq_of_le hHM] at hh
    exact hDH.trans (le_normalizer_residual H)
  have hzN : z₀ ∈ normalizer (S.map q : Set (alternatingGroup (Fin 7))) :=
    ((map_mono hCS).trans (S.le_normalizer_map q)) z.property
  have hcent := Theory.SpecificGroups.Alternating.SevenFiveCubicControl.five_threeCycle_centralizes (E.map q) e5
    (P.mapSurjective hq) hPq z₀ hzthree hzout (S.map q)
    ((map_mono (show S ≤ (P : Subgroup M) from fun _ hx => hx.1)).trans hPq) hzN
  have hCcent : C.map q ≤ centralizer (S.map q : Set (alternatingGroup (Fin 7))) := by
    rw [←hgenC]
    exact zpowers_le.mpr hcent
  have hqR : R.map q = S.map q := by
    rw [Subgroup.map_sup,show Q = q.ker from hcore.symm,
      (Subgroup.map_eq_bot_iff _).mpr le_rfl,bot_sup_eq]
  have hRC : ⁅R,C⁆ ≤ Q := by
    rw [←hkerQ,←Subgroup.map_eq_bot_iff,map_commutator,hqR,commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hCcent
  have hlenR := CubicComparison.length_eq_of_commutator_le C R Q hpC
    (P.isPGroup'.to_le hRP) le_sup_left hCR le_normalizer_of_normal hRC
  have hmove := (a.right_block_layers h hH hgen c d hb).2.2
  have hQC : ⁅Q,C⁆ ≤ U := by
    apply (map_le_map_iff_of_injective M.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hDM,map_subgroupOf_eq_of_le a.reduced.1]
    exact (commutator_mono le_rfl hDK).trans_eq hmove
  have hlenU := CubicComparison.length_eq_of_commutator_le C Q U hpC pCore_isPGroup hUQ
    le_normalizer_of_normal le_normalizer_of_normal hQC
  have hup := CubicComparison.length_le_log_card C U
  have hcU : Nat.card U = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe a.reduced.1).toEquiv).trans (a.four h hH hgen c d)
  rw [hcU] at hup
  have hmono := conjugationCubicLength_mono C (show S ≤ R from le_sup_right)
  rw [CubicComparison.length_subgroupOf D ((T : Subgroup G) ⊓ L) M hDM hSM] at hmono
  change conjugationCubicLength D ((T : Subgroup G) ⊓ L) ≤ conjugationCubicLength C R at hmono
  have hlo := (a.left_cubic_chief_lower h hH hgen c d).2.2
  norm_num at hup
  omega

/-- C.1.28 now forces the original left subgroup to be a block. -/
theorem LocalA7Configuration.left_block
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    ChapterC.IsChiBlockIn (L.subgroupOf (L ⊔ (T : Subgroup G))) :=
  (a.left_or_right_block h hH hgen c d).resolve_right (a.not_right_block h hH hgen c d)

/-- The genuine FF producer reduces noncentrality under the original inputs
to degree two and the literal left block; the right block is excluded. -/
theorem localCartan_noncentral_degree_two_left_block
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) :
    n = 2 ∧ ChapterC.IsChiBlockIn (L.subgroupOf (L ⊔ (T : Subgroup G))) ∧
      ¬ ChapterC.IsChiBlockIn (pResidual 2 H) := by
  obtain ⟨K,a⟩ := localCartan_ffReduction T L W n h H hH hgen A B c Y hY X D d hXC
  exact ⟨a.degree_two h hH hgen c d, a.left_block h hH hgen c d,
    a.not_right_block h hH hgen c d⟩

/-- If the literal right residual is a block, the original component
centralizes omega. No additional configuration is assumed. -/
theorem localCartan_centralizes_of_right_block
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D)
    (hb : ChapterC.IsChiBlockIn (pResidual 2 H)) : X ≤ omegaCentralizer T := by
  by_contra hc
  exact (localCartan_noncentral_degree_two_left_block h hH hgen c hY d hc).2.2 hb

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
