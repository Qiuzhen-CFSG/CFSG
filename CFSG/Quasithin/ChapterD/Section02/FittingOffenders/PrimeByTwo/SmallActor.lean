module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.PrimeByTwo
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryOffender.PrimeCentralizerImage
public import Theory.Representation.BinaryOffender.MovedSpaceTransport

/-!
# Small elementary actors on normal primes greater than three

D.2.13 applies to the actual prime-by-two join: faithfulness of the
elementary complement on the odd subgroup makes the two-core trivial.
Every starred actor moves the odd core, so the prime is five and the
minimum cubic ratio is two. Fixed codimension at most actor rank plus one
then forces actor rank one. Saturated support identifies the literal
odd commutator as order five, moving a binary four-space.

The fixed-space application transports this calculation back through the
actual restriction map, whose kernel on the odd subgroup is trivial.
No prime-rank inheritance by arbitrary quotients is used.

Source: Aschbacher–Smith D.2.13, pp.184–185, used in 14.5.11,
pp.1015–1016, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterD
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A faithful elementary supplement with the near-maximum bound is a quintic reflection. -/
theorem prime_five_small_supplement
    (hf : Function.Injective ρ) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (P A : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (hA : IsElementaryTwo A) (hgen : P ⊔ A = ⊤)
    (hfaith : A ⊓ centralizer (P : Set G) = ⊥)
    (hcub : IsCubic ρ A) (hcod : fixedCodim ρ A ≤ rank A + 1) :
    p = 5 ∧ cubicRatio ρ = 2 ∧ rank A = 1 ∧ Nat.card A = 2 ∧
      fixedCodim ρ A = 2 ∧ Nat.card (⁅P,A⁆ : Subgroup G) = 5 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⁅P,A⁆) = 4 ∧
      IsCompl (subspaceCommutator ρ ⊤ ⁅P,A⁆) (fixedSpace ρ (⁅P,A⁆ ⊔ A)) := by
  have hp2 : p ≠ 2 := by omega
  have ho := (Fact.out : p.Prime).odd_of_ne_two hp2
  let : IsElementaryAbelian 2 A := hA.2
  have hA2 := IsElementaryAbelian.isPGroup 2 A
  have hdis : Disjoint P A := IsPGroup.disjoint_of_ne p 2 hp2 P A hP hA2
  have hcompl : P.IsComplement' A := isComplement'_of_disjoint_and_mul_eq_univ hdis (by
    rw [← normal_mul,hgen]; rfl)
  have hodd : Odd (Nat.card P) := by
    obtain ⟨n,hn⟩ := hP.exists_card_eq
    exact hn ▸ ho.pow
  let S : Sylow 2 G := hA2.toSylow (by rw [hcompl.index_eq_card]; exact hodd.not_two_dvd_nat)
  have hQA : pCore 2 G ≤ A := pCore_isPGroup.le_sylow_of_normal S
  have hQP : pCore 2 G ≤ centralizer (P : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (commutator_eq_bot_of_disjoint
        (IsPGroup.disjoint_of_ne 2 p hp2.symm _ _ pCore_isPGroup hP))
  have hcore : pCore 2 G = ⊥ := bot_unique ((le_inf hQA hQP).trans hfaith.le)
  have hPC : P ≤ pCore p G := le_sSup ⟨inferInstance,hP⟩
  have hq : IsPGroup 2 (G ⧸ pCore p G) :=
    isPGroup_quotient_of_sup_eq_top _ A hA2
      (top_unique (hgen ▸ sup_le_sup_right hPC A))
  have hratio : cubicRatio ρ ≤ 2 := by
    apply (cubicRatio_le_nat_iff ρ 2).mpr
    exact ⟨A,hA,hcub,hcod.trans (by have := hA.rank_pos; omega)⟩
  obtain ⟨B,hB⟩ := (QhatStar_nonempty_iff ρ).mpr hratio
  have hCB := centralizer_pCore_le_of_quotient_isPGroup p 2 hcore hq
  have hmove : ⁅pCore p G,B⁆ ≠ ⊥ := by
    intro he
    have hBC : B ≤ pCore p G :=
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)).trans hCB
    have hd : Disjoint B (pCore p G) := IsPGroup.disjoint_of_ne 2 p hp2.symm _ _
      (by let := hB.1.2.1.2; exact IsElementaryAbelian.isPGroup 2 B) pCore_isPGroup
    exact hB.1.2.1.1 (bot_unique ((le_inf le_rfl hBC).trans hd.le_bot))
  obtain ⟨h35,h5⟩ := source_lemma_D_2_13_one_two ρ hf hB ho hmove
  have hp5 : p = 5 := h35.resolve_left (by omega)
  have hr2 : cubicRatio ρ = 2 := (h5 hp5).1
  have hlow : (2 : ℝ≥0∞) ≤ actionRatio ρ A := by
    rw [← hr2]
    exact iInf_le_of_le A (iInf_le_of_le ⟨hA,hcub⟩ le_rfl)
  have hnlow : 2 * rank A ≤ fixedCodim ρ A := by
    exact_mod_cast (ENNReal.le_div_iff_mul_le (by left; exact_mod_cast (Nat.ne_of_gt hA.rank_pos))
      (by simp)).mp hlow
  have hrA : rank A = 1 := by have := hA.rank_pos; omega
  have hdA : fixedCodim ρ A = 2 := by omega
  have hmP : ⁅P,A⁆ ≠ ⊥ := by
    intro he
    have hc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
    exact hA.1 (bot_unique ((le_inf le_rfl hc).trans hfaith.le))
  obtain ⟨hcard,_,hd,hs⟩ := cyclic_actor_saturated_support ρ hf hA hrA
    (p := p) (k := 2) (Or.inr rfl) (by omega) P hP
    (le_sSup ⟨inferInstance,hP.isNilpotent⟩) hmP hdA
  exact ⟨hp5,hr2,hrA,by rw [hA.card_eq_two_pow_rank,hrA]; rfl,hdA,
    hcard.trans hp5,hd,hs⟩

/-- The same conclusion inside the actual join of the odd group and actor. -/
theorem prime_five_small_actor
    (hf : Function.Injective ρ) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (P A : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (hA : IsElementaryTwo A) (hfaith : A ⊓ centralizer (P : Set G) = ⊥)
    (hcub : IsCubic ρ A) (hcod : fixedCodim ρ A ≤ rank A + 1) :
    p = 5 ∧ rank A = 1 ∧ Nat.card A = 2 ∧ fixedCodim ρ A = 2 ∧
      Nat.card (⁅P,A⁆ : Subgroup G) = 5 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⁅P,A⁆) = 4 ∧
      IsCompl (subspaceCommutator ρ ⊤ ⁅P,A⁆) (fixedSpace ρ (⁅P,A⁆ ⊔ A)) := by
  let H := P ⊔ A
  have hPH : P ≤ H := le_sup_left
  have hAH : A ≤ H := le_sup_right
  have hPA : P.subgroupOf H ⊔ A.subgroupOf H = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hPH,map_subgroupOf_eq_of_le hAH,
      ←MonoidHom.range_eq_map,range_subtype]
  let : IsElementaryAbelian 2 A := hA.2
  have hAe : IsElementaryTwo (A.subgroupOf H) := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf hAH⟩
    intro hz
    have hh := congrArg (Subgroup.map H.subtype) hz
    rw [map_subgroupOf_eq_of_le hAH,Subgroup.map_bot] at hh
    exact hA.1 hh
  have hfaithH : A.subgroupOf H ⊓ centralizer (P.subgroupOf H : Set H) = ⊥ := by
    apply bot_unique
    intro a ha
    apply Subtype.ext
    apply hfaith.le
    refine ⟨ha.1,?_⟩
    intro p hp
    exact congrArg Subtype.val (ha.2 ⟨p,hPH hp⟩ hp)
  have hcu : IsCubic (ρ.comp H.subtype) (A.subgroupOf H) := by
    intro a ha b hb c hc v
    exact hcub a ha b hb c hc v
  have hco : fixedCodim (ρ.comp H.subtype) (A.subgroupOf H) ≤
      rank (A.subgroupOf H) + 1 := by
    rw [fixedCodim_subgroupOf ρ hAH,rank_subgroupOf hAH]
    exact hcod
  obtain ⟨hp5,_,hr,hc,hd,hdc,hdim,hs⟩ := prime_five_small_supplement
    (ρ.comp H.subtype) (hf.comp H.subtype_injective) hp
    (P.subgroupOf H) (A.subgroupOf H) hP.comap_subtype hAe hPA hfaithH hcu hco
  have hm : ⁅P.subgroupOf H,A.subgroupOf H⁆ = (⁅P,A⁆).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hPH,map_subgroupOf_eq_of_le hAH,
      map_subgroupOf_eq_of_le (Subgroup.commutator_le_sup P A)]
  have hmoved : subspaceCommutator (ρ.comp H.subtype) ⊤
      ⁅P.subgroupOf H,A.subgroupOf H⁆ = subspaceCommutator ρ ⊤ ⁅P,A⁆ := by
    rw [subspaceCommutator_comp_map,map_commutator,
      map_subgroupOf_eq_of_le hPH,map_subgroupOf_eq_of_le hAH]
  have hfixed : fixedSpace (ρ.comp H.subtype)
      (⁅P.subgroupOf H,A.subgroupOf H⁆ ⊔ A.subgroupOf H) =
        fixedSpace ρ (⁅P,A⁆ ⊔ A) := by
    rw [fixedSpace_comp_map,Subgroup.map_sup,map_commutator,
      map_subgroupOf_eq_of_le hPH,map_subgroupOf_eq_of_le hAH]
  rw [rank_subgroupOf hAH] at hr
  rw [fixedCodim_subgroupOf ρ hAH] at hd
  rw [hm] at hdc
  exact ⟨hp5,hr,(Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv).symm.trans hc,hd,
    (Nat.card_congr (subgroupOfEquivOfLe (Subgroup.commutator_le_sup P A)).toEquiv).symm.trans hdc,
    hmoved ▸ hdim,hmoved ▸ hfixed ▸ hs⟩

end CFSG.Quasithin.ChapterD

namespace CFSG.Quasithin.ChapterD
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative ENNReal
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The quintic commutator and its support survive in the original kernel-fixed space. -/
theorem prime_fixed_small_actor
    (hf : Function.Injective ρ) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (R B : Subgroup G) [R.Normal] [IsElementaryAbelian 2 B]
    (hR : IsPGroup p R)
    (he : IsElementaryTwo (restrictedSubgroup ρ
      (fixedSpace ρ (B ⊓ centralizer (R : Set G))) B))
    (hcub : IsCubic (subspaceImageRepresentation ρ
      (fixedSpace ρ (B ⊓ centralizer (R : Set G))))
      (restrictedSubgroup ρ (fixedSpace ρ (B ⊓ centralizer (R : Set G))) B))
    (hcod : fixedCodim (subspaceImageRepresentation ρ
      (fixedSpace ρ (B ⊓ centralizer (R : Set G))))
      (restrictedSubgroup ρ (fixedSpace ρ (B ⊓ centralizer (R : Set G))) B) ≤
      rank (restrictedSubgroup ρ (fixedSpace ρ (B ⊓ centralizer (R : Set G))) B) + 1) :
    let U := fixedSpace ρ (B ⊓ centralizer (R : Set G))
    let I := restrictedSubgroup ρ U B
    p = 5 ∧ rank I = 1 ∧ Nat.card I = 2 ∧
      fixedCodim (subspaceImageRepresentation ρ U) I = 2 ∧
      Nat.card (⁅R,B⁆ : Subgroup G) = 5 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ U ⁅R,B⁆) = 4 := by
  let K := B ⊓ centralizer (R : Set G)
  let U := fixedSpace ρ K
  let S := subspaceStabilizer ρ U
  let f := subspaceActionHom ρ U
  let P := restrictedSubgroup ρ U R
  let I := restrictedSubgroup ρ U B
  have ho := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hRs : R ≤ S := le_stabilizer_fixedSpace_of_commutator_eq_bot ρ R K
    (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mpr inf_le_right))
  have hBs : B ≤ S := le_stabilizer_fixedSpace_of_commutator_eq_bot ρ B K
    (commutator_eq_bot_iff_le_centralizer.mpr
      (B.le_centralizer.trans (centralizer_le inf_le_left)))
  let : P.Normal := Normal.map inferInstance f
    (stabilizerRepresentation ρ U).asGroupHom.rangeRestrict_surjective
  have hP : IsPGroup p P := hR.comap_subtype.map f
  obtain ⟨hp5,hr,hc,hd,hdc,hdim,_⟩ := prime_five_small_actor
    (subspaceImageRepresentation ρ U) (subspaceImageRepresentation_injective ρ U)
    hp P I hP he (prime_fixed_image_centralizer ρ hf ho R B hR) hcub hcod
  have hDR : ⁅R,B⁆ ≤ R := commutator_le_left _ _
  have hDs : ⁅R,B⁆ ≤ S := hDR.trans hRs
  have hcomm : restrictedSubgroup ρ U ⁅R,B⁆ = ⁅P,I⁆ := by
    have hh : (⁅R,B⁆).subgroupOf S = ⁅R.subgroupOf S,B.subgroupOf S⁆ := by
      apply map_injective S.subtype_injective
      rw [map_commutator,map_subgroupOf_eq_of_le hRs,
        map_subgroupOf_eq_of_le hBs,map_subgroupOf_eq_of_le hDs]
    change ((⁅R,B⁆).subgroupOf S).map f = _
    rw [hh,map_commutator]
    rfl
  have hker : subspaceKernel ρ U ⁅R,B⁆ = ⊥ := by
    apply bot_unique
    intro d hd
    exact (prime_centralizer_fixed_kernel ρ hf ho R B hR).1.le ⟨hDR hd.1,hd.2⟩
  have hcard := card_subspaceKernel_mul_image ρ U ⁅R,B⁆ hDs
  rw [hker,card_bot,one_mul,hcomm] at hcard
  have hm : (subspaceCommutator (subspaceImageRepresentation ρ U) ⊤
      (restrictedSubgroup ρ U ⁅R,B⁆)).map U.subtype = subspaceCommutator ρ U ⁅R,B⁆ := by
    simpa only [Submodule.map_top,Submodule.range_subtype] using
      subspaceCommutator_restricted_map ρ U ⁅R,B⁆ hDs ⊤
  have hdimMap := (Submodule.equivMapOfInjective U.subtype U.subtype_injective
    (subspaceCommutator (subspaceImageRepresentation ρ U) ⊤
      (restrictedSubgroup ρ U ⁅R,B⁆))).finrank_eq
  rw [hm,hcomm] at hdimMap
  exact ⟨hp5,hr,hc,hd,hcard.symm.trans hdc,hdimMap.symm.trans hdim⟩
end CFSG.Quasithin.ChapterD
