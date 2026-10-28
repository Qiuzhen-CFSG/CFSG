module
public import Theory.SpecificGroups.PSL3Two.Parabolics.SquareSolvable
public import Theory.SpecificGroups.PSL3Two.Parabolics.WreathPair
public import Theory.GroupTheory.GeneralizedFitting.CenterlessTwoQuotient
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# Exchanged binary linear-three components with a cubic-plane Sylow overgroup

The two commuting centerless components use both available three-ranks.
Their outer automorphism groups are two-groups, so the pair has three-prime
index. A two-perfect two-by-three actor therefore lies in the pair. This
makes the original Sylow subgroup supplement the pair; its centralizer
is a normal two-subgroup and hence trivial when the ambient two-core is.

The supplied cubic plane in the solvable actor--Sylow join then applies
the marked square-parabolic calculation. It excludes both diagram actions
and identifies the whole group with SL₃(2) wr C₂.

Source application: Aschbacher--Smith 12.6.31, printed p.836, binary
exchanged-component exclusion. The matrix marking is the native calculation
used in 14.6.14(3), p.1033; ATLAS attribution is retained by its imports.
-/

public section
open Subgroup Theory.GroupTheory
namespace Matrix.PSL3Two.SquareParabolic
private theorem twoPerfect_le_of_three_free_index {X : Type*} [Group X] [Finite X]
    (A N : Subgroup X) [N.Normal] (hp : IsPPerfect 2 A)
    (hq : IsPGroup 3 (A ⧸ pCore 2 A)) (hi : Nat.Coprime 3 N.index) : A ≤ N := by
  let f := (QuotientGroup.mk' N).comp A.subtype
  have h3 : ¬ 3 ∣ Nat.card f.range := by
    intro hd
    exact (Nat.prime_three.coprime_iff_not_dvd.mp hi)
      (hd.trans (card_subgroup_dvd_card f.range))
  have hf : IsPGroup 2 f.range := by
    obtain ⟨r,hr⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
    obtain ⟨s,hs⟩ := hq.exists_card_eq
    have hcard : Nat.card A = 2 ^ r * 3 ^ s := by
      simpa only [index_eq_card,hr,hs] using (pCore 2 A).card_mul_index.symm
    have hd := card_range_dvd f
    rw [hcard] at hd
    exact IsPGroup.of_card_dvd_pow
      ((((Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm).pow_right s).dvd_of_dvd_mul_right hd)
  have he := hp.hom_eq_one_of_isPGroup hf f.rangeRestrict
  intro a ha
  apply (QuotientGroup.eq_one_iff a).mp
  exact congrArg Subtype.val (DFunLike.congr_fun he ⟨a,ha⟩)

/-- A two-perfect two-by-three actor with a cubic plane in its Sylow join
forces an exchanged binary linear-three pair to have the full inner wreath
extension. Both the pair and the Sylow subgroup remain the supplied ones. -/
theorem exchanged_full_wreath {X : Type*} [Group X] [Finite X]
    (C A : Subgroup X) (P : Sylow 2 X) (hC : IsComponent X C)
    (e : C ≃* Matrix.PSL3Two.SL)
    (hi : (normalizer (C : Set X)).index = 2)
    (hcore : pCore 2 X = ⊥) (hr : primeRank 3 X ≤ 2)
    (hp : IsPPerfect 2 A) (hqA : IsPGroup 3 (A ⧸ pCore 2 A))
    (hPA : (P : Subgroup X) ≤ normalizer (A : Set X))
    (hgen : componentOrbit C (P : Subgroup X) ⊔ A ⊔ (P : Subgroup X) = ⊤)
    (h9 : 9 ∣ Nat.card (A ⊔ (P : Subgroup X) : Subgroup X)) :
    Nonempty (X ≃* Matrix.PSL3Two.WreathPair.Actor) := by
  classical
  have hz : center C = ⊥ := by
    apply bot_unique
    intro x hx
    have hh : e x ∈ center Matrix.PSL3Two.SL := (centerCongr e ⟨x,hx⟩).property
    rw [Matrix.PSL3Two.center_eq_bot,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hmove : ¬ (P : Subgroup X) ≤ normalizer (C : Set X) := by
    intro h
    have hd := index_dvd_of_le h
    rw [hi] at hd
    exact P.not_dvd_index hd
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp hmove
  have htn' : t⁻¹ ∉ normalizer (C : Set X) := by simpa only [inv_mem_iff] using htn
  let N := C ⊔ C.conjBy t⁻¹
  have hneC : C.conjBy t⁻¹ ≠ C := fun he =>
    htn' (mem_normalizer_iff_map_conj_eq.mpr he)
  have hc : ⁅C,C.conjBy t⁻¹⁆ = ⊥ :=
    hC.commutator_eq_bot_of_ne (hC.map_conj t⁻¹) hneC.symm
  have hcomm := commutator_eq_bot_iff_le_centralizer.mp hc
  have hdis := disjoint_of_commuting_of_center_eq_bot hc hz
  have horbit : N = componentOrbit C (P : Subgroup X) := by
    apply le_antisymm
    · exact sup_le (le_componentOrbit C P)
        (le_iSup (fun s : P => C.map (MulAut.conj (s : X)).toMonoidHom)
          ⟨t⁻¹,(P : Subgroup X).inv_mem ht⟩)
    · apply iSup_le
      intro s
      change C.conjBy (s : X) ≤ N
      by_cases hs : (s : X) ∈ normalizer (C : Set X)
      · have he : C.conjBy (s : X) = C := mem_normalizer_iff_map_conj_eq.mp hs
        rw [he]
        exact le_sup_left
      · have he : (t⁻¹)⁻¹ * (s : X) ∈ normalizer (C : Set X) :=
          (mul_mem_iff_of_index_two hi).mpr (by simp [htn,hs])
        have hh := congrArg (fun B : Subgroup X => B.conjBy t⁻¹)
          (mem_normalizer_iff_map_conj_eq.mp he)
        change (C.conjBy ((t⁻¹)⁻¹ * (s : X))).conjBy t⁻¹ = C.conjBy t⁻¹ at hh
        rw [conjBy_mul,conjBy_inv'] at hh
        rw [hh]
        exact le_sup_right
  have hn : N.Normal := TwoOrbitThree.pair_normal_of_index_two C hi t⁻¹ htn'
  let := hn
  let et := (MulAut.conj t⁻¹).subgroupMap C
  have hzt : center (C.conjBy t⁻¹) = ⊥ := by
    apply bot_unique
    intro x hx
    have hh : et.symm x ∈ center C := ((centerCongr et).symm ⟨x,hx⟩).property
    rw [hz,mem_bot] at hh
    exact et.symm.map_eq_one_iff.mp hh
  have hzN : center N = ⊥ := TwoOrbitThree.join_center_eq_bot C _ hc hz hzt
  obtain ⟨ep,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting C _ hdis hcomm
  let en : N ≃* Matrix.PSL3Two.SL × Matrix.PSL3Two.SL :=
    ep.symm.trans (e.prodCongr (et.symm.trans e))
  have ho : IsPGroup 2 (MulAut.Outer C) :=
    Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.of_equiv (MulAut.outerCongr e).symm
  have hcop : Nat.Coprime 3 (MulAut.innerSubgroup C).index := by
    obtain ⟨n,hn⟩ := ho.exists_card_eq
    change Nat.Coprime 3 (Nat.card (MulAut.Outer C))
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hindex : Nat.Coprime 3 N.index := TwoOrbitThree.outer_pair_index_coprime_three
    C hi t⁻¹ hc hz (by rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_SL]; decide) hr hcop
  have hAN : A ≤ N := twoPerfect_le_of_three_free_index A N hp hqA hindex
  have hNP : N ⊔ (P : Subgroup X) = ⊤ := by
    apply top_unique
    rw [←hgen,←horbit]
    exact sup_le (sup_le le_sup_left (hAN.trans le_sup_left)) le_sup_right
  have hquot : IsPGroup 2 (X ⧸ N) := isPGroup_quotient_of_sup_eq_top N P P.isPGroup' hNP
  have hcent : centralizer (N : Set X) = ⊥ := by
    apply bot_unique
    exact (show centralizer (N : Set X) ≤ pCore 2 X from
      le_sSup ⟨inferInstance,centralizer_isPGroup_of_centerless_quotient N hzN hquot⟩).trans_eq hcore
  have hne : N ≠ ⊤ := by
    intro he
    have hNle : N ≤ normalizer (C : Set X) := sup_le C.le_normalizer
      ((le_centralizer_iff.mp hcomm).trans (Subgroup.centralizer_le_normalizer _))
    have hh : normalizer (C : Set X) = ⊤ := top_unique (he ▸ hNle)
    rw [hh,index_top] at hi
    omega
  let : Group.IsNilpotent (pCore 2 A) := pCore_isPGroup.isNilpotent
  let : Group.IsNilpotent (A ⧸ pCore 2 A) := hqA.isNilpotent
  let : Group.IsSolvable A :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 A)).mpr ⟨inferInstance,inferInstance⟩
  let : Group.IsNilpotent (P : Subgroup X) := P.isPGroup'.isNilpotent
  have hsol : Group.IsSolvable (A ⊔ (P : Subgroup X) : Subgroup X) :=
    Group.isSolvable_sup_of_normalizes A P hPA
  exact Matrix.PSL3Two.SquareParabolic.full_wreath_of_solvable_overgroup
    N (A ⊔ (P : Subgroup X)) en hcent hquot P hNP le_sup_right hsol h9 hne

end Matrix.PSL3Two.SquareParabolic
