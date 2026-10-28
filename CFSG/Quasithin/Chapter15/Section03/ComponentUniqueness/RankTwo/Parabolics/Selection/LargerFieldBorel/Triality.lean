module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.LargerFieldBorel.Reduction
public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.SpecificGroups.Triality.ParabolicLocalStructure
public import Theory.SpecificGroups.Triality.ConcreteBruhat.CartanNormalizer
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableParabolic.RankOne
public import GorensteinWalter.PSL2PerfectOfCard

/-!
# Solvable control in genuine triality parabolics

The concrete BN-pair puts every proper overgroup of the positive Borel in
one of the two root parabolics. Intersect a solvable Sylow overgroup with
the parabolic's normal local factor. Its image in the actual PSL₂ quotient
is proper by perfectness, and hence normalizes the image Sylow subgroup.
The two-group kernel lifts this normalization. The resulting normal Sylow
subgroup is characteristic in the intersection, giving normalization by
the whole solvable subgroup. Sylow conjugacy and the actual model
isomorphism then recover the intrinsic statement.

The local projection calculations adapt the private lemmas in
`Triality.ThreeOvergroupPlacement`, without its three-complement assumptions.
The local factor is normal in its parabolic, not in the ambient group.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.41(2),
printed p.1138, and the first paragraph of the final proof of 15.3.35,
p.1139; the concrete triality geometry is GLS3 §§2.3--2.6.
-/

public section

open Subgroup Triality.Standard Triality.Standard.Parabolics
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.LargerFieldBorel

private theorem projective_solvable_sylow_normalizes
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (_hF : 2 < Nat.card F) (T : Sylow 2 PSL(2, F)) (H : Subgroup PSL(2, F))
    (hsolv : Group.IsSolvable H) (hTH : (T : Subgroup PSL(2, F)) ≤ H)
    (hproper : H ≠ ⊤) : H ≤ normalizer (T : Set PSL(2, F)) := by
  let e := Theory.PSL2.sl2QuotientEquiv F
  have hesurj : Function.Surjective (e.symm.toMonoidHom) := by
    intro x
    obtain ⟨y, hy⟩ := e.symm.surjective x
    exact ⟨y, hy⟩
  let T' : Sylow 2 SL(2, F) := T.mapSurjective (f := e.symm.toMonoidHom) hesurj
  let H' : Subgroup SL(2, F) := H.map e.symm.toMonoidHom
  let _ : Group.IsSolvable H := hsolv
  have hsolv' : Group.IsSolvable H' :=
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective e.symm.toMonoidHom H)
  have hproper' : H' ≠ ⊤ := by
    intro hh
    apply hproper
    have htop := congrArg (Subgroup.map e.toMonoidHom) hh
    simpa [H', Subgroup.map_map] using htop
  have hT'H' : (T' : Subgroup SL(2, F)) ≤ H' := by
    change (T : Subgroup PSL(2, F)).map e.symm.toMonoidHom ≤ H.map e.symm.toMonoidHom
    exact Subgroup.map_mono hTH
  let _ : Group.IsSolvable H' := hsolv'
  have hn' := Theory.SpecificGroups.SymplecticFour.SolvableParabolic.proper_sylow_overgroup
    T' H' hproper' hT'H'
  have hmap := Subgroup.map_mono (f := e.toMonoidHom) hn'
  have hmap' : H'.map e.toMonoidHom ≤
      normalizer (((T' : Subgroup SL(2, F)).map e.toMonoidHom : Subgroup (PSL(2, F))) :
        Set (PSL(2, F))) := by
    rw [← Subgroup.map_equiv_normalizer_eq (T' : Subgroup SL(2, F)) e]
    exact hmap
  have hTmap : (T' : Subgroup SL(2, F)).map e.toMonoidHom = T := by
    rw [show (T' : Subgroup SL(2, F)) =
        (T : Subgroup (PSL(2, F))).map e.symm.toMonoidHom from
      Sylow.coe_mapSurjective hesurj T]
    rw [Subgroup.map_map]
    simp
  rw [hTmap] at hmap'
  simpa [H', Subgroup.map_map] using hmap'

private theorem normalizes_of_projection {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 3 < Nat.card F) (f : G →* PSL(2, F)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (T : Sylow 2 G) (H : Subgroup G)
    [Group.IsSolvable H] (hTH : (T : Subgroup G) ≤ H) :
    H ≤ normalizer (T : Set G) := by
  let Tq := T.mapSurjective hf
  have hsol : Group.IsSolvable (H.map f) :=
    Group.isSolvable_of_surjective (f.subgroupMap_surjective H)
  have hproper : H.map f ≠ ⊤ := by
    intro ht
    let _ := hsol
    let _ : Group.IsPerfect (PSL(2, F)) :=
      GorensteinWalter.psl2_isPerfect_of_card_gt_three F hF
    have hPSL : Group.IsSolvable (PSL(2, F)) :=
      Group.isSolvable_of_surjective (f := (H.map f).subtype)
        (by rw [ht]; exact topEquiv.surjective)
    exact Group.IsPerfect.not_isSolvable _ hPSL
  let _ := hsol
  have hnorm := projective_solvable_sylow_normalizes (by omega) Tq (H.map f) hsol
    (map_mono hTH) hproper
  have hker : f.ker ≤ (T : Subgroup G) := hk.le_sylow_of_normal T
  have hpre := (map_le_iff_le_comap.mp hnorm).trans
    ((Tq : Subgroup (PSL(2, F))).le_normalizer_comap f)
  simpa only [Tq, Sylow.coe_mapSurjective, comap_map_eq_self hker, Sylow.coe_coe] using hpre

private theorem normalizes_of_intermediate
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (L H : Subgroup G) (hTL : (T : Subgroup G) ≤ L)
    (hLN : L ≤ normalizer (T : Set G)) (hHL : H ≤ normalizer (L : Set G)) :
    H ≤ normalizer (T : Set G) := by
  let S := T.subtype hTL
  have hSN : S.Normal := (normal_subgroupOf_iff_le_normalizer hTL).mpr hLN
  have hSC : S.Characteristic := S.characteristic_of_normal hSN
  apply Subgroup.le_normalizer_iff.mpr
  intro h hh t ht
  let a := L.normalizerMonoidHom ⟨h, hHL hh⟩
  have hfix := hSC.fixed a
  have hmem : a ⟨t, hTL ht⟩ ∈ (S : Subgroup L) := by
    change (⟨t, hTL ht⟩ : L) ∈ (S : Subgroup L).comap a.toMonoidHom
    rw [hfix]
    exact ht
  exact hmem

private theorem normalizes_of_local_factor_projection
    {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 3 < Nat.card F) (K H : Subgroup G)
    (f : K →* PSL(2, F)) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H) (hTK : (T : Subgroup G) ≤ K)
    [Group.IsSolvable H] (hHK : H ≤ normalizer (K : Set G)) :
    H ≤ normalizer (T : Set G) := by
  have hsol : Group.IsSolvable (H.subgroupOf K) := by
    let j : H.subgroupOf K →* H :=
      { toFun := fun x => ⟨x.val.val, x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Group.isSolvable_of_isSolvable_injective (f := j)
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : H => (x : G)) h)))
  let _ := hsol
  have hlocal := normalizes_of_projection hF f hf hk (T.subtype hTK)
    (H.subgroupOf K) (fun _ hx => hTH hx)
  have hLN : H ⊓ K ≤ normalizer (T : Set G) := by
    intro x hx
    have hh := hlocal (show (⟨x, hx.2⟩ : K) ∈ H.subgroupOf K from hx.1)
    change (⟨x, hx.2⟩ : K) ∈ normalizer ((T : Subgroup G).subgroupOf K) at hh
    rw [← subgroupOf_normalizer_eq hTK] at hh
    exact hh
  exact normalizes_of_intermediate T (H ⊓ K) H (le_inf hTH hTK) hLN
    ((le_inf H.le_normalizer hHK).trans inf_normalizer_le_normalizer_inf)

private theorem normalizes_of_local_factor
    (P : Parameters) (hp : P.prime = 2) (hq : 3 < P.q) (a : Node)
    (T : Sylow 2 (Carrier P)) (H : Subgroup (Carrier P))
    (hsolv : Group.IsSolvable H) (hTH : (T : Subgroup (Carrier P)) ≤ H)
    (hTK : (T : Subgroup (Carrier P)) ≤ localFactor P a)
    (hHK : H ≤ normalizer (localFactor P a : Set (Carrier P))) :
    H ≤ normalizer (T : Set (Carrier P)) := by
  let _ : Group.IsSolvable H := hsolv
  cases a with
  | arms =>
      let _ : CharP (ExtensionField P) 2 := hp ▸ inferInstance
      let e := localFactorArmsQuotientEquivPSL2 P hp
      let qmk := QuotientGroup.mk' (pCore 2 (localFactor P .arms))
      let f := e.toMonoidHom.comp qmk
      have hf : Function.Surjective f := by
        exact e.surjective.comp (QuotientGroup.mk'_surjective _)
      have hker : f.ker = pCore 2 (localFactor P .arms) := by
        change (e.toMonoidHom.comp qmk).ker = _
        rw [MonoidHom.ker_comp_of_injective qmk e.toMonoidHom e.injective,
          QuotientGroup.ker_mk']
      have hF : 3 < Nat.card (ExtensionField P) := by
        rw [card_extensionField]
        exact lt_of_lt_of_le hq (Nat.le_pow (a := P.q) (b := 3) (by omega))
      apply normalizes_of_local_factor_projection hF (localFactor P .arms) H f hf
        (hker ▸ pCore_isPGroup) T hTH hTK
      exact hHK
  | central =>
      let _ : CharP (GaloisField P.prime P.exponent) 2 := hp ▸ inferInstance
      let e := localFactorCentralQuotientEquivPSL2 P hp
      let qmk := QuotientGroup.mk' (pCore 2 (localFactor P .central))
      let f := e.toMonoidHom.comp qmk
      have hf : Function.Surjective f := by
        exact e.surjective.comp (QuotientGroup.mk'_surjective _)
      have hker : f.ker = pCore 2 (localFactor P .central) := by
        change (e.toMonoidHom.comp qmk).ker = _
        rw [MonoidHom.ker_comp_of_injective qmk e.toMonoidHom e.injective,
          QuotientGroup.ker_mk']
      have hF : 3 < Nat.card (GaloisField P.prime P.exponent) := by
        simpa only [card_baseField] using hq
      apply normalizes_of_local_factor_projection hF (localFactor P .central) H f hf
        (hker ▸ pCore_isPGroup) T hTH hTK
      exact hHK

private theorem proper_borel_overgroup_le_parabolic
    (n : ℕ) (hn : 0 < n) (P : Subgroup (Carrier (binaryParameters n hn)))
    (hBP : borel (binaryParameters n hn) ≤ P) (hP : P ≠ ⊤) :
    ∃ a : Node, P ≤ parabolic (binaryParameters n hn) a := by
  classical
  let T := ConcreteBruhat.titsSystem n hn
  have hclass : P = T.standardParabolic (T.simpleIndices P) :=
    T.subgroup_eq_standardParabolic_simpleIndices P hBP
  have hnot : ¬ (ConcreteBruhat.simpleReflection n hn .arms ∈ T.simpleIndices P ∧
      ConcreteBruhat.simpleReflection n hn .central ∈ T.simpleIndices P) := by
    rintro ⟨ha, hc⟩
    apply hP
    have hI : T.simpleIndices P = T.S := by
      apply Set.Subset.antisymm (T.simpleIndices_subset P)
      intro w hw
      rcases (ConcreteBruhat.mem_titsSystem_S_iff n hn w).mp hw with rfl | rfl
      · exact ha
      · exact hc
    rw [hclass, hI, T.standardParabolic_S]
  by_cases ha : ConcreteBruhat.simpleReflection n hn .arms ∈ T.simpleIndices P
  · refine ⟨.arms, ?_⟩
    rw [ConcreteBruhat.parabolic_eq_standardParabolic, hclass]
    apply T.standardParabolic_mono
    intro w hw
    rcases (ConcreteBruhat.mem_titsSystem_S_iff n hn w).mp
      (T.simpleIndices_subset P hw) with rfl | rfl
    · exact Set.mem_singleton _
    · exact (hnot ⟨ha, hw⟩).elim
  · refine ⟨.central, ?_⟩
    rw [ConcreteBruhat.parabolic_eq_standardParabolic, hclass]
    apply T.standardParabolic_mono
    intro w hw
    rcases (ConcreteBruhat.mem_titsSystem_S_iff n hn w).mp
      (T.simpleIndices_subset P hw) with rfl | rfl
    · exact (ha hw).elim
    · exact Set.mem_singleton _

private theorem triality_carrier_control (n : ℕ) (hn : 1 < n) :
    ParabolicSolvableControl (Carrier (binaryParameters n (by omega))) := by
  let Q := binaryParameters n (by omega)
  intro U P H hNP hP hHP hsol hUH
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Carrier Q) U (unipotentSylow Q rfl)
  let e := MulAut.conj g
  have hU : (U : Subgroup (Carrier Q)).map e.toMonoidHom = unipotent Q :=
    congrArg Sylow.toSubgroup hg
  have hBP : borel Q ≤ P.map e.toMonoidHom := by
    rw [← ConcreteBruhat.normalizer_unipotent_eq_borel Q rfl,
      ← hU, ← map_equiv_normalizer_eq]
    exact map_mono hNP
  have hproper : P.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hP
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa only [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] using ht
  obtain ⟨a, hPa⟩ := proper_borel_overgroup_le_parabolic n (by omega)
    (P.map e.toMonoidHom) hBP hproper
  have hHa : H.map e.toMonoidHom ≤ parabolic Q a := (map_mono hHP).trans hPa
  let _ : Group.IsSolvable H := hsol
  have hsol' : Group.IsSolvable (H.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective H)
  have hUH' : (unipotentSylow Q rfl : Subgroup (Carrier Q)) ≤ H.map e.toMonoidHom := by
    change unipotent Q ≤ H.map e.toMonoidHom
    rw [← hU]
    exact map_mono hUH
  have hq : 3 < Q.q := by
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    change 3 < 2 ^ n
    omega
  have hHK : H.map e.toMonoidHom ≤ normalizer (localFactor Q a : Set (Carrier Q)) :=
    hHa.trans (Subgroup.le_normalizer_of_normal_subgroupOf (localFactor_le_parabolic Q a))
  have hN := normalizes_of_local_factor Q rfl hq a (unipotentSylow Q rfl)
    (H.map e.toMonoidHom) hsol' hUH' (unipotentSylow_le_localFactor Q rfl a) hHK
  change H.map e.toMonoidHom ≤ normalizer (unipotent Q : Set (Carrier Q)) at hN
  rw [← hU, ← map_equiv_normalizer_eq] at hN
  exact (map_le_map_iff_of_injective e.injective).mp hN

/-- In genuine ³D₄(2ⁿ), n > 1, a solvable Sylow overgroup inside any proper
Borel overgroup normalizes that Sylow subgroup. -/
theorem triality_control {D : Type*} [Group D] [Finite D]
    {n : ℕ} (hn : 1 < n) (hmodel : Triality.Standard.IsTrialityGroupAt (2 ^ n) D) :
    ParabolicSolvableControl D := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff D n (by omega)).mp hmodel
  exact control_of_mulEquiv e (triality_carrier_control n hn)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.LargerFieldBorel
