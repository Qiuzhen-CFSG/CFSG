module
public import CFSG.Quasithin.Chapter6.Section01.SourceCentralLine
public import CFSG.Quasithin.Chapter6.Section02.NaturalHyperplanes
public import Theory.SpecificGroups.SL2.SylowNormalizerCard
public import Theory.GroupTheory.IrreducibleNormalizerCore
public import Theory.GroupAction.ComponentRankAction.OuterTwo
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import Theory.SpecificGroups.SymmetricFourSolvable
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.AlternatingCubics
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank

/-!
# The original cubic in the central-line normalizer quotient

The Sylow normalizer in the actual SL₂(4) quotient has order twelve.
Surjectivity from the original Sylow normalizer and Cauchy's theorem produce
an element of order three in L normalizing T ∩ L and Z_S. Its action on the
four-group Z_S is fixed-free and irreducible. Consequently O₂(N_G(Z_S))
centralizes Z_S, and the cubic survives outside the centralizer image in
the literal quotient N_G(Z_S)/O₂(N_G(Z_S)).

The original conjugation action on Z_S descends through that quotient;
its kernel is exactly the image of C_G(Z_S). Since Aut(Z_S) is solvable,
every perfect component belongs to this kernel. In ambient three-rank at
most two, A.3.18 then excludes a component of rank two with prime-to-three
center and two-group outer automorphisms. The concrete alternating and
binary-linear exclusions retain their actual model isomorphisms; the
triple alternating covers are also excluded by their cubic-containment
calculations.

This constructs the ambient cubic and component exclusions used in 6.1.19.
It does not make the cubic act on W = U ∩ Q_z, since it moves z. Lifting
the W/Z_S transvection factors to these components, factor assembly, the
amalgam contradiction, initial 6.1.4–5 and unconditional 6.1.27 remain with
qt-d-1222-rankone-recognition-natural.

The Sylow-normalizer construction adapts the elementary argument in
RankOneModuleRecognitionIdentification, with only n = 2 and naturalness
as inputs; no identification or Conclusion6127 is invoked.
Source: Aschbacher–Smith 6.1.19, pp.674–675, and A.3.18, pp.51–53.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass.{u}} {T : Sylow 2 G} {L M R : Subgroup G}

/-- The original L contains a cubic normalizing the marked Sylow intersection
and central line, with its fixed-free conjugation action retained. -/
theorem natural_four_exists_cubic
    (h : Hypothesis611 κ T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2) :
    ∃ d ∈ L, d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G) ∧
      d ∈ normalizer (ZS (T : Subgroup G) L R : Set G) ∧
      orderOf d = 3 ∧
      ∀ z ∈ ZS (T : Subgroup G) L R, d * z * d⁻¹ = z → z = 1 := by
  obtain ⟨F, _, _, _, hF, e, f, hf⟩ := hnat
  obtain ⟨P, hP⟩ := NormalSylowQuotientAction.intersection_sylow T L
    h.sylow_normalizes_L
  let q : L →* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective hq
  have hcard : Nat.card (normalizer (Q : Set (Matrix.SpecialLinearGroup (Fin 2) F))) = 12 := by
    simpa [Sylow.coe_coe, hF] using
      Matrix.SpecialLinearGroup.card_sylow_normalizer_even Q
  have hdiv : 3 ∣ Nat.card (normalizer (P : Set L)) := by
    have hmap := (normalizer (P : Set L)).card_map_dvd q
    rw [P.normalizer_map_surjective q hq] at hmap
    exact (show 3 ∣ 12 by decide).trans (hcard ▸ hmap)
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := normalizer (P : Set L)) 3 hdiv
  have hm : (d.val : G) ∈ normalizer (((P : Subgroup L).map L.subtype) : Set G) :=
    (P : Subgroup L).le_normalizer_map L.subtype (mem_map.mpr ⟨d.val, d.property, rfl⟩)
  rw [hP, subgroupOf_map_subtype] at hm
  have hdG : orderOf (d.val : G) = 3 := by
    simpa only [Subgroup.orderOf_coe] using hd
  have hnat : IsNaturalModule L (layer L R) 2 := ⟨F, inferInstance, inferInstance,
    inferInstance, hF, e, f, hf⟩
  refine ⟨d.val,d.val.property,hm,?_,hdG,?_⟩
  · exact inf_normalizer_le_normalizer_inf ⟨normalizer_commutator_ge_right R L d.val.property,
      normalizer_le_normalizer_centralizer _ hm⟩
  · intro z hz hfix
    exact hnat.cubic_fixed_eq_one d.val.property hdG hz.1 hfix

private theorem cubic_irreducible_four (Z : Subgroup G) (hZ : Nat.card Z = 4)
    {d : G} (hd : orderOf d = 3)
    (hfix : ∀ z ∈ Z, d * z * d⁻¹ = z → z = 1)
    (A : Subgroup G) (hAZ : A ≤ Z) (hn : zpowers d ≤ normalizer (A : Set G)) :
    A = ⊥ ∨ A = Z := by
  by_cases hA : A = ⊥
  · exact Or.inl hA
  have hC : A ⊓ centralizer (zpowers d : Set G) = ⊥ := by
    apply eq_bot_iff.mpr
    rintro a ⟨ha,hc⟩
    exact hfix a (hAZ ha) (mul_inv_eq_iff_eq_mul.mpr (hc d (mem_zpowers d)))
  have hp : IsPGroup 3 (zpowers d) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers,pow_one] using hd)
  have hc := card_modEq_card_inf_centralizer (zpowers d) A hp hn
  rw [hC,card_bot] at hc
  have hlo : 1 < Nat.card A := by
    let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hA
    exact Finite.one_lt_card
  have hhi : Nat.card A ≤ 4 := (card_le_of_le hAZ).trans_eq hZ
  have he : Nat.card A = 4 := by
    change Nat.card A % 3 = 1 % 3 at hc
    omega
  exact Or.inr (eq_of_le_of_card_ge hAZ (by rw [he,hZ]))

/-- The actual central-line normalizer has two-core inside its centralizer. -/
theorem natural_four_normalizer_core_centralizes
    (h : Hypothesis611 κ T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2) :
    (Escape.H (T : Subgroup G) L R).pCoreIn 2 ≤ Escape.I (T : Subgroup G) L R := by
  obtain ⟨d,_,_,hdN,hd,hfix⟩ := natural_four_exists_cubic h hnat
  have hc : Nat.card (ZS (T : Subgroup G) L R) = 4 :=
    (hnat.sylow_intersection_geometry T h.sylow_normalizes_L).1
  exact pCoreIn_le_centralizer_of_irreducible
    (ZS (T : Subgroup G) L R) (zpowers d) (Escape.H (T : Subgroup G) L R)
    (T.isPGroup'.to_le h.ZS_le_T) (ZS (T : Subgroup G) L R).le_normalizer le_rfl (zpowers_le.mpr hdN)
    (cubic_irreducible_four _ hc hd hfix)

/-- The original cubic survives outside the centralizer image after quotienting
the actual normalizer by its two-core. The ambient odd rank bound also survives. -/
theorem natural_four_ambient_quotient_cubic
    (h : Hypothesis611 κ T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2) :
    let N := Escape.H (T : Subgroup G) L R
    let I := (Escape.I (T : Subgroup G) L R).subgroupOf N
    let q := QuotientGroup.mk' (pCore 2 N)
    pCore 2 N ≤ I ∧ primeRank 3 (N ⧸ pCore 2 N) ≤ 2 ∧
      ∃ c : N, (c : G) ∈ L ∧ (c : G) ∈ normalizer ((T : Subgroup G) ⊓ L : Set G) ∧
        orderOf c = 3 ∧
        orderOf (q c) = 3 ∧ q c ∉ I.map q := by
  let N := Escape.H (T : Subgroup G) L R
  let I := (Escape.I (T : Subgroup G) L R).subgroupOf N
  let q := QuotientGroup.mk' (pCore 2 N)
  have hcore : pCore 2 N ≤ I := by
    intro x hx
    exact natural_four_normalizer_core_centralizes h hnat (mem_map_of_mem N.subtype hx)
  have hsq : IsSQTK κ N := h.simpleQTKE.twoLocal_sqtk
    ⟨ZS (T : Subgroup G) L R,h.ZS_ne_bot,T.isPGroup'.to_le h.ZS_le_T,rfl⟩
  have hr : primeRank 3 (N ⧸ pCore 2 N) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans
      (hsq.stronglyQuasithin 3 (by decide) (by decide))
  obtain ⟨d,hdL,hdTL,hdN,hd,hfix⟩ := natural_four_exists_cubic h hnat
  let c : N := ⟨d,hdN⟩
  have hout : c ∉ I := by
    intro hc
    have hzero : ZS (T : Subgroup G) L R = ⊥ := by
      apply eq_bot_iff.mpr
      intro z hz
      exact hfix z hz (mul_inv_eq_iff_eq_mul.mpr (hc z hz).symm)
    exact h.ZS_ne_bot hzero
  have hqout : q c ∉ I.map q := by
    intro hx
    have hc : c ∈ (I.map q).comap q := hx
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hcore] at hc
    exact hout hc
  refine ⟨hcore,hr,c,hdL,hdTL,?_,?_,hqout⟩
  · exact (Subgroup.orderOf_coe c).symm.trans hd
  · apply orderOf_eq_prime
    · rw [←map_pow]
      have hc : c^3=1 := Subtype.ext (by rw [←hd]; exact pow_orderOf_eq_one d)
      rw [hc,map_one]
    · intro he
      exact hqout (he ▸ (I.map q).one_mem)

/-- Conjugation on Z_S descends to the normalizer two-core quotient with its
exact centralizer-image kernel and solvable target. -/
theorem natural_four_quotient_line_action
    (h : Hypothesis611 κ T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2) :
    let Z := ZS (T : Subgroup G) L R
    let N := Escape.H (T : Subgroup G) L R
    let I := (Escape.I (T : Subgroup G) L R).subgroupOf N
    let q := QuotientGroup.mk' (pCore 2 N)
    ∃ α : (N ⧸ pCore 2 N) →* MulAut Z,
      (∀ (c : N) (z : Z), (α (q c) z : G) = (c : G) * z * (c : G)⁻¹) ∧
      α.ker = I.map q ∧ Group.IsSolvable (MulAut Z) := by
  let Z := ZS (T : Subgroup G) L R
  let N := Escape.H (T : Subgroup G) L R
  have hk : pCore 2 N ≤ Z.normalizerMonoidHom.ker := by
    rw [Z.normalizerMonoidHom_ker]
    exact (natural_four_ambient_quotient_cubic h hnat).1
  let α := QuotientGroup.lift (pCore 2 N) Z.normalizerMonoidHom hk
  refine ⟨α,fun _ _ => rfl,?_,?_⟩
  · exact (QuotientGroup.ker_lift (pCore 2 N) Z.normalizerMonoidHom hk).trans
      (congrArg (map (QuotientGroup.mk' (pCore 2 N))) Z.normalizerMonoidHom_ker)
  · let := h.ZS_elementary
    let : Nontrivial Z := (nontrivial_iff_ne_bot _).mpr h.ZS_ne_bot
    let : IsKleinFour Z := ⟨(hnat.sylow_intersection_geometry T h.sylow_normalizes_L).1,
      IsElementaryAbelian.exponent_eq_prime⟩
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
      Group.isSolvable_of_isSolvable_injective
        (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
    exact Group.isSolvable_of_isSolvable_injective
      (f := (IsKleinFour.autEquivPermThree Z).toMonoidHom)
      (IsKleinFour.autEquivPermThree Z).injective

/-- Every perfect subgroup of the ambient quotient lies in the original
centralizer image; this supplies containment for every ordinary component. -/
theorem natural_four_quotient_perfect_le_centralizer
    (h : Hypothesis611 κ T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup (Escape.H (T : Subgroup G) L R ⧸ pCore 2 (Escape.H (T : Subgroup G) L R)))
    [Group.IsPerfect K] :
    K ≤ ((Escape.I (T : Subgroup G) L R).subgroupOf
      (Escape.H (T : Subgroup G) L R)).map (QuotientGroup.mk' _) := by
  obtain ⟨α,_,hker,hsol⟩ := natural_four_quotient_line_action h hnat
  let := hsol
  have hz : K.map α = ⊥ := by
    let := Group.IsPerfect.map α (H := K)
    by_contra hne
    let : Nontrivial (K.map α) := (nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable (K.map α) inferInstance
  rw [←hker]
  exact (Subgroup.map_eq_bot_iff _).mp hz

/-- The original outside cubic excludes three-rank two for a component
with prime-to-three center and two-group outer automorphism quotient. -/
theorem natural_four_quotient_component_rank
    (h : Hypothesis611 κ T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup (Escape.H (T : Subgroup G) L R ⧸ pCore 2 (Escape.H (T : Subgroup G) L R)))
    (hK : IsComponent _ K)
    (hz : Nat.Coprime 3 (Nat.card (center K)))
    (ho : IsPGroup 2 (MulAut.Outer (K ⧸ center K))) :
    primeRank 3 K ≤ 1 := by
  obtain ⟨_,hr,c,_,_,_,hc,hout⟩ := natural_four_ambient_quotient_cubic h hnat
  by_contra hn
  have htwo : 2 ≤ primeRank 3 K := by omega
  have he := (Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual_of_outer_twoGroup
    hK hz htwo hr (MulEquiv.refl _) (by decide) ho).1
  let := hK.2
  apply hout
  apply natural_four_quotient_perfect_le_centralizer h hnat K
  rw [he]
  exact subset_closure hc

/-- An alternating component of degree at least six would contain the
original outside cubic, contradicting its action on Z_S. -/
theorem natural_four_quotient_component_not_alternating
    (h : Hypothesis611 κ T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup (Escape.H (T : Subgroup G) L R ⧸ pCore 2 (Escape.H (T : Subgroup G) L R)))
    (hK : IsComponent _ K) {m : ℕ} (hm : 6 ≤ m) :
    ¬ Chapter1.Section02.LocalModels.IsAlternating K m := by
  intro hmodel
  obtain ⟨_,hr,c,_,_,_,hc,hout⟩ := natural_four_ambient_quotient_cubic h hnat
  let := hK.2
  apply hout
  apply natural_four_quotient_perfect_le_centralizer h hnat K
  exact ChapterA.Section03.OddPrime.SourceModels.AlternatingCubics.cubic_mem_of_alternating_component
    hK hm hmodel hr hc

/-- The actual triple covers of A₆ and A₇ are excluded by the same cubic,
without replacing their nontrivial centers by a centerless model. -/
theorem natural_four_quotient_component_not_alternating_cover
    (h : Hypothesis611 κ T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup (Escape.H (T : Subgroup G) L R ⧸ pCore 2 (Escape.H (T : Subgroup G) L R)))
    (hK : IsComponent _ K) :
    ¬ (Chapter1.Section02.LocalModels.IsAlternatingCover K 6 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover K 7) := by
  intro hmodel
  obtain ⟨_,hr,c,_,_,_,hc,hout⟩ := natural_four_ambient_quotient_cubic h hnat
  let := hK.2
  apply hout
  apply natural_four_quotient_perfect_le_centralizer h hnat K
  exact ChapterA.Section03.OddPrime.SourceModels.AlternatingCubics.cubic_mem_of_alternating_cover_component
    hK (MulEquiv.refl K) hmodel hr hc

private theorem binary_outer_two {m : ℕ} (hm : m = 4 ∨ m = 5) :
    IsPGroup 2 (MulAut.Outer (BinaryLinear.OuterCyclic.LinearGroup m)) := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (BinaryLinear.OuterCyclic.LinearGroup m))
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨g,hg⟩ := BinaryLinear.OuterCyclic.inner_graph hm a
  have hi : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
  refine ⟨1,?_⟩
  change (q a)^2=1
  rcases hg with rfl | rfl
  · rw [hi,one_pow]
  · rw [map_mul,hi,mul_one,←map_pow,BinaryLinear.OuterCyclic.graphLinear_sq,map_one]

/-- The binary degree-four and degree-five component quotients are excluded
when the component center has order prime to three. -/
theorem natural_four_quotient_component_not_binary_cover
    (h : Hypothesis611 κ T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup (Escape.H (T : Subgroup G) L R ⧸ pCore 2 (Escape.H (T : Subgroup G) L R)))
    (hK : IsComponent _ K) (hz : Nat.Coprime 3 (Nat.card (center K)))
    {m : ℕ} (hm : m = 4 ∨ m = 5) :
    ¬ Nonempty ((K ⧸ center K) ≃* BinaryLinear.OuterCyclic.LinearGroup m) := by
  rintro ⟨e⟩
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup m) := Finite.of_surjective e e.surjective
  have hr := natural_four_quotient_component_rank h hnat K hK hz
    ((binary_outer_two hm).of_equiv (MulAut.outerCongr e).symm)
  have hq : primeRank 3 (K ⧸ center K) ≤ primeRank 3 K :=
    primeRank_le_of_surjective_of_coprime 3 (QuotientGroup.mk' (center K))
      (QuotientGroup.mk'_surjective _) (by simpa only [QuotientGroup.ker_mk'] using hz)
  have hlo := BinaryLinear.SmallCubicRank.four_or_five hm
  rw [primeRank_equiv 3 (BinaryLinear.OuterCyclic.slEquivLinear m),
    ←primeRank_equiv 3 e] at hlo
  omega

/-- In particular, neither actual GL₄(2) nor GL₅(2) can be an ordinary
component of this normalizer quotient. -/
theorem natural_four_quotient_component_not_binary_large
    (h : Hypothesis611 κ T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup (Escape.H (T : Subgroup G) L R ⧸ pCore 2 (Escape.H (T : Subgroup G) L R)))
    (hK : IsComponent _ K) {m : ℕ} (hm : m = 4 ∨ m = 5) :
    ¬ Nonempty (K ≃* BinaryLinear.OuterCyclic.LinearGroup m) := by
  rintro ⟨e⟩
  let eSL := e.trans (BinaryLinear.OuterCyclic.slEquivLinear m).symm
  have hc : center K = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hh : eSL z ∈ center (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) :=
      (centerCongr eSL ⟨z,hz⟩).property
    rw [BinaryLinear.OuterCyclic.binary_center_eq_bot (by omega),mem_bot] at hh
    exact eSL.map_eq_one_iff.mp hh
  let eQ : (K ⧸ center K) ≃* BinaryLinear.OuterCyclic.LinearGroup m :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e
  exact natural_four_quotient_component_not_binary_cover h hnat K hK
    (by rw [hc]; simp) hm ⟨eQ⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
