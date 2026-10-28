module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourCatalogue
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.PrimeBounds.SuzukiModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.ModelThreeDivisibility
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.GroupTheory.GeneralizedFitting.Solvable

/-!
# Ordinary components in the extraspecial four-group centralizer

For every strict overgroup of H ∩ C_G(x) inside C_G(x), the original
U = [U,K] centralizes its odd core. The marked involution then places that
core in H, where the subnormal-subgroup reduction forces it into O₂.
Thus the odd core vanishes. A solvable such overgroup would have
F* = O₂, contrary to the proved characteristic-two maximality.

A Suzuki component produces a solvable Borel extension of the original
intersection. Its odd torus has order 2^(2m+1)-1, impossible in the
{2,3}-group H. Every ordinary component therefore has order divisible by
three. It is normal and contains L₁; its centralizer normalizes L₁ and
hence lies in H, so the same subnormal reduction identifies that
centralizer with the actual O₂(C_G(x)). Perfectness lifts centralizers
through the two-core quotient.

The literal quotient action consequently has exactly that two-core as
kernel. Its image contains the inner group and the original faithful
Heisenberg subgroup; the local image is solvable of odd index and retains
its Heisenberg residual. The alternating rows of 1.1.5 are impossible:
the triple covers conflict with the two-primary center, and the simple
rows have no faithful ternary Heisenberg automorphisms. Hence the original
marked involution acts by an inner automorphism of the ordinary component.
The final theorem applies this chain to the original escaping centralizer.

The remaining inner-action model exclusions, centralizer containment, TI
and subsequent reductions through 14.7.52 are not asserted here.
Source: Aschbacher–Smith, 14.7.26, printed p.1053, refs/quasithin.pdf;
1.1.5(3), printed pp.501–503, for the actual model/action alternatives.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Representation Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
private theorem extraspecial_H_prime_divisor
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {r : ℕ} (hr : r.Prime) (hd : r ∣ Nat.card F.H) : r = 2 ∨ r = 3 := by
  have two_prime {A : Type u} [Group A] [Finite A] (hA : IsPGroup 2 A)
      (hdA : r ∣ Nat.card A) : r = 2 := by
    obtain ⟨n,hn⟩ := hA.exists_card_eq
    rw [hn] at hdA
    exact ((Nat.dvd_prime Nat.prime_two).mp (hr.dvd_of_dvd_pow hdA)).resolve_left hr.ne_one
  have hcH := (pResidual 2 F.H).card_mul_index
  rw [←hcH] at hd
  rcases hr.dvd_mul.mp hd with hR | hQ
  · have hK : r ∣ Nat.card (K F) := by
      change r ∣ Nat.card ((pResidual 2 F.H).map F.H.subtype)
      rw [card_map_of_injective F.H.subtype_injective]
      exact hR
    have hcK := (pCore 2 (K F)).card_mul_index
    rw [←hcK] at hK
    rcases hr.dvd_mul.mp hK with hcore | hquot
    · exact Or.inl (two_prime (pCore_isPGroup (p := 2) (G := K F)) hcore)
    · obtain ⟨e⟩ := he
      change r ∣ Nat.card ((K F) ⧸ pCore 2 (K F)) at hquot
      rw [Nat.card_congr e.toEquiv,HeisenbergPrime.card] at hquot
      exact Or.inr (((Nat.dvd_prime Nat.prime_three).mp
        (hr.dvd_of_dvd_pow hquot)).resolve_left hr.ne_one)
  · change r ∣ Nat.card (F.H ⧸ pResidual 2 F.H) at hQ
    exact Or.inl (two_prime (isPGroup_quotient_pResidual (G := F.H) 2) hQ)


/-- The actual odd core vanishes in every strict overgroup of the original local intersection inside the involution centralizer. -/
theorem extraspecial_four_overgroup_oddCore_eq_bot
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    : pPrimeCore 2 G₀ = ⊥ := by
  let C := centralizer ({x} : Set G)
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨hC,_,z,hzo,hzpow,P,hP,h115⟩ := extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  have hKC : K F ≤ C := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hk)
  have hKG : K F ≤ G₀ := (le_inf (K_le_H F) hKC).trans hJG.le
  have hUG : F.U ≤ G₀ :=
    ((span_le_residual_core h hab).trans (pCoreIn_le 2 (K F))).trans hKG
  have hG : IsSQTK KnownSimple.IsKnownSimple G₀ :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hGC)).mp
      (hC.subgroup (G₀.subgroupOf C))
  let : IsElementaryAbelian 2 (F.U.subgroupOf G₀) := IsElementaryAbelian.subgroupOf hUG
  have hp : IsPPerfect 2 ((K F).subgroupOf G₀) := (K_twoPerfect F).of_surjective
    (subgroupOfEquivOfLe hKG).symm.toMonoidHom (subgroupOfEquivOfLe hKG).symm.surjective
  have hcomm : ⁅F.U.subgroupOf G₀,(K F).subgroupOf G₀⁆ = F.U.subgroupOf G₀ := by
    apply map_injective G₀.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hUG,map_subgroupOf_eq_of_le hKG,commutator_U h F]
  have hcent := commutator_eq_bot_iff_le_centralizer.mp
    (ChapterA.lemma_A_1_26_1_of_stronglyQuasithin hG.stronglyQuasithin
      ((K F).subgroupOf G₀) (F.U.subgroupOf G₀) hp hcomm)
  have hzU : z ∈ F.U := ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))
    (hzpow ▸ mem_zpowers z)
  have hNH : (pPrimeCore 2 G₀).map G₀.subtype ≤ F.H := by
    rintro _ ⟨r,hr,rfl⟩
    have hcentral : z * (r : G) = (r : G) * z :=
      (congrArg Subtype.val (hcent (show (⟨z,hUG hzU⟩ : G₀) ∈ F.U.subgroupOf G₀ from hzU) r hr)).symm
    exact h115.centralizer_le (mem_centralizer_singleton_iff.mpr hcentral.symm)
  have h3 := extraspecial_four_threeCore_eq_bot
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC
  have hle : pPrimeCore 2 G₀ ≤ pCore 2 G₀ :=
    le_twoCore_of_subnormal_two_three h3 _
      (inferInstance : (pPrimeCore 2 G₀).Normal).isSubnormal (by
        intro p hp hd
        exact extraspecial_H_prime_divisor he hp (hd.trans (card_dvd_of_injective
          ((inclusion hNH).comp ((pPrimeCore 2 G₀).equivMapOfInjective G₀.subtype
            G₀.subtype_injective).toMonoidHom)
          ((inclusion_injective hNH).comp
            ((pPrimeCore 2 G₀).equivMapOfInjective G₀.subtype G₀.subtype_injective).injective))))
  have hp2 : IsPGroup 2 (pPrimeCore 2 G₀) := pCore_isPGroup.to_le hle
  rcases hp2.card_eq_or_dvd with h1 | hd
  · exact (eq_bot_iff_card _).mpr h1
  · exact ((Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card) hd).elim

/-- The original local intersection is maximal among solvable subgroups of the involution centralizer. -/
theorem extraspecial_four_solvable_overgroup_eq
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) ≤ G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hs : Group.IsSolvable G₀) : G₀ = F.H ⊓ centralizer ({x} : Set G) := by
  by_contra hne
  have hlt := lt_of_le_of_ne hJG (Ne.symm hne)
  have hout : ¬ centralizer ({x} : Set G) ≤ F.H := by
    intro hCH
    exact hlt.not_ge (le_inf (hGC.trans hCH) hGC)
  have ho := extraspecial_four_overgroup_oddCore_eq_bot
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hlt hGC
  let := hs
  have hf : generalizedFitting G₀ = pCore 2 G₀ :=
    (generalizedFitting_eq_fitting_of_solvable G₀).trans (Fitting_eq_pcore G₀ 2 ho)
  exact extraspecial_four_overgroup_not_characteristicTwo
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hlt hGC hf

/-- The literal Suzuki Borel extension contradicts solvable maximality of the original intersection. -/
theorem extraspecial_four_not_suzuki_component
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B)
    {m : ℕ} (hm : 0 < m)
    (e : B ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False := by
  let C := centralizer ({x} : Set G)
  let M := F.H.subgroupOf C
  obtain ⟨_,_,_,_,_,P,hP,_⟩ := extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  have hPM : (P : Subgroup C) ≤ M := by
    intro a ha
    have hh : (a : G) ∈ (T : Subgroup G) ⊓ C := hP ▸ mem_map_of_mem C.subtype ha
    exact F.invariant 1 hh.1
  have hsol : Group.IsSolvable F.H := isSolvable_of_prime_dvd_card_eq_two_or_three F.H
    (fun p hp hd => extraspecial_H_prime_divisor he hp hd)
  let := hsol
  let f : M →* F.H := (C.subtype.comp M.subtype).codRestrict F.H (fun a => a.property)
  have hf : Function.Injective f := by
    intro a b hh
    exact Subtype.ext (Subtype.ext (show ((a : C) : G) = ((b : C) : G) from
      congrArg (fun y : F.H => (y : G)) hh))
  have hMsol : Group.IsSolvable M := Group.isSolvable_of_isSolvable_injective hf
  obtain ⟨A,hMA,hAs,hd⟩ := Chapter14.Section06.OddNormalizer.suzuki_component_solvable_extension
    P M B hPM hMsol hB.isCComponent hm e
  let G₀ := A.map C.subtype
  have hJG : F.H ⊓ C ≤ G₀ := by
    intro a ha
    exact ⟨⟨a,ha.2⟩,hMA ha.1,rfl⟩
  let := hAs
  have heq : G₀ = F.H ⊓ C := extraspecial_four_solvable_overgroup_eq
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ
    G₀ hJG (map_subtype_le A) (Group.isSolvable_of_surjective (C.subtype.subgroupMap_surjective A))
  have hdiv : 2 ^ (2*m+1) - 1 ∣ Nat.card F.H := by
    have hc : Nat.card A = Nat.card G₀ := (card_map_of_injective C.subtype_injective).symm
    exact (hc ▸ hd).trans (card_dvd_of_le (heq.le.trans inf_le_left))
  have hq : 8 ≤ 2 ^ (2*m+1) := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 3 ≤ 2*m+1)
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ (2*m+1) - 1 ≠ 1 by omega)
  rcases extraspecial_H_prime_divisor he hp (hpd.trans hdiv) with rfl | rfl
  · have hmod : 2 ^ (2*m+1) % 2 = 0 := by simp [pow_add]
    have hmod' := Nat.mod_eq_zero_of_dvd hpd
    omega
  · have hmod : 2 ^ (2*m+1) % 3 = 2 := by
      simp [pow_add,pow_mul,Nat.mul_mod,Nat.pow_mod]
    have hmod' := Nat.mod_eq_zero_of_dvd hpd
    omega

/-- Every ordinary component of the original centralizer has order divisible by three. -/
theorem extraspecial_four_ordinary_three_dvd
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B) : 3 ∣ Nat.card B := by
  obtain ⟨_,_,z,_,_,P,_,h115⟩ := extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  obtain ⟨_,_,α,_,hmodel⟩ := Chapter1.lemma_1_1_5_three_knownSimple d.qtke
    (centralizer ({x} : Set G)) P F.H z h115 B hB
  rcases Chapter15.Section03.Candidates.SuzukiExclusion.ModelThreeDivisibility.suzuki_or_three_dvd
      α hmodel with ⟨m,hm,⟨e⟩⟩ | hd
  · exact (extraspecial_four_not_suzuki_component
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ B hB hm e).elim
  · exact hd

/-- The ordinary component is normal, contains the original L₁, and has exactly O₂(C_G(x)) as centralizer. Its literal two-core quotient has trivial centralizer in C_G(x)/O₂(C_G(x)). -/
theorem extraspecial_four_ordinary_structure
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B) :
    B.Normal ∧ F.Li L 1 ≤ B.map (centralizer ({x} : Set G)).subtype ∧
      centralizer (B : Set (centralizer ({x} : Set G))) = pCore 2 (centralizer ({x} : Set G)) ∧
      center B = pCore 2 B ∧ IsSimpleGroup (B ⧸ pCore 2 B) ∧
      centralizer (B.map (QuotientGroup.mk' (pCore 2 (centralizer ({x} : Set G)))) :
        Set ((centralizer ({x} : Set G)) ⧸ pCore 2 (centralizer ({x} : Set G)))) = ⊥ := by
  let C := centralizer ({x} : Set G)
  have hstrict : F.H ⊓ C < C :=
    lt_of_le_of_ne inf_le_right (fun heq => hout (heq.symm.trans_le inf_le_left))
  have hd := extraspecial_four_ordinary_three_dvd
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ B hB
  have hnormal : B.Normal := extraspecial_four_component_normal
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    C hstrict le_rfl B hB.isCComponent hd
  let := hnormal
  have hLB := extraspecial_four_component_contains_point
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
    C inf_le_right le_rfl B hB.isCComponent hd
  have hNK := (extraspecial_source_14721 d h hab structural previous faithful earlier he).1
  have hNpoint : normalizer (F.Li L 1 : Set G) = F.H :=
    (extraspecial_core_normalizer_eq d h hab structural previous faithful he).2.trans hNK
  let Z := centralizer (B : Set C)
  have hZH : Z.map C.subtype ≤ F.H := by
    rintro _ ⟨c,hc,rfl⟩
    rw [←hNpoint]
    apply Subgroup.centralizer_le_normalizer (F.Li L 1 : Set G)
    intro l hl
    obtain ⟨b,hb,rfl⟩ := hLB hl
    exact congrArg Subtype.val (hc b hb)
  have h3 := extraspecial_four_threeCore_eq_bot
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    C hstrict le_rfl
  have hZle : Z ≤ pCore 2 C := le_twoCore_of_subnormal_two_three h3 Z
    (inferInstance : Z.Normal).isSubnormal (by
      intro p hp hpZ
      have hd : p ∣ Nat.card (Z.map C.subtype) := by
        rwa [card_map_of_injective C.subtype_injective]
      exact extraspecial_H_prime_divisor he hp (hd.trans (card_dvd_of_le hZH)))
  let : Group.IsNilpotent (pCore 2 C) := pCore_isPGroup.isNilpotent
  have hCle : pCore 2 C ≤ Z := le_centralizer_iff.mp
    (hB.le_centralizer_of_solvable_normal (pCore 2 C))
  have hZ : Z = pCore 2 C := le_antisymm hZle hCle
  let : IsQuasisimple B := hB.2
  have ho := extraspecial_four_oddCore_eq_bot
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  have hz : center B = pCore 2 B := IsQuasisimple.center_eq_pCore (hB.1.pPrimeCore_eq_bot ho)
  have hs : IsSimpleGroup (B ⧸ pCore 2 B) := by
    let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
    exact (QuotientGroup.quotientMulEquivOfEq hz.symm).isSimpleGroup
  refine ⟨hnormal,hLB,hZ,hz,hs,?_⟩
  let q := QuotientGroup.mk' (pCore 2 C)
  apply (comap_injective (QuotientGroup.mk'_surjective (pCore 2 C)))
  rw [comap_centralizer_map_eq_of_perfect q B (by
    rw [QuotientGroup.ker_mk']; exact hCle)]
  change Z = q.ker
  rw [QuotientGroup.ker_mk']
  exact hZ

/-- The literal action of C_G(x) on the surviving ordinary component quotient has exactly the two-core as kernel. The original local image is solvable of odd index, with its marked Heisenberg residual and faithful original Heisenberg subgroup. -/
theorem extraspecial_four_ordinary_action
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B) :
    ∃ hn : B.Normal, letI := hn
      let a := normalQuotientAction B (pCore 2 B)
      let M := (F.H ⊓ centralizer ({x} : Set G)).subgroupOf (centralizer ({x} : Set G))
      let J := M.map a.rangeRestrict
      a.ker = pCore 2 (centralizer ({x} : Set G)) ∧
        MulAut.innerSubgroup (B ⧸ pCore 2 B) ≤ a.range ∧
        primeRank 3 a.range ≤ 2 ∧ Group.IsSolvable J ∧ Odd J.index ∧
        Nonempty (pResidual 2 (J ⧸ pCore 2 J) ≃* HeisenbergPrime 3) ∧
        ∃ f : HeisenbergPrime 3 →* a.range, Function.Injective f ∧ ∀ y, f y ∈ J := by
  have hsB := extraspecial_four_ordinary_structure
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  have hn : B.Normal := hsB.1
  let := hn
  refine ⟨hn,?_⟩
  let C := centralizer ({x} : Set G)
  let H₀ := F.H ⊓ C
  let M := H₀.subgroupOf C
  let a := normalQuotientAction B (pCore 2 B)
  let J := M.map a.rangeRestrict
  have hk : a.ker = pCore 2 C := hB.isCComponent.normalQuotientAction_ker_of_centralizer_eq_bot hsB.2.2.2.2.2
  have setup := extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  have hC := setup.1
  have hz := setup.2.2.choose_spec
  let P := hz.2.2.choose
  have hP := hz.2.2.choose_spec.1
  have hi : MulAut.innerSubgroup (B ⧸ pCore 2 B) ≤ a.range := by
    rintro _ ⟨z,rfl⟩
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) z
    exact ⟨b,normalQuotientAction_inner B (pCore 2 B) b⟩
  have hr : primeRank 3 a.range ≤ 2 := by
    rw [←primeRank_equiv 3 (QuotientGroup.quotientKerEquivRange a)]
    exact (primeRank_quotient_le_of_isTwoGroup 3 (by decide) a.ker
      (hk.symm ▸ pCore_isPGroup)).trans (hC.stronglyQuasithin 3 (by decide) (by decide))
  have hsol : Group.IsSolvable F.H := isSolvable_of_prime_dvd_card_eq_two_or_three F.H
    (fun p hp hd => extraspecial_H_prime_divisor he hp hd)
  let := hsol
  let φ : M →* F.H := (C.subtype.comp M.subtype).codRestrict F.H (fun y => y.property.1)
  have hφ : Function.Injective φ := by
    intro y z hh
    exact Subtype.ext (Subtype.ext (show ((y : C) : G) = ((z : C) : G) from
      congrArg (fun w : F.H => (w : G)) hh))
  let : Group.IsSolvable M := Group.isSolvable_of_isSolvable_injective hφ
  have hs : Group.IsSolvable J := Group.isSolvable_of_surjective (a.rangeRestrict.subgroupMap_surjective M)
  have hPM : (P : Subgroup C) ≤ M := by
    intro y hy
    have hh : (y : G) ∈ (T : Subgroup G) ⊓ C := hP ▸ mem_map_of_mem C.subtype hy
    exact ⟨F.invariant 1 hh.1,hh.2⟩
  have hodd : Odd M.index := Nat.not_even_iff_odd.mp (fun heven =>
    P.not_dvd_index (((even_iff_two_dvd).mp heven).trans (index_dvd_of_le hPM)))
  have ho : Odd J.index := hodd.of_dvd_nat (M.index_map_dvd a.rangeRestrict_surjective)
  have hres : Nonempty (pResidual 2 (J ⧸ pCore 2 J) ≃* HeisenbergPrime 3) := by
    let f : H₀ →* J := (a.rangeRestrict.subgroupMap M).comp
      (subgroupOfEquivOfLe (show H₀ ≤ C from inf_le_right)).symm.toMonoidHom
    have hf : Function.Surjective f := (a.rangeRestrict.subgroupMap_surjective M).comp
      (subgroupOfEquivOfLe (show H₀ ≤ C from inf_le_right)).symm.surjective
    have hkf : f.ker = (pCore 2 C).comap (inclusion (show H₀ ≤ C from inf_le_right)) := by
      ext j
      change f j = 1 ↔ inclusion (show H₀ ≤ C from inf_le_right) j ∈ pCore 2 C
      rw [Subtype.ext_iff,Subtype.ext_iff]
      change inclusion (show H₀ ≤ C from inf_le_right) j ∈ a.ker ↔ _
      rw [hk]
    have hpf : IsPGroup 2 f.ker := by
      rw [hkf]
      exact pCore_isPGroup.comap_of_injective _ (inclusion_injective inf_le_right)
    exact extraspecial_four_image_residual he hDK hx f hf hpf
  refine ⟨hk,hi,hr,hs,ho,hres,?_⟩
  have hY := extraspecial_four_three_sylow_center
    d h hab structural previous faithful earlier he
  let Y := hY.choose
  have hYK := hY.choose_spec.1
  let e := Classical.choice hY.choose_spec.2.2.2.1
  have hKC : K F ≤ C := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hkk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hkk)
  have hYH : Y ≤ H₀ := hYK.trans (le_inf (K_le_H F) hKC)
  have hYC : Y ≤ C := hYH.trans inf_le_right
  have hYp : IsPGroup 3 Y := IsPGroup.of_card (n := 3)
    ((Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)))
  have hcop : Nat.Coprime 3 (Nat.card a.ker) := by
    rw [hk]
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := C)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hinj : Function.Injective (a.comp (inclusion hYC)) :=
    (injective_comp_subtype_of_coprime_ker a hcop (Y.subgroupOf C) hYp.comap_subtype).comp
      (subgroupOfEquivOfLe hYC).symm.injective
  let f := (a.rangeRestrict.comp (inclusion hYC)).comp e.symm.toMonoidHom
  refine ⟨f,?_,?_⟩
  · intro y z hh
    exact e.symm.injective (hinj (congrArg Subtype.val hh))
  · intro y
    exact ⟨inclusion hYC (e.symm y),hYH (e.symm y).property,rfl⟩

private theorem ordinary_alternating_false
    {A : Type*} [Group A] [Finite A]
    (hc : center A = pCore 2 A) {α : MulAut A} {n : ℕ}
    (hn : n = 6 ∨ n = 7) (σ : Equiv.Perm (Fin n))
    (ha : Chapter15.Section03.Candidates.ComponentStructure.AlternatingAction α n σ)
    (f : HeisenbergPrime 3 →* MulAut (A ⧸ pCore 2 A)) (hf : Function.Injective f) : False := by
  rcases ha with ⟨e,_⟩ | ⟨_,⟨ez⟩,_,_⟩
  · have hn4 : 4 ≤ Nat.card (Fin n) := by simp only [Nat.card_fin]; omega
    have hzA : center (alternatingGroup (Fin n)) = ⊥ :=
      alternatingGroup.center_eq_bot hn4
    have hz : center A = ⊥ := (eq_bot_iff_card _).mpr (by
      rw [Nat.card_congr (centerCongr e).toEquiv,hzA,card_bot])
    let eQ : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin n) :=
      (QuotientGroup.quotientMulEquivOfEq (hc.symm.trans hz)).trans (QuotientGroup.quotientBot.trans e)
    exact HeisenbergPrime.SmallAutomorphismExclusions.no_alternating_action
      (by omega) eQ f hf
  · have hcard : Nat.card (pCore 2 A) = 3 := by
      rw [←hc,Nat.card_congr ez.toEquiv]
      simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]
    rcases (pCore_isPGroup (p := 2) (G := A)).card_eq_or_dvd with he | hd
    · omega
    · rw [hcard] at hd
      norm_num at hd

/-- The two alternating-action rows of 1.1.5 are impossible on the original component. Every surviving marked involution action is inner. -/
theorem extraspecial_four_ordinary_inner
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B)
    (z : G) (hm : Chapter15.Section03.Candidates.ComponentStructure.HasModelAction115 B z) :
    ∃ α : MulAut B, (∀ y : B, ((α y : centralizer ({x} : Set G)) : G) = z * (y : G) * z⁻¹) ∧
      α ∈ (MulAut.conj (G := B)).range ∧
      Chapter15.Section03.Candidates.ComponentStructure.ModelAction115 B α := by
  obtain ⟨_,_,_,hz,_,_⟩ := extraspecial_four_ordinary_structure
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  obtain ⟨hn,ha⟩ := extraspecial_four_ordinary_action
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  let := hn
  obtain ⟨_,_,_,_,_,_,f,hf,_⟩ := ha
  let f' := (normalQuotientAction B (pCore 2 B)).range.subtype.comp f
  have hf' : Function.Injective f' := Subtype.val_injective.comp hf
  obtain ⟨α,hα,hmodel⟩ := hm
  have hi : α ∈ (MulAut.conj (G := B)).range := by
    cases hmodel with
    | lie _ _ hi => exact hi
    | two_cover _ _ _ hi => exact hi
    | six σ _ a => exact (ordinary_alternating_false hz (Or.inl rfl) σ a f' hf').elim
    | seven σ _ a => exact (ordinary_alternating_false hz (Or.inr rfl) σ a f' hf').elim
    | odd _ hi => exact hi
    | sporadic _ _ _ hi => exact hi.1
  exact ⟨α,hα,hi,hmodel⟩

/-- Application to the original escaping centralizer: the marked ordinary component is normal, contains L₁, and its actual z-action is inner. -/
theorem extraspecial_four_ordinary_inner_source
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    : ∃ (B : Subgroup (centralizer ({x} : Set G))) (z : G),
      IsComponent (centralizer ({x} : Set G)) B ∧ B.Normal ∧
      F.Li L 1 ≤ B.map (centralizer ({x} : Set G)).subtype ∧
      orderOf z = 2 ∧ zpowers z = F.Vi 1 ∧
      B.map (centralizer ({x} : Set G)).subtype =
        ⁅B.map (centralizer ({x} : Set G)).subtype,zpowers z⁆ ∧
      ¬ B.map (centralizer ({x} : Set G)).subtype ≤ F.H ∧
      ∃ α : MulAut B, (∀ y : B, ((α y : centralizer ({x} : Set G)) : G) = z * (y : G) * z⁻¹) ∧
        α ∈ (MulAut.conj (G := B)).range ∧
        Chapter15.Section03.Candidates.ComponentStructure.ModelAction115 B α := by
  obtain ⟨B,z,hB,hz,hzp,hm,houtB,hmodel⟩ := extraspecial_four_ordinary_component
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
  obtain ⟨hn,hLB,_,_,_,_⟩ := extraspecial_four_ordinary_structure
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  exact ⟨B,z,hB,hn,hLB,hz,hzp,hm,houtB,extraspecial_four_ordinary_inner
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB z hmodel⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
