module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeSecondSupport
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.NaturalRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.LargePrimeGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeComponentCover
public import Theory.GroupAction.FiveSixteenCentralizer
public import Theory.GroupAction.IndependentCoprimeSupports
public import Theory.Representation.BinaryOffender.IrreducibleDiagonal
public import Theory.GroupTheory.SubgroupTransport
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimePointLiftSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeComponentCoverSource
public import Theory.GroupAction.ElementaryEightPointResidual.AmbientSylow
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCoreContainmentSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCoreContainment
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeSingleFactor
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCritical
public import Theory.Representation.SmallBinaryPrimeNormalizer.CubicInvolutions
public import Theory.GroupTheory.PGroup.OmegaAmbient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Baumann
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeSingleFusion
public import CFSG.Quasithin.Chapter14.Section03.Prelim.ThompsonSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeSingleThompson
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Factorization.SolvableThreePrime
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.NormalizedSupCard
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeSingleFactorSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCubicRadicalSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCubicRadical
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCubicSplittingSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCubicSplitting
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCubicCrossSource
public import Theory.GroupTheory.Commutator.SplitPair
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeExclusion
public import Theory.Representation.BinaryConjugationSection.NoTransvection

/-!
# Guarded large prime exclusion

This unit collects the indicated original source arguments at the same G,T.
Each constituent overview records its proof and source; the universal exports
remain unchanged. The larger unit avoids repeated loading of the common source
imports. Public mathematical statements and literal subgroup maps are retained.
-/

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The second quintic support fixed by the component Sylow intersection

For the original pair of canonical dihedral factors, the normalizer of one
factor normalizes the other. The literal five-residual of its full preimage
maps onto the marked order-five subgroup. The established component
commutator bound then makes the compatible Sylow intersection commute with
that five-subgroup in the original star quotient.

On its four-dimensional support the five-subgroup has centralizer of odd
order dividing fifteen. Thus the two-group image fixes this support. The
normal point cubic has no fixed vectors, so fixing this nonzero invariant
support also forces centralization of the cubic. The final commutator bound
uses the intrinsic two-core of the original point residual.

LargePrimeSecondSupportSource applies both conclusions to the same original
minimal local witness. The simultaneous-cubic alternative, Sylow enlargement
and ambient five-core contradiction remain open.
Source: Aschbacher–Smith, 14.7.6, printed pp.1044–1045, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
universe u
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source ChapterD
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne

private theorem LargePrimeSecondSupport_five_residual_of_ten {G : Type*} [Group G] [Finite G]
    (B P : Subgroup G) (hPB : P ≤ B) (hB : Nat.card B = 10) (hP : Nat.card P = 5) :
    (primeToResidual 5 B).map B.subtype = P := by
  let P₀ := P.subgroupOf B
  have hc : Nat.card P₀ = 5 := (Nat.card_congr (subgroupOfEquivOfLe hPB).toEquiv).trans hP
  have hi : P₀.index = 2 := by
    have hh := P₀.card_mul_index
    rw [hc,hB] at hh
    omega
  let : P₀.Normal := normal_of_index_eq_two hi
  have he : primeToResidual 5 B = P₀ := le_antisymm
    (primeToResidual_le _ (by rw [hi]; decide))
    (le_primeToResidual_of_isPGroup (IsPGroup.of_card (n := 1) (by simpa using hc)))
  rw [he,map_subgroupOf_eq_of_le hPB]

private theorem LargePrimeSecondSupport_pair_factor_normalizer {G V : Type*} [Group G] [Finite G]
    [Group V] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V] [FaithfulSMul G V]
    (f : CanonicalFiveDihedralFamily (G := G) (V := V))
    (i j : smallSupportFactors G V 2) (hij : i ≠ j)
    (htwo : Nat.card (smallSupportFactors G V 2) = 2) :
    normalizer (f.factor i : Set G) ≤ normalizer (f.factor j : Set G) := by
  intro g hg
  have hi : smallSupportFactors_conjEquiv 2 g i = i :=
    f.factor_injective (by
      rw [←f.permuted]
      change (f.factor i).map (MulAut.conj g).toMonoidHom = f.factor i
      exact mem_normalizer_iff_map_conj_eq.mp hg)
  have hj : smallSupportFactors_conjEquiv 2 g j ≠ i := by
    rw [←hi]
    exact fun hh => hij ((smallSupportFactors_conjEquiv (V := V) 2 g).injective hh).symm
  obtain ⟨k,_,hk⟩ := (Nat.card_eq_two_iff' i).mp htwo
  have he : smallSupportFactors_conjEquiv 2 g j = j := (hk _ hj).trans (hk j hij.symm).symm
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (f.factor j).conjBy g = f.factor j
  rw [f.permuted,he]


private theorem LargePrimeSecondSupport_two_centralizer_fixes_five_support {G V : Type*} [Group G] [Finite G]
    [Group V] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V] [FaithfulSMul G V]
    (P B : Subgroup G) (hP : Nat.card P = 5)
    (hU : Nat.card (commutatorAction P V) = 16)
    (hB : IsPGroup 2 B) (hBP : B ≤ centralizer (P : Set G)) :
    commutatorAction P V ≤ FixedPoints.subgroup B V := by
  let N := normalizer (P : Set G)
  let U := commutatorAction P V
  let : IsInvariant N V U := commutatorAction_isInvariant_of_normalizing_actor N P le_rfl
  let φ : N →* MulAut U := MulDistribMulAction.toMulAut N U
  let ψ : P →* MulAut U := φ.comp (inclusion P.le_normalizer)
  have hcop : Nat.Coprime (Nat.card P) (Nat.card V) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hP,hn]
    exact (by decide : Nat.Coprime 5 2).pow_right n
  have hψ : Function.Injective ψ := by
    apply (injective_iff_map_eq_one ψ).mpr
    intro p hp
    apply Subtype.ext
    apply ActionSupport.eq_one_of_fixes_support P hcop p
    intro v hv
    exact congrArg Subtype.val (congrArg (fun f : MulAut U => f ⟨v,hv⟩) hp)
  have hψc : Nat.card ψ.range = 5 :=
    (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm.trans hP
  let B₀ := B.subgroupOf N
  have hBN : B ≤ N := hBP.trans (Subgroup.centralizer_le_normalizer _)
  have hcentral : B₀.map φ ≤ centralizer (ψ.range : Set (MulAut U)) := by
    rintro _ ⟨b,hb,rfl⟩ _ ⟨p,rfl⟩
    have he : (inclusion P.le_normalizer p) * b = b * (inclusion P.le_normalizer p) :=
      Subtype.ext (hBP hb p p.property)
    simpa only [ψ,MonoidHom.comp_apply,map_mul] using congrArg φ he
  have hd := card_centralizer_five_dvd_fifteen (V := U) ψ.range hψc hU
  have hp : IsPGroup 2 (B₀.map φ) := hB.comap_subtype.map φ
  have hdis : Disjoint (B₀.map φ) (centralizer (ψ.range : Set (MulAut U))) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hn]
    exact ((by decide : Nat.Coprime 2 15).of_dvd_right hd).pow_left n
  have hz : B₀.map φ = ⊥ := bot_unique ((le_inf le_rfl hcentral).trans hdis.le_bot)
  intro v hv b
  have hb : φ ⟨b,hBN b.property⟩ = 1 :=
    mem_bot.mp (hz ▸ mem_map_of_mem φ (show (⟨b,hBN b.property⟩ : N) ∈ B₀ from b.property))
  exact congrArg Subtype.val (congrArg (fun f : MulAut U => f ⟨v,hv⟩) hb)

private theorem LargePrimeSecondSupport_lifted_five_residual_image {G : Type*} [Group G] [Finite G]
    (I : Subgroup G) (B P : Subgroup (HStar I))
    (hPB : P ≤ B) (hB : Nat.card B = 10) (hP : Nat.card P = 5) :
    let K2 := (B.comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
    actorImage I ((primeToResidual 5 K2).map K2.subtype) = P := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let B₀ := B.comap q
  have hm : B₀.map q = B := map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) B
  have he := map_embedded_primeToResidual_of_hom 5 B₀ I.subtype
  change ((((primeToResidual 5 (B₀.map I.subtype)).map (B₀.map I.subtype).subtype).comap I.subtype).map q) = P
  rw [←he,comap_map_eq_self_of_injective I.subtype_injective,
    map_embedded_primeToResidual_of_hom 5 B₀ q,hm]
  exact LargePrimeSecondSupport_five_residual_of_ten B P hPB hB hP

private theorem LargePrimeSecondSupport_lift_normalizer_mono {G : Type*} [Group G] [Finite G]
    (I : Subgroup G) (A B : Subgroup (HStar I))
    (hn : normalizer (A : Set (HStar I)) ≤ normalizer (B : Set (HStar I))) :
    I ⊓ normalizer (((A.comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype) : Set G) ≤
      normalizer (((B.comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype) : Set G) := by
  let q := QuotientGroup.mk' (pCore 2 I)
  have hh : normalizer (A.comap q : Set I) ≤ normalizer (B.comap q : Set I) := by
    rw [←comap_normalizer_eq_of_surjective A (QuotientGroup.mk'_surjective _),
      ←comap_normalizer_eq_of_surjective B (QuotientGroup.mk'_surjective _)]
    exact comap_mono hn
  intro g hg
  have hgA : (⟨g,hg.1⟩ : I) ∈ normalizer (A.comap q : Set I) := by
    have he := subgroupOf_normalizer_eq (map_subtype_le (A.comap q))
    simp only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] at he
    exact he ▸ hg.2
  exact (B.comap q).le_normalizer_map I.subtype (mem_map_of_mem I.subtype (hh hgA))

private theorem LargePrimeSecondSupport_actor_commutes_of_two_commutator {G : Type*} [Group G] [Finite G]
    (I B D K : Subgroup G) (hBI : B ≤ I) (hKI : K ≤ I)
    (hBK : B ≤ normalizer (K : Set G))
    (hcomm : ⁅D,K⁆ ≤ D.pCoreIn 2)
    (hfive : IsPGroup 5 (actorImage I K)) :
    actorImage I (B ⊓ D) ≤ centralizer (actorImage I K : Set (HStar I)) := by
  have hE : ⁅B ⊓ D,K⁆ ≤ K :=
    le_normalizer_iff_commutator_le_right.mp (inf_le_left.trans hBK)
  have hE2 : IsPGroup 2 (⁅B ⊓ D,K⁆ : Subgroup G) :=
    (isPGroup_pCoreIn 2 D).to_le ((commutator_mono inf_le_right le_rfl).trans hcomm)
  have he2 : IsPGroup 2 (actorImage I ⁅B ⊓ D,K⁆) :=
    hE2.comap_subtype.map (QuotientGroup.mk' (pCore 2 I))
  have he5 : IsPGroup 5 (actorImage I ⁅B ⊓ D,K⁆) :=
    hfive.to_le (map_mono (comap_mono hE))
  have he : actorImage I ⁅B ⊓ D,K⁆ = ⊥ := by
    have hd := IsPGroup.disjoint_of_ne 2 5 (by decide)
      (actorImage I ⁅B ⊓ D,K⁆) (actorImage I ⁅B ⊓ D,K⁆) he2 he5
    exact bot_unique ((le_inf le_rfl le_rfl).trans hd.le_bot)
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [actorImage,actorImage,←map_commutator,
    ←Theory.GroupTheory.SubgroupTransport.subgroupOf_commutator _ _ (inf_le_left.trans hBI) hKI]
  exact he

/-- On the same canonical pair, the actual Sylow intersection with the covering
component fixes the other four-dimensional support under the original star action. -/
theorem local_other_factor_support_fixed
    {G : Type*} [Group G] [Finite G] {I U Z : Subgroup G}
    [IsElementaryAbelian 2 U] (a : LocalQuotientAction I U Z) :
    let := BinaryGroupAction.action a.representation
    ∀ (f : CanonicalFiveDihedralFamily (G := HStar I)
        (V := Multiplicative (Additive (U ⧸ Z.subgroupOf U))))
      (i j : smallSupportFactors (HStar I)
        (Multiplicative (Additive (U ⧸ Z.subgroupOf U))) 2)
      (A : Subgroup (HStar I)) (C : Subgroup G),
      i ≠ j →
      Nat.card (smallSupportFactors (HStar I)
        (Multiplicative (Additive (U ⧸ Z.subgroupOf U))) 2) = 2 →
      A ≤ f.factor i →
      C = Chapter14.Section06.OddNormalizer.supportPreimage a
        (subspaceCommutator a.representation ⊤ A) →
      ∀ (_ : IsElementaryAbelian 2 C), Nat.card C = 8 →
      IsSimpleQTKE KnownSimple.IsKnownSimple G →
      ∀ (D : Subgroup (normalizer (C : Set G))), D.IsCComponent →
        D.map C.normalizerMonoidHom = ⊤ →
        ∀ S : Sylow 2 G, (S : Subgroup G) ≤ I →
        let K1 := ((f.factor i).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
        let K2 := ((f.factor j).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
        let K0 := (primeToResidual 5 K2).map K2.subtype
        let T1 := (S : Subgroup G) ⊓ normalizer (K1 : Set G)
        let DA := D.map (normalizer (C : Set G)).subtype
        T1 ≤ normalizer (K0 : Set G) ∧ actorImage I K0 = j.val ∧
        actorImage I (T1 ⊓ DA) ≤ centralizer (j.val : Set (HStar I)) ∧
        subspaceCommutator a.representation ⊤ j.val ≤
          fixedSpace a.representation (actorImage I (T1 ⊓ DA)) := by
  intro _
  let := BinaryGroupAction.action a.representation
  intro f i j A C hij htwo hAi hC hCE hc hG D hD hm S hSI
  let W := Additive (U ⧸ Z.subgroupOf U)
  let : IsElementaryAbelian 2 (Multiplicative W) := BinaryGroupAction.elementary
  let : FaithfulSMul (HStar I) (Multiplicative W) :=
    BinaryGroupAction.faithful a.representation a.faithful
  let K1 := ((f.factor i).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
  let K2 := ((f.factor j).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
  let K0 := (primeToResidual 5 K2).map K2.subtype
  let T1 := (S : Subgroup G) ⊓ normalizer (K1 : Set G)
  let DA := D.map (normalizer (C : Set G)).subtype
  have hT1I : T1 ≤ I := inf_le_left.trans hSI
  have hT1K2 : T1 ≤ normalizer (K2 : Set G) :=
    (le_inf hT1I inf_le_right).trans (LargePrimeSecondSupport_lift_normalizer_mono I _ _
      (LargePrimeSecondSupport_pair_factor_normalizer f i j hij htwo))
  have hT1K0 : T1 ≤ normalizer (K0 : Set G) :=
    hT1K2.trans (normalizer_le_normalizer_characteristic_image K2 (primeToResidual 5 K2))
  have hK2c : Nat.card (f.factor j) = 10 := by
    obtain ⟨e⟩ := f.model j
    exact (Nat.card_congr e.toEquiv).trans (DihedralGroup.nat_card (n := 5))
  have hK0m : actorImage I K0 = j.val :=
    LargePrimeSecondSupport_lifted_five_residual_image I (f.factor j) j.val (f.contains j) hK2c j.property.2.1
  have hK0I : K0 ≤ I := (map_subtype_le _).trans (map_subtype_le _)
  obtain ⟨_,hcomm⟩ := local_other_factor_component_commutator a f i j A C hij hAi hC hCE hc hG D hD hm
  have hcent : actorImage I (T1 ⊓ DA) ≤ centralizer (j.val : Set (HStar I)) := by
    rw [←hK0m]
    exact LargePrimeSecondSupport_actor_commutes_of_two_commutator I T1 DA K0 hT1I hK0I hT1K0 hcomm
      (IsPGroup.of_card (n := 1) (by rw [hK0m,j.property.2.1]; rfl))
  have htwoActor : IsPGroup 2 (actorImage I (T1 ⊓ DA)) :=
    ((S.isPGroup'.to_le (inf_le_left.trans inf_le_left)).comap_subtype).map
      (QuotientGroup.mk' (pCore 2 I))
  have hfix := LargePrimeSecondSupport_two_centralizer_fixes_five_support (V := Multiplicative W) j.val
    (actorImage I (T1 ⊓ DA)) j.property.2.1 j.property.2.2 htwoActor hcent
  rw [BinaryGroupAction.commutator_eq,BinaryGroupAction.fixedPoints_eq] at hfix
  exact ⟨hT1K0,hK0m,hcent,BinaryGroupAction.submoduleEquivSubgroup.symm.monotone hfix⟩

private theorem LargePrimeSecondSupport_normal_prime_centralized_of_fixed_space
    {E W : Type*} [Group E] [Finite E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (P B : Subgroup E) [P.Normal]
    (hP : Nat.card P = 3) (hfix : fixedSpace ρ P = ⊥)
    (U : Submodule (ZMod 2) W) (hne : U ≠ ⊥)
    (hstable : P ≤ subspaceStabilizer ρ U) (hB : U ≤ fixedSpace ρ B) :
    B ≤ centralizer (P : Set E) := by
  have hc : ⁅P,B⁆ ≤ P := commutator_le_left P B
  have hd : Nat.card (⁅P,B⁆ : Subgroup E) ∣ 3 := hP ▸ card_dvd_of_le hc
  have he : ⁅P,B⁆ = ⊥ := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with hb | hp
    · exact eq_bot_of_card_eq _ hb
    · have hh : ⁅P,B⁆ = P := eq_of_le_of_card_ge hc (by rw [hP,hp])
      have hf := le_fixedSpace_commutator_of_invariant ρ hstable hB
      rw [hh,hfix] at hf
      exact (hne (bot_unique hf)).elim
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)

private theorem LargePrimeSecondSupport_commutator_le_core_of_actor_centralizes
    {G : Type*} [Group G] [Finite G] (I B P : Subgroup G)
    (hBI : B ≤ I) (hPI : P ≤ I) (hn : B ≤ normalizer (P : Set G))
    (hc : actorImage I B ≤ centralizer (actorImage I P : Set (HStar I))) :
    ⁅B,P⁆ ≤ P.pCoreIn 2 := by
  have hBP : ⁅B,P⁆ ≤ P := le_normalizer_iff_commutator_le_right.mp hn
  have he : actorImage I ⁅B,P⁆ = ⊥ := by
    rw [actorImage,Theory.GroupTheory.SubgroupTransport.subgroupOf_commutator _ _ hBI hPI,
      map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc
  have hcore : ⁅B,P⁆ ≤ I.pCoreIn 2 := by
    intro x hx
    have hxI := hPI (hBP hx)
    have hh : QuotientGroup.mk' (pCore 2 I) ⟨x,hxI⟩ = 1 :=
      mem_bot.mp (he ▸ mem_map_of_mem (QuotientGroup.mk' (pCore 2 I)) hx)
    exact mem_map.mpr ⟨⟨x,hxI⟩,(QuotientGroup.eq_one_iff _).mp hh,rfl⟩
  exact (le_inf hBP hcore).trans (inf_pCoreIn_le_of_le 2 hPI)

/-- The original point cubic and its intrinsic two-core quotient are centralized
by the same Sylow intersection, once the actual second support is fixed. -/
theorem local_point_centralized_of_other_support_fixed
    {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I : Subgroup G) (hLI : F.Li L 1 ≤ I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (P : Subgroup (HStar I))
    (h4 : Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ P) = 4)
    (hcent : actorImage I (F.Li L 1) ≤ centralizer (P : Set (HStar I)))
    (B : Subgroup G) (hBI : B ≤ I)
    (hfixed : subspaceCommutator a.representation ⊤ P ≤ fixedSpace a.representation (actorImage I B)) :
    actorImage I B ≤ centralizer (actorImage I (F.Li L 1) : Set (HStar I)) ∧
      ⁅B,F.Li L 1⁆ ≤ (F.Li L 1).pCoreIn 2 := by
  let Q := actorImage I (F.Li L 1)
  let : Q.Normal := Normal.map hn _ (QuotientGroup.mk'_surjective _)
  have hQ : Nat.card Q = 3 := local_point_star_card_of_normal h structural I hLI hn
  have hstable : Q ≤ subspaceStabilizer a.representation
      (subspaceCommutator a.representation ⊤ P) :=
    subspaceCommutator_invariant_normalizer a.representation
      (le_subspaceStabilizer _ ⊤ (by intros; trivial))
      (hcent.trans (Subgroup.centralizer_le_normalizer _))
  have hc := LargePrimeSecondSupport_normal_prime_centralized_of_fixed_space a.representation Q (actorImage I B)
    hQ (local_point_fixedSpace_eq_bot h structural I hLI hn a) _
    (fun he => by rw [he,finrank_bot] at h4; omega) hstable hfixed
  exact ⟨hc,LargePrimeSecondSupport_commutator_le_core_of_actor_centralizes I B (F.Li L 1) hBI hLI
    (hBI.trans ((normal_subgroupOf_iff_le_normalizer hLI).mp hn)) hc⟩


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original point preimage and a compatible Sylow normalizer

In the full-action two-factor branch, the original factor normalizer T₁
has index two in the compatible ambient Sylow S. Its image on the common
eight-group therefore has order divisible by four. Since it normalizes
the original point residual, that residual cannot have cubic image: a
cubic normalizer in GL₃(2) has two-part at most two. Its actual image is A₄.

Construct L₀ as the full preimage of this A₄ image inside the same normal
covering component D. Its action kernel includes the entire intersection
with C_G(C). The odd index of the A₄ normalizer then gives a Sylow subgroup
of N_G(C) containing the same T₁ and normalizing this literal L₀. The
second-support calculation and the original point-residual centralization
then force strict enlargement of T₁: otherwise its component intersection
would have image of order eight contained in A₄. Since T₁ has index two
in the original compatible S, the enlargement is an actual Sylow T_A of G.

The simultaneous-cubic branch remains explicit. Transport of the faithful
source hypotheses to T_A, ambient normalizer control and the final five-core
contradiction remain to be proved.
Source: Aschbacher–Smith 14.7.6, printed pp.1044–1045, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter12.Section08 CriticalFusion.Source ChapterD
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open scoped IsMulCommutative
universe u
open Chapter14.Section06.OddCriticalPair.Selection
open Theory.GroupAction.ElementaryEightPointResidual
open scoped Pointwise
/-- On the same original two-factor witness, construct the full A₄ point
preimage and its compatible Sylow normalizer, retaining the second support. -/
theorem local_minimal_five_point_preimage_control
    {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ I : Subgroup G, I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      pCore 5 (HStar I) ≠ ⊥ ∧
      (∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
        pCore 5 (HStar E) = ⊥) ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          let : IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
          ∃ hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis,
            ∃ c : SelectedQuadraticEndpoint hf a,
              c.endpoint.representative ∉ F.H ∧
              let A := actorImage I (c.endpoint.conjugate (F.UH I))
              let C := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
              let := BinaryGroupAction.action a.representation
              ∃ (f : CanonicalFiveDihedralFamily (G := HStar I)
                  (V := Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) )
                (i : smallSupportFactors (HStar I)
                  (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2),
                A ≤ f.factor i ∧ Nat.card A = 2 ∧
                C = Chapter14.Section06.OddNormalizer.supportPreimage a
                  (subspaceCommutator a.representation ⊤ A) ∧
                IsElementaryAbelian 2 C ∧ Nat.card C = 8 ∧
                F.Vi 1 ≤ C ∧ c.endpoint.conjugate (F.Vi 1) ≤ C ∧
                F.Vi 1 ≠ c.endpoint.conjugate (F.Vi 1) ∧
                ((I.pCoreIn 2 ≤ centralizer (C : Set G) ∧
                    (c.endpoint.conjugate I).pCoreIn 2 ≤ centralizer (C : Set G)) ∨
                  ∃ D : Subgroup (normalizer (C : Set G)),
                    D.IsCComponent ∧ D.Normal ∧ D.map C.normalizerMonoidHom = ⊤ ∧
                    D.map (normalizer (C : Set G)).subtype ⊔ centralizer (C : Set G) =
                      normalizer (C : Set G) ∧
                    (Nat.card (smallSupportFactors (HStar I)
                      (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 2 →
                      ∃ S : Sylow 2 G, (S : Subgroup G) ≤ I ∧
                        c.endpoint.conjugate (F.UH I) ≤ S ∧
                        (∃ x : I, S = (x : G)⁻¹ • T) ∧
                        let K1 := ((f.factor i).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
                        let T1 := (S : Subgroup G) ⊓ normalizer (K1 : Set G)
                        let DA := D.map (normalizer (C : Set G)).subtype
                        T1.relIndex (S : Subgroup G) = 2 ∧ T1 ≤ normalizer (C : Set G) ∧
                        (∃ P : Sylow 2 (I ⊓ normalizer (C : Set G) : Subgroup G),
                          (P : Subgroup (I ⊓ normalizer (C : Set G) : Subgroup G)).map
                            (I ⊓ normalizer (C : Set G)).subtype = T1) ∧
                        (∀ j : smallSupportFactors (HStar I)
                            (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2,
                          i ≠ j →
                          let K2 := ((f.factor j).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
                          let K0 := (primeToResidual 5 K2).map K2.subtype
                          T1 ≤ normalizer (K0 : Set G) ∧ actorImage I K0 = j.val ∧
                          actorImage I (T1 ⊓ DA) ≤ centralizer (j.val : Set (HStar I)) ∧
                          subspaceCommutator a.representation ⊤ j.val ≤
                            fixedSpace a.representation (actorImage I (T1 ⊓ DA))) ∧
                        actorImage I (T1 ⊓ DA) ≤
                          centralizer (actorImage I (F.Li L 1) : Set (HStar I)) ∧
                        ⁅T1 ⊓ DA,F.Li L 1⁆ ≤ (F.Li L 1).pCoreIn 2 ∧
                        conjugationImage (T1 ⊓ DA) C ≤ conjugationImage (F.Li L 1) C ∧
                        Nat.card (conjugationImage (F.Li L 1) C) = 12 ∧
                        Nonempty (conjugationImage (F.Li L 1) C ≃* alternatingGroup (Fin 4)) ∧
                        let L0 := D ⊓ (conjugationImage (F.Li L 1) C).comap C.normalizerMonoidHom
                        let L0G := L0.map (normalizer (C : Set G)).subtype
                        conjugationImage L0G C = conjugationImage (F.Li L 1) C ∧
                        (D ⊓ C.normalizerMonoidHom.ker).map (normalizer (C : Set G)).subtype ≤ L0G ∧
                        ∃ P : Sylow 2 (normalizer (C : Set G)),
                          T1 ≤ (P : Subgroup (normalizer (C : Set G))).map
                            (normalizer (C : Set G)).subtype ∧
                          (P : Subgroup (normalizer (C : Set G))).map
                            (normalizer (C : Set G)).subtype ≤ normalizer (L0G : Set G) ∧
                          ∃ TA : Sylow 2 G, (TA : Subgroup G) =
                            (P : Subgroup (normalizer (C : Set G))).map
                              (normalizer (C : Set G)).subtype)) := by
  obtain ⟨I,X,Y,hIJ,hI,hproper,hXn,hXp,hcore,hcard,hmin,hYn,hYp,hYle,
      hYm,hYk,he,hout,hgen,hs,hn,hpoint,hm,hU,a,hno,hf,hb,ho,c,houtc,hAP,hAX,
      hr,hAc,hAd,hCX,hW,hcomp,hden,hcan,f,i,hi,hfi,hXD,hPD,hfull,hpos,hcount,
      r,hlabels,hprod,hrr,hrd,hbase,hopp,hnepoints,hCU,hCB,hCE,hCc,himage,hdim,hpre,
      hLC,hLZ,hCS,hoppN,hoppZ,hfixed,hfixedOpp,himageB,himageOpp,
      hsupp,hsuppOpp,hindex,hpair,hcubic,hcubicOpp,hresult,hnormalizer⟩ :=
    local_minimal_five_full_cover_or_cubic_pair h hab structural previous J hJ hne
  let := hU
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  let := BinaryGroupAction.action a.representation
  let C := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
  have hAi : actorImage I (c.endpoint.conjugate (F.UH I)) ≤ f.factor i := by
    rw [hfi]
    exact le_sup_right
  have hCpre : C = Chapter14.Section06.OddNormalizer.supportPreimage a
      (subspaceCommutator a.representation ⊤ (actorImage I (c.endpoint.conjugate (F.UH I)))) := by
    simpa only [himage] using hpre
  have hIne : pCore 5 (HStar I) ≠ ⊥ := by
    intro hz
    rw [hcore,hz,card_bot] at hcard
    omega
  refine ⟨I,hIJ,hI,hIne,hproper,hU,a,hf,c,houtc,f,i,hAi,hAc,hCpre,hCE,hCc,
    hbase,hopp,hnepoints,?_⟩
  rcases hresult with hpairC | ⟨hfullC,heC,⟨D,hD,hmD,hjoin,hquot,hnD,hker,hmodel,hfree,hother⟩,hpoints⟩
  · exact Or.inl hpairC
  · refine Or.inr ⟨D,hD,hnD,hmD,hjoin,?_⟩
    intro htwo
    obtain ⟨S,hSI,hBS,hconj,hindexT,hindexS,hT1C,hIC,hSyl⟩ := hnormalizer htwo
    let K1 := ((f.factor i).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
    let T1 := (S : Subgroup G) ⊓ normalizer (K1 : Set G)
    let DA := D.map (normalizer (C : Set G)).subtype
    have hall := fun j hij => local_other_factor_support_fixed a f i j
      (actorImage I (c.endpoint.conjugate (F.UH I))) C hij htwo hAi hCpre hCE hCc
      h.source.simpleQTKE D hD hmD S hSI
    obtain ⟨j,hji,_⟩ := (Nat.card_eq_two_iff' i).mp htwo
    have hdimj : Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ j.val) = 4 := by
      have hh := j.property.2.2
      rw [BinaryGroupAction.commutator_card] at hh
      exact Nat.pow_right_injective (by decide : 1 < 2) hh
    have hPj : actorImage I (F.Li L 1) ≤ centralizer (j.val : Set (HStar I)) :=
      hPD.trans (centralizer_le ((f.contains j).trans (le_iSup f.factor j)))
    have hc := local_point_centralized_of_other_support_fixed h structural I
      (F.Li_one_le_of_mem_Hz hI) hn a j.val hdimj hPj
      (T1 ⊓ DA) (inf_le_left.trans (inf_le_left.trans hSI)) (hall j hji.symm).2.2.2
    let := hCE
    let := hnD
    have hT1B : T1 ≤ normalizer (F.Li L 1 : Set G) :=
      (inf_le_left.trans hSI).trans
        ((normal_subgroupOf_iff_le_normalizer (F.Li_one_le_of_mem_Hz hI)).mp hn)
    have hpointLift := point_preimage_ambient_sylow S T1 (F.Li L 1) C (F.Vi 1)
      inf_le_left hindexS hT1C hLC hT1B hCc hf.point_card hfixed himageB.1 D hmD hc.2
    have himageLe := conjugationImage_le_point_image (T1 ⊓ DA) (F.Li L 1) C (F.Vi 1)
      (inf_le_left.trans hT1C) hLC (inf_le_left.trans hT1B) hCc hf.point_card
      hfixed hpointLift.1 hc.2
    exact ⟨S,hSI,hBS,hconj,hindexS,hT1C,hSyl,hall,hc.1,hc.2,himageLe,hpointLift⟩

/-- On the same original two-factor witness, construct the full A₄ point
preimage and its compatible Sylow normalizer, retaining the second support. -/
theorem local_minimal_five_point_preimage
    {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ I : Subgroup G, I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      pCore 5 (HStar I) ≠ ⊥ ∧
      (∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
        pCore 5 (HStar E) = ⊥) ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          let : IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
          ∃ hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis,
            ∃ c : SelectedQuadraticEndpoint hf a,
              c.endpoint.representative ∉ F.H ∧
              let A := actorImage I (c.endpoint.conjugate (F.UH I))
              let C := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
              let := BinaryGroupAction.action a.representation
              ∃ (f : CanonicalFiveDihedralFamily (G := HStar I)
                  (V := Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) )
                (i : smallSupportFactors (HStar I)
                  (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2),
                A ≤ f.factor i ∧ Nat.card A = 2 ∧
                C = Chapter14.Section06.OddNormalizer.supportPreimage a
                  (subspaceCommutator a.representation ⊤ A) ∧
                IsElementaryAbelian 2 C ∧ Nat.card C = 8 ∧
                F.Vi 1 ≤ C ∧ c.endpoint.conjugate (F.Vi 1) ≤ C ∧
                F.Vi 1 ≠ c.endpoint.conjugate (F.Vi 1) ∧
                ((I.pCoreIn 2 ≤ centralizer (C : Set G) ∧
                    (c.endpoint.conjugate I).pCoreIn 2 ≤ centralizer (C : Set G)) ∨
                  ∃ D : Subgroup (normalizer (C : Set G)),
                    D.IsCComponent ∧ D.Normal ∧ D.map C.normalizerMonoidHom = ⊤ ∧
                    D.map (normalizer (C : Set G)).subtype ⊔ centralizer (C : Set G) =
                      normalizer (C : Set G) ∧
                    (Nat.card (smallSupportFactors (HStar I)
                      (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 2 →
                      ∃ S : Sylow 2 G, (S : Subgroup G) ≤ I ∧
                        c.endpoint.conjugate (F.UH I) ≤ S ∧
                        (∃ x : I, S = (x : G)⁻¹ • T) ∧
                        let K1 := ((f.factor i).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
                        let T1 := (S : Subgroup G) ⊓ normalizer (K1 : Set G)
                        let DA := D.map (normalizer (C : Set G)).subtype
                        T1.relIndex (S : Subgroup G) = 2 ∧ T1 ≤ normalizer (C : Set G) ∧
                        (∃ P : Sylow 2 (I ⊓ normalizer (C : Set G) : Subgroup G),
                          (P : Subgroup (I ⊓ normalizer (C : Set G) : Subgroup G)).map
                            (I ⊓ normalizer (C : Set G)).subtype = T1) ∧
                        (∀ j : smallSupportFactors (HStar I)
                            (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2,
                          i ≠ j →
                          let K2 := ((f.factor j).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
                          let K0 := (primeToResidual 5 K2).map K2.subtype
                          T1 ≤ normalizer (K0 : Set G) ∧ actorImage I K0 = j.val ∧
                          actorImage I (T1 ⊓ DA) ≤ centralizer (j.val : Set (HStar I)) ∧
                          subspaceCommutator a.representation ⊤ j.val ≤
                            fixedSpace a.representation (actorImage I (T1 ⊓ DA))) ∧
                        actorImage I (T1 ⊓ DA) ≤
                          centralizer (actorImage I (F.Li L 1) : Set (HStar I)) ∧
                        ⁅T1 ⊓ DA,F.Li L 1⁆ ≤ (F.Li L 1).pCoreIn 2 ∧
                        Nat.card (conjugationImage (F.Li L 1) C) = 12 ∧
                        Nonempty (conjugationImage (F.Li L 1) C ≃* alternatingGroup (Fin 4)) ∧
                        let L0 := D ⊓ (conjugationImage (F.Li L 1) C).comap C.normalizerMonoidHom
                        let L0G := L0.map (normalizer (C : Set G)).subtype
                        conjugationImage L0G C = conjugationImage (F.Li L 1) C ∧
                        (D ⊓ C.normalizerMonoidHom.ker).map (normalizer (C : Set G)).subtype ≤ L0G ∧
                        ∃ P : Sylow 2 (normalizer (C : Set G)),
                          T1 ≤ (P : Subgroup (normalizer (C : Set G))).map
                            (normalizer (C : Set G)).subtype ∧
                          (P : Subgroup (normalizer (C : Set G))).map
                            (normalizer (C : Set G)).subtype ≤ normalizer (L0G : Set G) ∧
                          ∃ TA : Sylow 2 G, (TA : Subgroup G) =
                            (P : Subgroup (normalizer (C : Set G))).map
                              (normalizer (C : Set G)).subtype)) := by
  obtain ⟨I,hIJ,hI,hneI,hmin,hU,a,hf,c,hout,f,i,hAi,hAc,hpre,hCE,hcard,hbase,hopp,hnep,hr⟩ :=
    local_minimal_five_point_preimage_control h hab structural previous J hJ hne
  let := hU
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  let := BinaryGroupAction.action a.representation
  refine ⟨I,hIJ,hI,hneI,hmin,hU,a,hf,c,hout,f,i,hAi,hAc,hpre,hCE,hcard,hbase,hopp,hnep,?_⟩
  rcases hr with hpair | ⟨D,hD,hnD,hm,hjoin,hfull⟩
  · exact Or.inl hpair
  · refine Or.inr ⟨D,hD,hnD,hm,hjoin,?_⟩
    intro htwo
    obtain ⟨S,hSI,hBS,hconj,hi,hTC,hSyl,hother,hcent,hcomm,_,hrest⟩ := hfull htwo
    exact ⟨S,hSI,hBS,hconj,hi,hTC,hSyl,hother,hcent,hcomm,hrest⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original covering core inside the factor normalizer

On the same full-action two-factor witnesses, retain the A₄ bound for the
image of T₁ intersect D and the faithful identification of the full kernel
with O₂(D). The index-two Sylow calculation places the actual ambient image
of O₂(D) inside T₁ and proves T_A = T₁ (T_A intersect D).

The original commutator bound with each other factor's literal five-residual
then makes D normalize that residual. The displayed Sylow factorization
makes T_A normalize it as well. No kernel-containment premise is assumed.
The resulting normalizer chain forces the first full factor to normalize
the common eight-group, contradicting its canonical support. Thus the
full-action two-factor branch is excluded. The simultaneous-cubic and
one-factor alternatives remain to be resolved.

Source: Aschbacher–Smith 14.7.6, printed p.1045, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter12.Section08 CriticalFusion.Source ChapterD
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter14.Section06.OddCriticalPair.Selection
open Chapter14.Section04.LargerDimension.LocalAction.Components ChapterA.Section04
open Theory.GroupAction.ElementaryEightPointResidual
open scoped IsMulCommutative Pointwise
universe u

/-- The original covering core lies in T₁, and both the component and its
compatible ambient Sylow normalize the actual other-factor five-residuals. -/
theorem local_minimal_five_core_normalizer
    {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ I : Subgroup G, I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      pCore 5 (HStar I) ≠ ⊥ ∧
      (∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
        pCore 5 (HStar E) = ⊥) ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          let : IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
          ∃ hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis,
            ∃ c : SelectedQuadraticEndpoint hf a,
              c.endpoint.representative ∉ F.H ∧
              let A := actorImage I (c.endpoint.conjugate (F.UH I))
              let C := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
              let := BinaryGroupAction.action a.representation
              ∃ (f : CanonicalFiveDihedralFamily (G := HStar I)
                  (V := Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))))
                (i : smallSupportFactors (HStar I)
                  (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2),
                A ≤ f.factor i ∧ Nat.card A = 2 ∧
                C = Chapter14.Section06.OddNormalizer.supportPreimage a
                  (subspaceCommutator a.representation ⊤ A) ∧
                IsElementaryAbelian 2 C ∧ Nat.card C = 8 ∧
                F.Vi 1 ≤ C ∧ c.endpoint.conjugate (F.Vi 1) ≤ C ∧
                F.Vi 1 ≠ c.endpoint.conjugate (F.Vi 1) ∧
                ((I.pCoreIn 2 ≤ centralizer (C : Set G) ∧
                    (c.endpoint.conjugate I).pCoreIn 2 ≤ centralizer (C : Set G)) ∨
                  ∃ D : Subgroup (normalizer (C : Set G)),
                    D.IsCComponent ∧ D.Normal ∧ D.map C.normalizerMonoidHom = ⊤ ∧
                    D.map (normalizer (C : Set G)).subtype ⊔ centralizer (C : Set G) =
                      normalizer (C : Set G) ∧
                    (Nat.card (smallSupportFactors (HStar I)
                      (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 2 →
                      ∃ S : Sylow 2 G, (S : Subgroup G) ≤ I ∧
                        (∃ x : I, S = (x : G)⁻¹ • T) ∧
                        let K1 := ((f.factor i).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
                        let T1 := (S : Subgroup G) ⊓ normalizer (K1 : Set G)
                        let DA := D.map (normalizer (C : Set G)).subtype
                        let L0 := D ⊓ (conjugationImage (F.Li L 1) C).comap C.normalizerMonoidHom
                        let L0G := L0.map (normalizer (C : Set G)).subtype
                        ∃ TA : Sylow 2 G,
                          T1 ≤ TA ∧ (TA : Subgroup G) ≤ normalizer (C : Set G) ∧
                          (TA : Subgroup G) ≤ normalizer (L0G : Set G) ∧
                          DA.pCoreIn 2 ≤ T1 ∧
                          T1 ⊔ ((TA : Subgroup G) ⊓ DA) = (TA : Subgroup G) ∧
                          (∀ j : smallSupportFactors (HStar I)
                              (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2,
                            i ≠ j →
                            let K2 := ((f.factor j).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
                            let K0 := (primeToResidual 5 K2).map K2.subtype
                            actorImage I K0 = j.val ∧ K0.pCoreIn 2 ≠ ⊥ ∧
                            K1 ≤ normalizer (K0 : Set G) ∧
                            normalizer (K0 : Set G) ≤ normalizer (DA : Set G) ∧
                            DA ≤ normalizer (K0 : Set G) ∧
                            (TA : Subgroup G) ≤ normalizer (K0 : Set G)) ∧
                          DA ∈ Chapter1.LStar G (TA : Subgroup G) ∧ IsFaithfulSignalizerType DA ∧
                          (DA.subgroupOf (DA ⊔ (TA : Subgroup G))).Normal ∧
                          (C.normalizerMonoidHom.comp D.subtype).ker = pCore 2 D ∧
                          Nonempty ((D ⧸ pCore 2 D) ≃* Matrix.PSL3Two.PSL) ∧
                          normalizer (C : Set G) ≤ normalizer (DA : Set G) ∧
                          IsMaximalTwoLocal (normalizer (DA : Set G)) ∧
                          (∀ M : Subgroup G, IsMaximalTwoLocal M → DA ⊔ (TA : Subgroup G) ≤ M →
                            M = normalizer (DA : Set G)))) := by
  obtain ⟨I,hIJ,hI,hIne,hmin,hU,a,hf,c,houtc,f,i,hAi,hAc,hCpre,hCE,hCc,
      hbase,hopp,hnepoints,hresult⟩ :=
    local_minimal_five_point_preimage_control h hab structural previous J hJ hne
  let := hU
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  let := BinaryGroupAction.action a.representation
  let C := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
  refine ⟨I,hIJ,hI,hIne,hmin,hU,a,hf,c,houtc,f,i,hAi,hAc,hCpre,hCE,hCc,
    hbase,hopp,hnepoints,?_⟩
  rcases hresult with hpair | ⟨D,hD,hnD,hmD,hjoin,hfull⟩
  · exact Or.inl hpair
  · refine Or.inr ⟨D,hD,hnD,hmD,hjoin,?_⟩
    intro htwo
    obtain ⟨S,hSI,hBS,hconj,hindex,hT1C,hSyl,hother,hcentral,hcomm,hpointImage,h12,he,
      hL0image,hL0kernel,P,hT1P,hPL0,TA,hTA⟩ := hfull htwo
    have hTAC : (TA : Subgroup G) ≤ normalizer (C : Set G) :=
      hTA.le.trans (map_subtype_le _)
    let := hCE
    let := hnD
    have hfaith := common_eight_component_faithful_normalizer h.source.simpleQTKE T faithful
      C hCc TA hTAC D hD hmD
    let K1 := ((f.factor i).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
    let T1 := (S : Subgroup G) ⊓ normalizer (K1 : Set G)
    let DA := D.map (normalizer (C : Set G)).subtype
    have hT1TA : T1 ≤ TA := hT1P.trans hTA.ge
    obtain ⟨hcore,hgen⟩ := common_eight_component_core_containment S TA T1 C
      inf_le_left hindex hT1TA hTAC hCc D hmD hfaith.2.2.2.1
      (conjugationImage (F.Li L 1) C) h12 hpointImage
    refine ⟨S,hSI,hconj,TA,hT1TA,hTAC,hTA.le.trans hPL0,hcore,hgen,?_,hfaith⟩
    intro j hij
    let K2 := ((f.factor j).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
    obtain ⟨hT1K0,hmK0,_,_⟩ := hother j hij
    obtain ⟨_,hcK0⟩ := local_other_factor_component_commutator a f i j
      (actorImage I (c.endpoint.conjugate (F.UH I))) C hij hAi hCpre hCE hCc
      h.source.simpleQTKE D hD hmD
    obtain ⟨hDK0,hTAK0⟩ := five_residual_normalized_of_component_core_containment DA T1 K2 TA
      hcore hgen hT1K0 hcK0
    have hneK0 : actorImage I ((primeToResidual 5 K2).map K2.subtype) ≠ ⊥ := by
      rw [hmK0]
      intro hz
      have hc := j.property.2.1
      rw [hz,card_bot] at hc
      norm_num at hc
    have hcoreK0 := local_five_residual_core_ne_bot a (f.factor j) hneK0
    have hK1K0 := local_factor_normalizes_other_five_residual a f i j hij
    have hNK0 := five_residual_normalizer_le_component_normalizer DA
      ((primeToResidual 5 K2).map K2.subtype) TA hcoreK0 hDK0 hTAK0 hfaith.2.2.2.2.2.2.2
    exact ⟨hmK0,hcoreK0,hK1K0,hNK0,hDK0,hTAK0⟩

/-- The original two-factor alternative can only have simultaneous cubic
endpoint actions: the full common-space action gives a contradiction. -/
theorem local_minimal_five_two_factor_exclusion
    {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ I : Subgroup G, I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      pCore 5 (HStar I) ≠ ⊥ ∧
      (∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
        pCore 5 (HStar E) = ⊥) ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          let : IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
          ∃ hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis,
            ∃ c : SelectedQuadraticEndpoint hf a,
              c.endpoint.representative ∉ F.H ∧
              let A := actorImage I (c.endpoint.conjugate (F.UH I))
              let C := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
              let := BinaryGroupAction.action a.representation
              ∃ (f : CanonicalFiveDihedralFamily (G := HStar I)
                  (V := Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))))
                (i : smallSupportFactors (HStar I)
                  (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2),
                A ≤ f.factor i ∧ Nat.card A = 2 ∧
                C = Chapter14.Section06.OddNormalizer.supportPreimage a
                  (subspaceCommutator a.representation ⊤ A) ∧
                IsElementaryAbelian 2 C ∧ Nat.card C = 8 ∧
                F.Vi 1 ≤ C ∧ c.endpoint.conjugate (F.Vi 1) ≤ C ∧
                F.Vi 1 ≠ c.endpoint.conjugate (F.Vi 1) ∧
                ((I.pCoreIn 2 ≤ centralizer (C : Set G) ∧
                    (c.endpoint.conjugate I).pCoreIn 2 ≤ centralizer (C : Set G)) ∨
                  Nat.card (smallSupportFactors (HStar I)
                    (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) ≠ 2) := by
  obtain ⟨I,hIJ,hI,hneI,hmin,hU,a,hf,c,hout,f,i,hAi,hAc,hpre,hCE,hCc,hbase,hopp,hnep,hr⟩ :=
    local_minimal_five_core_normalizer h hab structural previous faithful J hJ hne
  let := hU
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  let := BinaryGroupAction.action a.representation
  let C := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
  refine ⟨I,hIJ,hI,hneI,hmin,hU,a,hf,c,hout,f,i,hAi,hAc,hpre,hCE,hCc,hbase,hopp,hnep,?_⟩
  rcases hr with hpair | ⟨D,hD,hnD,hmD,hjoin,hfull⟩
  · exact Or.inl hpair
  · right
    intro htwo
    obtain ⟨S,hSI,hconj,TA,hT1TA,hTAC,hTAL0,hcore,hgen,hother,hrest⟩ := hfull htwo
    obtain ⟨j,hji,_⟩ := (Nat.card_eq_two_iff' i).mp htwo
    let K1 := ((f.factor i).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
    have hK1D : K1 ≤ normalizer (D.map (normalizer (C : Set G)).subtype : Set G) :=
      (hother j hji.symm).2.2.1.trans (hother j hji.symm).2.2.2.1
    have hK1Z : K1 ≤ normalizer (F.Vi 1 : Set G) := (map_subtype_le _).trans hI.2.1
    have hZne : F.Vi 1 ≠ ⊥ := by
      intro hz
      have hc := hf.point_card
      change Nat.card (F.Vi 1) = 2 at hc
      rw [hz,card_bot] at hc
      omega
    let := hCE
    have hK1C := (le_inf hK1Z hK1D).trans
      (normalizes_common_space_of_normalizes_point_cover C (F.Vi 1) hbase hZne D hmD)
    exact local_factor_not_normalizes_common a f i
      (actorImage I (c.endpoint.conjugate (F.UH I))) C hAi hAc hpre hCE hCc hK1C

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Involution control in the single quintic factor branch

A singleton canonical five-factor is normal. The actual point cubic acts
without fixed vectors on the original U_I/V₁, so the support calculation
forces every square-one star actor to centralize it. The full star image
of R₁ is the centralizer of that cubic in the Sylow image. Its inverse
image is exactly R₁: O₂(I) already lies in O₂(L₁T). Thus Ω₁(T) lies in R₁,
with the original ambient Sylow and quotient maps unchanged.

Source: Aschbacher–Smith, 14.7.5(3), 14.7.6, printed pp.1044–1045,
refs/quasithin.pdf. The ambient source application is in
LargePrimeSingleFactorSource.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter12.Section08 CriticalFusion.Source ChapterD
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

/-- The single canonical five-factor is normal, so every square-one star
actor centralizes the original point cubic. -/
theorem local_single_five_square_one_centralizes
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I : Subgroup G) (hLI : F.Li L 1 ≤ I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    let := BinaryGroupAction.action a.representation
    ∀ (_i : smallSupportFactors (HStar I)
        (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2),
      Nat.card (smallSupportFactors (HStar I)
        (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 1 →
      ∀ t : HStar I, t ^ 2 = 1 →
        t ∈ centralizer (actorImage I (F.Li L 1) : Set (HStar I)) := by
  intro _ i hone t ht
  let W := Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I))
  let := BinaryGroupAction.action a.representation
  let : IsElementaryAbelian 2 (Multiplicative W) := BinaryGroupAction.elementary
  let : FaithfulSMul (HStar I) (Multiplicative W) :=
    BinaryGroupAction.faithful a.representation a.faithful
  let : Subsingleton (smallSupportFactors (HStar I) (Multiplicative W) 2) :=
    (Nat.card_eq_one_iff_unique.mp hone).1
  let : i.val.Normal := normalizer_eq_top_iff.mp (top_unique (by
    intro g _
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact congrArg Subtype.val (Subsingleton.elim (smallSupportFactors_conjEquiv 2 g i) i)))
  let B := actorImage I (F.Li L 1)
  let : B.Normal := Normal.map hn _ (QuotientGroup.mk'_surjective _)
  have hB : Nat.card B = 3 := local_point_star_card_of_normal h structural I hLI hn
  have hfixed : FixedPoints.subgroup B (Multiplicative W) = ⊥ := by
    rw [BinaryGroupAction.fixedPoints_eq]
    change BinaryGroupAction.submoduleEquivSubgroup
      (fixedSpace a.representation (((F.Li L 1).subgroupOf I).map
        (QuotientGroup.mk' (pCore 2 I)))) = ⊥
    rw [local_point_fixedSpace_eq_bot h structural I hLI hn a]
    exact BinaryGroupAction.submoduleEquivSubgroup.map_bot
  exact _root_.SmallBinaryPrimeNormalizer.square_one_centralizes_cubic_on_five_support
    (V := Multiplicative W) i.val B i.property.2.1 hB i.property.2.2 hfixed t ht

/-- Centralization of the actual point image by a subgroup of T places it
in R₁. Both two-cores and the full original quotient map are retained. -/
theorem local_sylow_le_point_core_of_star_centralizes
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I : Subgroup G) (hBI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (E : Subgroup G) (hET : E ≤ T)
    (hc : actorImage I E ≤ centralizer (actorImage I (F.Li L 1) : Set (HStar I))) :
    E ≤ F.Ri L 1 := by
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 I)
  let P := actorImage I (F.Li L 1)
  let : P.Normal := Normal.map hn _ (QuotientGroup.mk'_surjective _)
  have hP : IsPGroup 3 P := IsPGroup.of_card (n := 1)
    (by change Nat.card P = 3
        exact local_point_star_card_of_normal h structural I (le_sup_left.trans hBI) hn)
  let S : Sylow 2 I := T.subtype (le_sup_right.trans hBI)
  let S' : Sylow 2 (HStar I) := S.mapSurjective (QuotientGroup.mk'_surjective _)
  have hgen : actorImage I B = P ⊔ (S' : Subgroup (HStar I)) := by
    change (B.subgroupOf I).map q = _
    rw [subgroupOf_sup (le_sup_left.trans hBI) (le_sup_right.trans hBI),Subgroup.map_sup]
    rfl
  have hcore : actorImage I (F.Ri L 1) = (actorImage I B).pCoreIn 2 := by
    have he : (B.subgroupOf I).pCoreIn 2 = (B.pCoreIn 2).subgroupOf I := by
      apply map_injective I.subtype_injective
      rw [map_pCoreIn_of_injective 2 _ _ I.subtype_injective,map_subgroupOf_eq_of_le hBI,
        map_subgroupOf_eq_of_le ((pCoreIn_le 2 B).trans hBI)]
    change ((B.pCoreIn 2).subgroupOf I).map q = _
    rw [←he,map_pCoreIn_of_ker_isPGroup q (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)]
    rfl
  have hm : actorImage I E ≤ actorImage I (F.Ri L 1) := by
    rw [hcore,hgen,core_join_odd_eq_sylow_centralizer P hP S']
    exact le_inf (map_mono (comap_mono hET)) hc
  have hQI : I.pCoreIn 2 ≤ T := by
    have hh := pCoreIn_le_sylow I S
    simpa only [S,Sylow.coe_subtype,map_subgroupOf_eq_of_le (le_sup_right.trans hBI)] using hh
  have hQB : I.pCoreIn 2 ≤ B.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 I) (hQI.trans le_sup_right)
    (hBI.trans (I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))))
  intro e he
  have heI : e ∈ I := (hET.trans (le_sup_right.trans hBI)) he
  have heimage := hm (mem_map_of_mem q (show (⟨e,heI⟩ : I) ∈ E.subgroupOf I from he))
  obtain ⟨r,hr,heq⟩ := heimage
  have hdiff : (r : G)⁻¹ * e ∈ B.pCoreIn 2 := hQB (mem_map.mpr
    ⟨r⁻¹ * ⟨e,heI⟩,(QuotientGroup.eq_one_iff _).mp (by
      change q (r⁻¹ * ⟨e,heI⟩) = 1
      rw [map_mul,map_inv,heq,inv_mul_cancel]),rfl⟩)
  change e ∈ B.pCoreIn 2
  have hh := (B.pCoreIn 2).mul_mem hr hdiff
  change (r : G) * ((r : G)⁻¹ * e) ∈ B.pCoreIn 2 at hh
  simpa only [mul_inv_cancel_left] using hh

/-- The original involution-generated Sylow subgroup lies in R₁ in the
singleton canonical-factor branch. -/
theorem local_single_five_omega_le_point_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I : Subgroup G) (hBI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    let := BinaryGroupAction.action a.representation
    ∀ (_i : smallSupportFactors (HStar I)
        (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2),
      Nat.card (smallSupportFactors (HStar I)
        (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 1 →
      omegaOneAmbient (T : Subgroup G) ≤ F.Ri L 1 := by
  intro _ i hone
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro t ht ht2
  have hzt : zpowers t ≤ T := zpowers_le.mpr ht
  have htI : t ∈ I := (le_sup_right.trans hBI) ht
  apply local_sylow_le_point_core_of_star_centralizes h structural I hBI hn (zpowers t) hzt
    (by
      have hm : actorImage I (zpowers t) = zpowers (QuotientGroup.mk' (pCore 2 I) ⟨t,htI⟩) := by
        rw [actorImage,show (zpowers t).subgroupOf I = zpowers (⟨t,htI⟩ : I) from
          (map_injective I.subtype_injective (by rw [map_subgroupOf_eq_of_le (hzt.trans (le_sup_right.trans hBI)),MonoidHom.map_zpowers]; rfl)),
          MonoidHom.map_zpowers]
      rw [hm]
      exact zpowers_le.mpr (local_single_five_square_one_centralizes h structural I
        (le_sup_left.trans hBI) hn a i hone _ (by
          rw [←map_pow]
          have he : (⟨t,htI⟩ : I) ^ 2 = 1 := Subtype.ext ht2
          rw [he,map_one])))
  exact mem_zpowers t

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original involution fusion into the seed core

The same natural-action marking identifies T's image with the binary Borel
and R₁'s image with its point four-group. A nontrivial point-four element
has an actual conjugate in the Borel outside that four-group. Lift its
conjugator through the original action. The full two-group kernel lies in
T, so the conjugate of an original involution again lies in T. Consequently
Ω₁(T) ≤ R₁ forces Ω₁(T) ≤ O₂(LT).

Every rank-indexed elementary Thompson subgroup lies in Ω₁(T). Heredity
inside O₂(LT) makes each such subgroup normal in LT. This retains the
original flag, group action and Sylow; no new involution lift is assumed.

Source: Aschbacher–Smith, 14.7.6, printed p.1045; B.2.3(3), p.75;
refs/quasithin.pdf. LargePrimeSingleFactorSource supplies the application.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Subgroup Theory.GroupTheory Stellmacher
open Chapter12.Section08 ChapterB
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {K : GroupClass.{u}}

/-- Fusion in the original L₃(2) action places the entire first omega in
O₂(LT) as soon as it lies in R₁. No involution-lifting premise is used. -/
theorem omega_le_seed_core_of_le_point_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hΩ : omegaOneAmbient (T : Subgroup G) ≤ F.Ri L 1) :
    omegaOneAmbient (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  rw [←h.centralizer_LT_at structural]
  refine le_inf ((omegaOneAmbient_le _).trans le_sup_right) ?_
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro t ht ht2
  obtain ⟨e,q,hq,hk2,ha,hk,hT,hR⟩ :=
    Chapter14.Section03.ThompsonSourceAt.exists_marking h F structural
  let H := L ⊔ (T : Subgroup G)
  let S : Sylow 2 H := T.subtype le_sup_right
  let t₀ : H := ⟨t,mem_sup_right ht⟩
  have htR : t ∈ F.Ri L 1 :=
    hΩ ((omegaOneAmbient_le_iff _ _).mp le_rfl t ht ht2)
  have htimage : q t₀ ∈ Matrix.PSL3Two.MarkedAutomorphisms.pointV :=
    hR ▸ mem_map_of_mem q htR
  by_contra htc
  have hne : q t₀ ≠ 1 := by
    intro hz
    have hh : t₀ ∈ q.ker := hz
    rw [hk] at hh
    exact htc hh
  obtain ⟨g,hgT,hgR⟩ := BinaryLinearThree.ThompsonEscape.cyclic_escape (q t₀) htimage hne
  obtain ⟨x,rfl⟩ := hq g
  let y : H := x * t₀ * x⁻¹
  have hqy : q y = (MulAut.conj (q x)) (q t₀) := by
    simp only [y,map_mul,map_inv,MulAut.conj_apply]
  have hyimage : q y ∈ Matrix.PSL3Two.borelSL :=
    hqy.symm ▸ hgT (mem_map_of_mem _ (mem_zpowers (q t₀)))
  have hyS : y ∈ ((T : Subgroup G).subgroupOf H) := by
    have hh : y ∈ (((T : Subgroup G).subgroupOf H).map q).comap q := hT.symm ▸ hyimage
    have hkerS : q.ker ≤ (T : Subgroup G).subgroupOf H := hk2.le_sylow_of_normal S
    rw [comap_map_eq,sup_eq_left.mpr hkerS] at hh
    exact hh
  have hy2 : (y : G) ^ 2 = 1 := by
    change ((x : G) * t * (x : G)⁻¹) ^ 2 = 1
    rw [conj_pow,ht2]
    simp
  have hyR : (y : G) ∈ F.Ri L 1 :=
    hΩ ((omegaOneAmbient_le_iff (T : Subgroup G)
      (omegaOneAmbient (T : Subgroup G))).mp le_rfl (y : G) hyS hy2)
  apply hgR
  rw [MonoidHom.map_zpowers]
  apply zpowers_le.mpr
  change (MulAut.conj (q x)) (q t₀) ∈ Matrix.PSL3Two.MarkedAutomorphisms.pointV
  rw [←hqy]
  exact hR ▸ mem_map_of_mem q hyR

/-- Every rank-indexed elementary Thompson subgroup is inherited by the
original seed core and is consequently normalized by LT. -/
theorem thompson_normalized_of_omega_le_point_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hΩ : omegaOneAmbient (T : Subgroup G) ≤ F.Ri L 1)
    (i : ℕ) (hi : i < twoRank (T : Subgroup G)) :
    thompsonJ (T : Subgroup G) i = thompsonJ ((L ⊔ (T : Subgroup G)).pCoreIn 2) i ∧
      L ⊔ (T : Subgroup G) ≤ normalizer (thompsonJ (T : Subgroup G) i : Set G) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hJΩ : thompsonJ (T : Subgroup G) i ≤ omegaOneAmbient (T : Subgroup G) := by
    apply sSup_le
    intro A hA
    let := hA.2.1
    rw [←omegaOneAmbient_eq_self A]
    exact omegaOneAmbient_mono hA.1
  have hJQ := hJΩ.trans (omega_le_seed_core_of_le_point_core h structural hΩ)
  have hQT : Q ≤ T := by
    have hh := pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using hh
  have he := lemma_B_2_3_3 (T : Subgroup G) Q hi hJQ hQT
  refine ⟨he,?_⟩
  rw [he]
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (thompsonJ Q i).map (MulAut.conj g).toMonoidHom = thompsonJ Q i
  rw [←thompsonJ_map_equiv]
  congr 1
  apply mem_normalizer_iff_map_conj_eq.mp
  exact ((L ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))) hg

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Thompson factorization excludes the singleton five-factor branch

Fusion places Ω₁(T) inside the seed core whenever it lies in R₁. Thompson
heredity then makes LT normalize J₀(T) and Ω₁(Z(J₁(T))). Both are nontrivial
two-groups, so uniqueness over LT places their full normalizers in M.

For the original normal escaping lift Y with five-group quotient by O₂(Y),
YT is solvable of order prime to three. Characteristic two passes from the
original local I to this Sylow overgroup. Solvable Thompson factorization
gives its literal ordered product of the two normalizers, forcing Y into M
and contradicting its original escape. The quotient kernel is never erased.
LargePrimeSingleFactorSource applies this to the original canonical family.

Source: Aschbacher–Smith, 14.7.6, printed p.1045; GLS Number 2, G.26.18(a),
printed pp.152–153; refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Subgroup Theory.GroupTheory Stellmacher ChapterB
open Chapter12.Section08
open scoped IsMulCommutative Pointwise
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

include F in
private theorem LargePrimeSingleThompson_seed_rank_lower
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    3 ≤ twoRank (T : Subgroup G) := by
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty (T : Subgroup G)
  have hc := hA.2.2 V h.chosen.le_sylow h.chosen.elementary
  have hV : Nat.card V = 2 ^ 3 := by simpa only [F.last] using F.card 3 (by decide)
  rw [hV,elementaryAbelianMaxSubgroups_card_eq _ _ hA,maxOrder_eq_two_pow_rank] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

private theorem LargePrimeSingleThompson_thompson_nonzero (R : Subgroup G) {j : ℕ} (hj : j < twoRank R) :
    thompsonJ R j ≠ ⊥ := by
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty R
  have hAJ : A ≤ thompsonJ R 0 := by
    rw [thompsonJ_zero]
    exact le_sSup hA
  have hc : 1 < Nat.card A := by
    rw [elementaryAbelianMaxSubgroups_card_eq R A hA,maxOrder_eq_two_pow_rank]
    exact one_lt_pow₀ (by decide : 1 < 2) (by omega)
  intro he
  have hAbot : A = ⊥ := bot_unique
    ((hAJ.trans (lemma_B_2_3_1 R (Nat.zero_le j) hj)).trans he.le)
  rw [hAbot,Subgroup.card_bot] at hc
  omega

private theorem LargePrimeSingleThompson_omega_center_nonzero (R : Subgroup G)
    (hR : IsPGroup 2 R) (hne : R ≠ ⊥) : omegaOneCenterAmbient R ≠ ⊥ := by
  have hi := Chapter1.RadicalNormalizers.omegaCenterIn_ne_bot R hR hne
  intro he
  apply hi
  apply Subgroup.map_injective (f := R.subtype) R.subtype_injective
  simpa [omegaOneCenterAmbient,Chapter1.RadicalNormalizers.omegaCenterIn] using he

/-- Uniqueness over the original LT controls the two full normalizers
used by solvable Thompson factorization. -/
theorem thompson_normalizers_le_of_omega_le_point_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hΩ : omegaOneAmbient (T : Subgroup G) ≤ F.Ri L 1) :
    normalizer (thompsonJ (T : Subgroup G) 0 : Set G) ≤ normalizer (L : Set G) ∧
      normalizer (omegaOneCenterAmbient (thompsonJ (T : Subgroup G) 1) : Set G) ≤
        normalizer (L : Set G) := by
  have hr := LargePrimeSingleThompson_seed_rank_lower (F := F) h
  have hu : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  have huniq (M : Subgroup G) (hM : IsMaximalTwoLocal M)
      (hLM : L ⊔ (T : Subgroup G) ≤ M) : M = normalizer (L : Set G) :=
    Set.mem_singleton_iff.mp ((h.maximal_unique_at structural).2 ▸
      show M ∈ {M : Subgroup G | IsMaximalTwoLocal M ∧ L ⊔ (T : Subgroup G) ≤ M} from
        ⟨hM,hLM⟩)
  have hJp (j : ℕ) : IsPGroup 2 (thompsonJ (T : Subgroup G) j) :=
    T.isPGroup'.to_le (thompsonJ_le _ _)
  have hn (j : ℕ) (hj : j < twoRank (T : Subgroup G)) :
      L ⊔ (T : Subgroup G) ≤ normalizer (thompsonJ (T : Subgroup G) j : Set G) :=
    (thompson_normalized_of_omega_le_point_core h structural hΩ j hj).2
  refine ⟨normalizer_le_of_unique_maximalTwoLocal huniq (hJp 0)
    (LargePrimeSingleThompson_thompson_nonzero _ (by omega)) (hn 0 (by omega)),?_⟩
  apply normalizer_le_of_unique_maximalTwoLocal huniq
    ((hJp 1).to_le (by intro x hx; exact ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1))
    (LargePrimeSingleThompson_omega_center_nonzero _ (hJp 1) (LargePrimeSingleThompson_thompson_nonzero _ (by omega)))
  apply (hn 1 (by omega)).trans
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
  change (omegaOneCenterAmbient (thompsonJ (T : Subgroup G) 1)).map
    (MulAut.conj g).toMonoidHom = _
  change (thompsonJ (T : Subgroup G) 1).map (MulAut.conj g).toMonoidHom =
    thompsonJ (T : Subgroup G) 1 at hg
  rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,hg]

/-- A solvable subgroup containing T inside the original local I lies in M
when its order is prime to three and all involutions of T lie in R₁. -/
theorem local_threePrime_le_normalizer_of_omega
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hΩ : omegaOneAmbient (T : Subgroup G) ≤ F.Ri L 1)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (W : Subgroup G) (hTW : (T : Subgroup G) ≤ W) (hWI : W ≤ I)
    [Group.IsSolvable W] (h3 : Nat.Coprime 3 (Nat.card W)) :
    W ≤ normalizer (L : Set G) := by
  let S : Sylow 2 W := T.subtype hTW
  have hS : (S : Subgroup W).map W.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hTW
  have hr : 1 < twoRank (S : Subgroup W) := by
    rw [←twoRank_map_injective W.subtype W.subtype_injective,hS]
    exact lt_of_lt_of_le (by decide : 1 < 3) (LargePrimeSingleThompson_seed_rank_lower (F := F) h)
  have hchar := F.localKernel_characteristicTwo h.source.simpleQTKE L _ I hI
  have hfit := generalizedFitting_eq_pCore_of_sylow_overgroup T W I hTW hWI hchar
  have hc : centralizer (pCore 2 W : Set W) ≤ pCore 2 W := by
    rw [←hfit]
    exact centralizer_generalizedFitting_le W
  have hf := solvable_threePrime_thompson_factorization S hr h3 hc
  have hp := thompson_factorization_subgroup_product W (S : Subgroup W) hf
  rw [hS] at hp
  obtain ⟨hN0,hN1⟩ := thompson_normalizers_le_of_omega_le_point_core h structural hΩ
  intro x hx
  have hh : x ∈ ((W ⊓ normalizer (thompsonJ (T : Subgroup G) 0 : Set G) : Subgroup G) : Set G) *
      ((W ⊓ normalizer (omegaOneCenterAmbient (thompsonJ (T : Subgroup G) 1) : Set G) : Subgroup G) : Set G) := hp ▸ hx
  obtain ⟨a,ha,b,hb,rfl⟩ := hh
  exact (normalizer (L : Set G)).mul_mem (hN0 ha.2) (hN1 hb.2)

/-- The original normal five-core lift prevents Ω₁(T) from lying in R₁.
Its full two-core is retained when proving the order of YT is prime to three. -/
theorem local_five_lift_not_omega_le_point_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    [Group.IsSolvable I] (Y : Subgroup I) [Y.Normal]
    (hY5 : IsPGroup 5 (Y ⧸ pCore 2 Y))
    (hout : ¬ Y.map I.subtype ≤ normalizer (L : Set G)) :
    ¬ omegaOneAmbient (T : Subgroup G) ≤ F.Ri L 1 := by
  intro hΩ
  let N := Y.map I.subtype
  let W := N ⊔ (T : Subgroup G)
  have hTI : (T : Subgroup G) ≤ I := fun _ ht => hI.1.2 (Or.inr ht)
  have hWI : W ≤ I := sup_le (map_subtype_le Y) hTI
  let : Group.IsSolvable W := Group.isSolvable_of_isSolvable_injective (f := inclusion hWI) (inclusion_injective hWI)
  have hTN : (T : Subgroup G) ≤ normalizer (N : Set G) := by
    apply hTI.trans
    have hh := Y.le_normalizer_map I.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hY3 : Nat.Coprime 3 (Nat.card Y) := by
    obtain ⟨a,ha⟩ := hY5.exists_card_eq
    obtain ⟨b,hb⟩ := (show IsPGroup 2 (pCore 2 Y) from pCore_isPGroup).exists_card_eq
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 Y),ha,hb]
    exact ((by decide : Nat.Coprime 3 5).pow_right a).mul_right
      ((by decide : Nat.Coprime 3 2).pow_right b)
  have hN3 : Nat.Coprime 3 (Nat.card N) := by
    rw [card_map_of_injective I.subtype_injective]
    exact hY3
  have hT3 : Nat.Coprime 3 (Nat.card (T : Subgroup G)) := by
    obtain ⟨n,hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have h3 : Nat.Coprime 3 (Nat.card W) := by
    have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes N (T : Subgroup G) hTN
    apply (hN3.mul_right hT3).of_dvd_right
    rw [hc]
    exact dvd_mul_left _ _
  exact hout (le_sup_left.trans
    (local_threePrime_le_normalizer_of_omega h structural hΩ I hI W le_sup_right hWI h3))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original singleton exclusion and remaining simultaneous-cubic branch

Apply the four-dimensional normalizer calculation to the actual canonical
family supplied by the original minimal five-core reduction. In the
singleton case it places Ω₁(T) in R₁. The source-marked L₃(2) fusion then
places it in O₂(LT). Thompson heredity, uniqueness over LT and solvable
Thompson factorization force the original escaping five-core lift into M.
This excludes the singleton case without a new local recognition premise.

Minimality makes the argument apply to any fixed original witness and its
unchanged quotient action. The ambient five-rank bound gives exactly two
canonical factors. Combining this with the full-action exclusion leaves
both endpoint two-cores centralizing the same common eight-group, the
simultaneous-cubic alternative. Its exclusion and the later local
recognition reductions remain to be proved.

The original group, flag, minimal local I, normal five-core X, two-perfect
lift Y and exact quotient kernels are retained throughout.

Source: Aschbacher–Smith, 14.7.6, printed pp.1044–1045, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Chapter12.Section08 CriticalFusion.Source ChapterD ChapterB
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter14.Section06.OddCriticalPair.Selection
open Chapter14.Section04.LargerDimension.LocalAction.Components
open scoped IsMulCommutative
universe u

/-- Apply the singleton-factor argument to the original minimal witness,
including its escaping lift and the literal Sylow subgroup T. -/
theorem local_minimal_five_single_factor_control
    {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ (I : Subgroup G) (X : Subgroup (HStar I)) (Y : Subgroup I),
      I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      (∀ D : Subgroup G, D ∈ F.Hz L (normalizer (L : Set G)) → D < I →
        pCore 5 (HStar D) = ⊥) ∧
      X = pCore 5 (HStar I) ∧ (Nat.card X = 5 ∨ Nat.card X = 25) ∧
      Y.Normal ∧ IsPPerfect 2 Y ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* X) ∧
      ¬ Y.map I.subtype ≤ normalizer (L : Set G) ∧
      I = Y.map I.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∧
      Group.IsSolvable I ∧ ((F.Li L 1).subgroupOf I).Normal ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          let := BinaryGroupAction.action a.representation
          ∃ f : CanonicalFiveDihedralFamily (G := HStar I)
              (V := Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))),
            X ≤ f.product ∧
            (Nat.card (smallSupportFactors (HStar I)
              (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 1 ∨
             Nat.card (smallSupportFactors (HStar I)
              (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 2) ∧
            (Nat.card (smallSupportFactors (HStar I)
                (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 1 →
              omegaOneAmbient (T : Subgroup G) ≤ F.Ri L 1 ∧
              omegaOneAmbient (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
              ∀ k : ℕ, k < twoRank (T : Subgroup G) →
                thompsonJ (T : Subgroup G) k =
                  thompsonJ ((L ⊔ (T : Subgroup G)).pCoreIn 2) k ∧
                L ⊔ (T : Subgroup G) ≤ normalizer (thompsonJ (T : Subgroup G) k : Set G)) := by
  obtain ⟨I,X,Y,hIJ,hI,hproper,hXn,hXp,hcore,hcard,hmin,hYn,hYp,hYle,
      hYm,hYk,he,hout,hgen,hs,hn,hpoint,hm,hU,a,A,R,hAR,hA,hfaith,hR,hRE,hRc,
      hcub,hfixed,hcomm,hmove,hcompl,hcan,hpos,hcount,hcentral,f,i,hi,hfi,hXD,hPD,hfull⟩ :=
    local_minimal_five_dihedral h hab structural previous J hJ hne
  let := hU
  let := BinaryGroupAction.action a.representation
  refine ⟨I,X,Y,hIJ,hI,hproper,hcore,hcard,hYn,hYp,hYm,hYk,he,hout,hgen,hs,hn,
    hU,a,f,hXD,by omega,?_⟩
  intro hone
  have hBI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I :=
    sup_le (fun _ hx => hI.1.2 (Or.inl hx)) (fun _ hx => hI.1.2 (Or.inr hx))
  have hΩ := local_single_five_omega_le_point_core h structural I hBI hn a i hone
  exact ⟨hΩ,omega_le_seed_core_of_le_point_core h structural hΩ,
    thompson_normalized_of_omega_le_point_core h structural hΩ⟩

/-- The original minimal five-core witness has exactly two canonical factors:
Thompson factorization rules out the singleton case. -/
theorem local_minimal_five_single_factor_exclusion
    {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ (I : Subgroup G) (X : Subgroup (HStar I)) (Y : Subgroup I),
      I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      (∀ D : Subgroup G, D ∈ F.Hz L (normalizer (L : Set G)) → D < I →
        pCore 5 (HStar D) = ⊥) ∧
      X = pCore 5 (HStar I) ∧ (Nat.card X = 5 ∨ Nat.card X = 25) ∧
      Y.Normal ∧ IsPPerfect 2 Y ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* X) ∧
      ¬ Y.map I.subtype ≤ normalizer (L : Set G) ∧
      I = Y.map I.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∧
      Group.IsSolvable I ∧ ((F.Li L 1).subgroupOf I).Normal ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          let := BinaryGroupAction.action a.representation
          ∃ f : CanonicalFiveDihedralFamily (G := HStar I)
              (V := Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))),
            X ≤ f.product ∧
            Nat.card (smallSupportFactors (HStar I)
              (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 2 := by
  obtain ⟨I,X,Y,hIJ,hI,hproper,hcore,hcard,hYn,hYp,hYm,hYk,he,hout,hgen,hs,hn,
      hU,a,f,hXD,hcount,hcontrol⟩ :=
    local_minimal_five_single_factor_control h hab structural previous J hJ hne
  let := hs
  let := hYn
  let := hU
  let := BinaryGroupAction.action a.representation
  have hX5 : IsPGroup 5 X := by rw [hcore]; exact pCore_isPGroup
  have hY5 : IsPGroup 5 (Y ⧸ pCore 2 Y) := hX5.of_equiv he.some.symm
  have htwo : Nat.card (smallSupportFactors (HStar I)
      (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 2 := by
    rcases hcount with hone | htwo
    · exact False.elim ((local_five_lift_not_omega_le_point_core h structural I hI Y hY5 hout)
        (hcontrol hone).1)
    · exact htwo
  exact ⟨I,X,Y,hIJ,hI,hproper,hcore,hcard,hYn,hYp,hYm,hYk,he,hout,hgen,hs,hn,
    hU,a,f,hXD,htwo⟩

section FixedWitness
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

/-- The singleton case is impossible on any fixed minimal witness and its
original quotient action; minimality identifies the point-normal lift with I. -/
theorem local_minimal_five_single_factor_impossible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar I) ≠ ⊥)
    (hmin : ∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
      pCore 5 (HStar E) = ⊥)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    let := BinaryGroupAction.action a.representation
    ∀ (_i : smallSupportFactors (HStar I)
        (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2),
      Nat.card (smallSupportFactors (HStar I)
        (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) ≠ 1 := by
  intro _ i hone
  obtain ⟨I',X,Y,hI'I,hI',_,hcore,hcard,hYn,_,_,_,he,hout,_,hs,hn,_⟩ :=
    local_minimal_five_single_factor_control h hab structural previous I hI hne
  have hXne : X ≠ ⊥ := by
    intro hz
    rcases hcard with hc | hc <;> rw [hz,card_bot] at hc <;> omega
  have heq : I' = I := by
    by_contra hne'
    exact hXne (hcore.trans (hmin I' hI' (lt_of_le_of_ne hI'I hne')))
  subst I'
  let := hs
  let := hYn
  have hBI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I :=
    sup_le (fun _ hx => hI.1.2 (Or.inl hx)) (fun _ hx => hI.1.2 (Or.inr hx))
  have hX5 : IsPGroup 5 X := by rw [hcore]; exact pCore_isPGroup
  have hY5 : IsPGroup 5 (Y ⧸ pCore 2 Y) := hX5.of_equiv he.some.symm
  exact (local_five_lift_not_omega_le_point_core h structural I hI Y hY5 hout)
    (local_single_five_omega_le_point_core h structural I hBI hn a i hone)

/-- The actual local five-rank bounds the canonical factors of every faithful
literal quotient action, with no choice of a replacement action. -/
theorem local_five_factor_count_le_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    let := BinaryGroupAction.action a.representation
    Nat.card (smallSupportFactors (HStar I)
      (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) ≤ 2 := by
  intro _
  let W := Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I))
  let := BinaryGroupAction.action a.representation
  let : IsElementaryAbelian 2 (Multiplicative W) := BinaryGroupAction.elementary
  let : FaithfulSMul (HStar I) (Multiplicative W) :=
    BinaryGroupAction.faithful a.representation a.faithful
  let C := smallSupportFactors (HStar I) (Multiplicative W) 2
  let : Fintype C := Fintype.ofFinite C
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro hz
    have hc := F.card 1 (by decide)
    rw [hz,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  have hrI : primeRank 5 I ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 5 (inclusion hI.2.1) (inclusion_injective hI.2.1)).trans
      ((h.source.simpleQTKE.twoLocal_sqtk hH).stronglyQuasithin 5 Nat.prime_five (by decide))
  have hrX : primeRank 5 (pCore 5 (HStar I)) ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 5 _ (pCore 5 (HStar I)).subtype_injective).trans
      ((primeRank_quotient_le_of_isTwoGroup 5 (by decide) (pCore 2 I) pCore_isPGroup).trans hrI)
  change Nat.card C ≤ 2
  rw [Nat.card_eq_fintype_card]
  exact (Chapter13.Section08.SolvableExclusion.Five.canonicalFive_count_le_subgroup_rank
    (fun N : C => N.val) (fun N => N.property) Subtype.val_injective (pCore 5 (HStar I))
    (fun N => IsPGroup.le_pCore_of_le_fitting
      (IsPGroup.of_card (n := 1) (by simpa using N.property.2.1)) N.property.1)).trans hrX

end FixedWitness

/-- On the same original endpoint and common eight-group, exactly two
canonical factors remain and both endpoint two-cores centralize that group.
The simultaneous-cubic alternative is retained, not asserted impossible. -/
theorem local_minimal_five_simultaneous_cubic
    {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ I : Subgroup G, I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      pCore 5 (HStar I) ≠ ⊥ ∧
      (∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
        pCore 5 (HStar E) = ⊥) ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          let : IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
          ∃ hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis,
            ∃ c : SelectedQuadraticEndpoint hf a,
              c.endpoint.representative ∉ F.H ∧
              let A := actorImage I (c.endpoint.conjugate (F.UH I))
              let C := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
              let := BinaryGroupAction.action a.representation
              ∃ (f : CanonicalFiveDihedralFamily (G := HStar I)
                  (V := Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))))
                (i : smallSupportFactors (HStar I)
                  (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2),
                A ≤ f.factor i ∧ Nat.card A = 2 ∧
                C = Chapter14.Section06.OddNormalizer.supportPreimage a
                  (subspaceCommutator a.representation ⊤ A) ∧
                IsElementaryAbelian 2 C ∧ Nat.card C = 8 ∧
                F.Vi 1 ≤ C ∧ c.endpoint.conjugate (F.Vi 1) ≤ C ∧
                F.Vi 1 ≠ c.endpoint.conjugate (F.Vi 1) ∧
                Nat.card (smallSupportFactors (HStar I)
                  (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 2 ∧
                I.pCoreIn 2 ≤ centralizer (C : Set G) ∧
                (c.endpoint.conjugate I).pCoreIn 2 ≤ centralizer (C : Set G) := by
  obtain ⟨I,hIJ,hI,hneI,hmin,hU,a,hf,c,hout,f,i,hAi,hAc,hpre,hCE,hCc,hbase,hopp,hnep,halt⟩ :=
    local_minimal_five_two_factor_exclusion h hab structural previous faithful J hJ hne
  let := hU
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  let := BinaryGroupAction.action a.representation
  have hbound := local_five_factor_count_le_two h I hI a
  have hnotone := local_minimal_five_single_factor_impossible h hab structural previous
    I hI hneI hmin a i
  let : Nonempty (smallSupportFactors (HStar I)
      (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) := ⟨i⟩
  have hpos : 0 < Nat.card (smallSupportFactors (HStar I)
      (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) := Nat.card_pos
  have htwo : Nat.card (smallSupportFactors (HStar I)
      (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 2 := by omega
  exact ⟨I,hIJ,hI,hneI,hmin,hU,a,hf,c,hout,f,i,hAi,hAc,hpre,hCE,hCc,hbase,hopp,hnep,
    htwo,halt.resolve_right (fun hn => hn htwo)⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The order-four pairing restriction on the original minimal witness

Apply the radical-kernel argument after the established full-action and
singleton exclusions. Minimality identifies the normal five-core lift
with the same original local I. All calculations keep its original
quotient action. The selected endpoint, its actor and canonical factor remain the ones
from the simultaneous-cubic construction.

The resulting necessary condition retains the normal two-perfect lift,
its full two-core quotient kernel, generation of I, and escape from M.
Both original pairing quotients have order four, and a fixed-witness
corollary allows subsequent arguments to keep their existing coordinates.
The ambient exclusion of this configuration, five-core vanishing and
the later reductions through 14.7.52 remain to be proved.

Source: Aschbacher–Smith, 14.7.6, printed pp.1044–1045,
refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter12.Section08 CriticalFusion.Source ChapterD
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter14.Section06.OddCriticalPair.Selection
open Chapter14.Section04.LargerDimension.LocalAction.Components
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]

/-- On the original minimal five-core obstruction, the remaining cubic
branch forces the full two-core pairing quotient to have order four.
The normal two-perfect lift, its full quotient kernel and its escape from
M are preserved; no source-recognition datum or radical hypothesis is used. -/
theorem local_minimal_five_radical_reduction
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ (I : Subgroup G) (Y : Subgroup I),
      I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      pCore 5 (HStar I) ≠ ⊥ ∧
      (∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
        pCore 5 (HStar E) = ⊥) ∧
      Y.Normal ∧ IsPPerfect 2 Y ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = pCore 5 (HStar I) ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* pCore 5 (HStar I)) ∧
      ¬ Y.map I.subtype ≤ normalizer (L : Set G) ∧
      I = Y.map I.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∧
      Group.IsSolvable I ∧ ((F.Li L 1).subgroupOf I).Normal ∧
      IsElementaryAbelian 2 (F.UH I) ∧
      ⁅Y.map I.subtype,F.UH I⁆ ≤ F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G) ∧
      V ⊔ (F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G)) = F.UH I ∧
      V ⊓ (F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G)) = F.Vi 1 ∧
      (F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G)).relIndex (F.UH I) = 4 ∧
      (centralizer (F.UH I : Set G)).relIndex (I.pCoreIn 2) = 4 := by
  obtain ⟨I,hIJ,hI,hneI,hmin,hU,a,hf,c,houtc,f,i,hAi,hAc,hpre,hCE,hCc,hbase,hopp,hnep,
      htwo,hcentral,hcentralOpp⟩ :=
    local_minimal_five_simultaneous_cubic h hab structural previous faithful J hJ hne
  let := hU
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  let := BinaryGroupAction.action a.representation
  obtain ⟨I',X,Y,hI'I,hI',_,hXn,hXp,hcore,hcard,hminX,hYn,hYp,hYle,hYm,hYk,he,
      hout,hgen,hs,hn,hpoint,hm,_⟩ :=
    local_minimal_five_point_normal h hab structural previous I hI hneI
  have hXne : X ≠ ⊥ := by
    intro hz
    rcases hcard with hc | hc <;> rw [hz,card_bot] at hc <;> omega
  have heq : I' = I := by
    by_contra hne'
    exact hXne (hcore.trans (hmin I' hI' (lt_of_le_of_ne hI'I hne')))
  subst I'
  have hb : 3 ≤ hf.b := (local_f9_critical_bounds h hab structural previous I hI).1
  have hBI : c.endpoint.conjugate (F.UH I) ≤ I :=
    (map_mono (conjugateSpanBy_mono hf.plus_le le_rfl)).trans (c.endpoint.large_le hb)
  have hcomm : ⁅I.pCoreIn 2,F.UH I⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    exact hf.commutator_UH_QH_le_point
  have hZ : F.Vi 1 ≤ centralizer (I : Set G) := le_centralizer_iff.mp hf.H_centralizes
  have hmove := local_minimal_five_lift_radical a hcomm hZ X hcore hminX Y hYm
    (c.endpoint.conjugate (F.UH I)) hBI hcentral f i hAi hAc
  have hsup := local_span_eq_seed_sup_radical h I Y hgen hmove
  have hinter := local_pairing_radical_seed_intersection h I (F.Li_one_le_of_mem_Hz hI) hn hZ
  have hindices := local_cubic_pairing_index_four h I (F.Li_one_le_of_mem_Hz hI) hn hf hsup
  refine ⟨I,Y,hIJ,hI,hneI,hmin,hYn,hYp,hYm.trans hcore,hYk,?_,hout,hgen,hs,hn,hU,
    hmove,hsup,hinter,hindices⟩
  exact ⟨he.some.trans (MulEquiv.subgroupCongr hcore)⟩

/-- The numerical restriction holds on any fixed original minimal witness,
so later arguments can reuse its own action and quotient coordinates. -/
theorem local_minimal_five_pairing_index
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar I) ≠ ⊥)
    (hmin : ∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
      pCore 5 (HStar E) = ⊥) :
    (F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G)).relIndex (F.UH I) = 4 ∧
      (centralizer (F.UH I : Set G)).relIndex (I.pCoreIn 2) = 4 := by
  obtain ⟨I',Y,hI'I,hI',hne',_,_,_,_,_,_,_,_,_,_,_,_,_,_,hindices⟩ :=
    local_minimal_five_radical_reduction h hab structural previous faithful I hI hne
  have he : I' = I := by
    by_contra hh
    exact hne' (hmin I' hI' (lt_of_le_of_ne hI'I hh))
  exact he ▸ hindices

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The splitting on the original minimal five-core witness

Apply the full-module splitting to the same minimal I and its original
normal two-perfect lift. Its actual five-core quotient, full two-core
kernel, generation of I and escape from M are retained. The fixed eight
and moved complement are both I-invariant, the fixed eight meets V in
V₁, and it differs from V by original normalizer uniqueness.

No new action or local-recognition assumption is introduced. The result
does not exclude the simultaneous-cubic configuration; five-core
vanishing and the later reductions through 14.7.52 remain open.
Source: Aschbacher–Smith, 14.7.6, printed pp.1044–1045,
refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Subgroup Theory.GroupTheory Representation
open Chapter12.Section08 CriticalFusion.Source
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section04.LargerDimension.LocalAction.Components
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]

/-- On any fixed original minimal five-core witness, the same two-perfect
lift has its exact two-core as full-module action kernel. Its fixed eight
and moved complement, and the full radical, are literal ambient subgroups. -/
theorem local_minimal_five_split_lift
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar I) ≠ ⊥)
    (hmin : ∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
      pCore 5 (HStar E) = ⊥) :
    ∃ Y : Subgroup I,
      Y.Normal ∧ IsPPerfect 2 Y ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = pCore 5 (HStar I) ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* pCore 5 (HStar I)) ∧
      ¬ Y.map I.subtype ≤ normalizer (L : Set G) ∧
      I = Y.map I.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          (((F.UH I).normalizerMonoidHom.comp (inclusion a.normalizes)).comp Y.subtype).ker =
            pCore 2 Y ∧
          let W := ⁅F.UH I,Y.map I.subtype⁆
          let C := F.UH I ⊓ centralizer (Y.map I.subtype : Set G)
          I ≤ normalizer (W : Set G) ∧ I ≤ normalizer (C : Set G) ∧
          W ⊔ C = F.UH I ∧ W ⊓ C = ⊥ ∧
          V ⊔ W = F.UH I ∧ V ⊓ W = ⊥ ∧ Nat.card C = 8 ∧
          V ⊓ C = F.Vi 1 ∧ C ≠ V ∧
          W ⊔ F.Vi 1 = F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G) := by
  obtain ⟨I',Y,hI'I,hI',hne',_,hYn,hYp,hYm,hYk,he,hout,hgen,hs,hn,hU,
      hmove,hsup,hinter,hindices⟩ :=
    local_minimal_five_radical_reduction h hab structural previous faithful I hI hne
  have heq : I' = I := by
    by_contra hh
    exact hne' (hmin I' hI' (lt_of_le_of_ne hI'I hh))
  subst I'
  let := hU
  let := hYn
  obtain ⟨_,a,_⟩ := local_quadratic_actor_at h structural hab I hI
  let hf := local_f9_hypothesis h hab structural previous I hI
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  have hZ : F.Vi 1 ≤ centralizer (I : Set G) := le_centralizer_iff.mp hf.H_centralizes
  have hz := hZ.trans (centralizer_le (map_subtype_le Y))
  have hq : ⁅I.pCoreIn 2,F.UH I⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    exact hf.commutator_UH_QH_le_point
  have hY5 : IsPGroup 5 (Y ⧸ pCore 2 Y) := pCore_isPGroup.of_equiv he.some.symm
  have hk := local_radical_lift_action_kernel a Y hYp hY5 hYk hz hq hmove
  obtain ⟨hsplit,hdis⟩ := local_radical_lift_splitting a Y hYp hY5 hYk hz hq hmove
  have heigt := local_radical_fixed_eight h I Y hgen hz hmove hinter hsplit hdis
  have hrad := local_radical_eq_moved_sup_point h I Y hgen hz hmove hinter hdis hindices.1
  have hIB : I ≤ normalizer (Y.map I.subtype : Set G) := by
    have hh := Y.le_normalizer_map I.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hIW : I ≤ normalizer ((⁅F.UH I,Y.map I.subtype⁆ : Subgroup G) : Set G) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (a.normalizes hx),
      mem_normalizer_iff_map_conj_eq.mp (hIB hx)]
  have hIC := le_normalizer_inf a.normalizes
    (hIB.trans (normalizer_le_normalizer_centralizer _))
  let C := F.UH I ⊓ centralizer (Y.map I.subtype : Set G)
  have hCV : C ≠ V := by
    intro heq
    have hIV : I ≤ normalizer (V : Set G) := heq ▸ hIC
    exact hI.2.2 (hIV.trans (h.seed_normalizer_le_at structural))
  have hVC : V ⊓ C = F.Vi 1 := by
    let := h.chosen.elementary
    let := F.localKernel_tilde_seed_elementary
    have hZC : F.Vi 1 ≤ C := le_inf a.kernel_le hz
    have hLN : F.Li L 1 ≤ normalizer ((V ⊓ C : Subgroup G) : Set G) :=
      le_normalizer_inf ((F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes))
        ((F.Li_one_le_of_mem_Hz hI).trans hIC)
    rcases F.invariant_subgroup_of_ambient_natural h.naturalMarking (by decide : 3 ≤ 3)
      (V ⊓ C) (le_inf (F.le_seed 1) hZC) inf_le_left hLN with heq | heq
    · exact heq
    · exfalso
      apply hCV
      symm
      apply eq_of_le_of_card_ge (heq.ge.trans inf_le_right)
      have hv : Nat.card V = 8 := by
        simpa only [F.last,show (2 : ℕ)^3 = 8 from rfl] using F.card 3 (by decide)
      exact heigt.2.le.trans hv.ge
  exact ⟨Y,hYn,hYp,hYm,hYk,he,hout,hgen,hU,a,hk,hIW,hIC,hsplit,hdis,
    local_span_eq_seed_sup_moved h I Y hgen,heigt.1,heigt.2,hVC,hCV,hrad⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Crossed splittings on the original simultaneous-cubic witness

Write U = W C for the literal moved and fixed factors of the original
normal five-lift, and transport both factors by the selected endpoint g.
The pairing radical W V₁ contains A = [U,Uᵍ]. Splitting its commutator
in the two factors identifies A intersect C with V₁. Applying the same
calculation at the opposite endpoint forces [C,Cᵍ] = 1 and gives the
crossed identities [W,Cᵍ] = V₁ᵍ and [Wᵍ,C] = V₁.

Consequently A has distinct planes A intersect W and A intersect Wᵍ.
Their intersection is exactly [W,Wᵍ], of order two; this subgroup and
the two original point lines generate A. All subgroups are literal
ambient subgroups, before taking any quotient.

The final theorem constructs these identities on the original minimal
witness with its actual five-core quotient and full two-core action
kernel. It adds no local-recognition premise. These are restrictions on
the simultaneous-cubic branch; its exclusion, five-core vanishing and
the remaining reductions through 14.7.52 are still open.

Source: Aschbacher–Smith, 14.5.21(1) and the critical-pair calculation in
14.7.6, printed pp.1019 and 1044–1045, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Subgroup Theory.GroupTheory Representation
open Chapter12.Section08 CriticalFusion.Source
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section06.OddCriticalPair.Selection
open Chapter14.Section04.LargerDimension.LocalAction.Components
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]

local instance {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (I : Subgroup G) [hU : IsElementaryAbelian 2 (F.UH I)] :
    IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU

/-- Apply the two splittings at the literal critical endpoints. -/
theorem local_split_crossed_points
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (I : Subgroup G) [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis)
    (c : SelectedQuadraticEndpoint hf a) (hb : 3 ≤ hf.b)
    (W C : Subgroup G) (hIW : I ≤ normalizer (W : Set G))
    (hIC : I ≤ normalizer (C : Set G))
    (hsplit : W ⊔ C = F.UH I) (hdis : W ⊓ C = ⊥)
    (hZC : F.Vi 1 ≤ C)
    (hrad : W ⊔ F.Vi 1 = F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G))
    (hbase : F.Vi 1 ≤ ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆)
    (hopp : c.endpoint.conjugate (F.Vi 1) ≤ ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆)
    (hne : F.Vi 1 ≠ c.endpoint.conjugate (F.Vi 1))
    (hcard : Nat.card (⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆ : Subgroup G) = 8)
    (hcentral : I.pCoreIn 2 ≤ centralizer ((⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆ : Subgroup G) : Set G))
    (hcentralOpp : (c.endpoint.conjugate I).pCoreIn 2 ≤
      centralizer ((⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆ : Subgroup G) : Set G)) :
    let A := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
    ⁅C,c.endpoint.conjugate (F.UH I)⁆ = F.Vi 1 ∧
    ⁅c.endpoint.conjugate C,F.UH I⁆ = c.endpoint.conjugate (F.Vi 1) ∧
    ⁅C,c.endpoint.conjugate C⁆ = ⊥ ∧
    ⁅W,c.endpoint.conjugate C⁆ = c.endpoint.conjugate (F.Vi 1) ∧
    ⁅c.endpoint.conjugate W,C⁆ = F.Vi 1 ∧
    c.endpoint.conjugate (F.Vi 1) ≤ W ∧ F.Vi 1 ≤ c.endpoint.conjugate W ∧
    A ⊓ C = F.Vi 1 ∧ A ⊓ c.endpoint.conjugate C = c.endpoint.conjugate (F.Vi 1) ∧
    (A ⊓ W) ⊔ F.Vi 1 = A ∧
    (A ⊓ c.endpoint.conjugate W) ⊔ c.endpoint.conjugate (F.Vi 1) = A ∧
    Nat.card (A ⊓ W : Subgroup G) = 4 ∧
    Nat.card (A ⊓ c.endpoint.conjugate W : Subgroup G) = 4 ∧
    A ⊓ W ≠ A ⊓ c.endpoint.conjugate W ∧
    (⁅W,c.endpoint.conjugate W⁆ ⊔ c.endpoint.conjugate (F.Vi 1)) ⊔ F.Vi 1 = A ∧
    A ⊓ W ⊓ c.endpoint.conjugate W = ⁅W,c.endpoint.conjugate W⁆ ∧
    Nat.card (⁅W,c.endpoint.conjugate W⁆ : Subgroup G) = 2 := by
  let U := F.UH I
  let A := ⁅U,c.endpoint.conjugate U⁆
  let e := (MulAut.conj c.endpoint.representative).toMonoidHom
  have hWU : W ≤ U := le_sup_left.trans hsplit.le
  have hCU : C ≤ U := le_sup_right.trans hsplit.le
  have hUU : U ≤ centralizer (U : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hWC : W ≤ centralizer (C : Set G) := hWU.trans (hUU.trans (centralizer_le hCU))
  have hUopI : c.endpoint.conjugate U ≤ I :=
    (map_mono (conjugateSpanBy_mono hf.plus_le le_rfl)).trans (c.endpoint.large_le hb)
  have hUIop : U ≤ c.endpoint.conjugate I :=
    (conjugateSpanBy_mono hf.plus_le le_rfl).trans (c.endpoint.reverse_le hb)
  have hUIopW : U ≤ normalizer (c.endpoint.conjugate W : Set G) := by
    have hn := map_mono (f := e) hIW
    rw [map_equiv_normalizer_eq] at hn
    exact hUIop.trans hn
  have hUIopC : U ≤ normalizer (c.endpoint.conjugate C : Set G) := by
    have hn := map_mono (f := e) hIC
    rw [map_equiv_normalizer_eq] at hn
    exact hUIop.trans hn
  have hWCop : c.endpoint.conjugate W ≤ centralizer (c.endpoint.conjugate C : Set G) := by
    have hh := map_mono (f := e) hWC
    rw [map_centralizer_equiv] at hh
    exact hh
  have hsop : c.endpoint.conjugate W ⊔ c.endpoint.conjugate C = c.endpoint.conjugate U := by
    simpa only [Subgroup.map_sup] using congrArg (map e) hsplit
  have hradop : c.endpoint.conjugate W ⊔ c.endpoint.conjugate (F.Vi 1) =
      c.endpoint.conjugate U ⊓ centralizer ((c.endpoint.conjugate I).pCoreIn 2 : Set G) := by
    have hh := congrArg (map e) hrad
    rw [Subgroup.map_sup,map_inf _ _ _ (MulAut.conj c.endpoint.representative).injective,
      map_centralizer_equiv] at hh
    change c.endpoint.conjugate W ⊔ c.endpoint.conjugate (F.Vi 1) =
      c.endpoint.conjugate U ⊓ centralizer ((I.pCoreIn 2).map e : Set G) at hh
    rw [map_pCoreIn_of_injective 2 I e
      (MulAut.conj c.endpoint.representative).injective] at hh
    exact hh
  have hAU : A ≤ U := le_normalizer_iff_commutator_le_left.mp (hUopI.trans a.normalizes)
  have hAUop : A ≤ c.endpoint.conjugate U := by
    apply le_normalizer_iff_commutator_le_right.mp
    have hn := map_mono (f := e) a.normalizes
    rw [map_equiv_normalizer_eq] at hn
    exact hUIop.trans hn
  have hAR : A ≤ W ⊔ F.Vi 1 :=
    (le_inf hAU (le_centralizer_iff.mp hcentral)).trans hrad.ge
  have hARop : A ≤ c.endpoint.conjugate W ⊔ c.endpoint.conjugate (F.Vi 1) :=
    (le_inf hAUop (le_centralizer_iff.mp hcentralOpp)).trans hradop.ge
  have hz : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hzop : Nat.card (c.endpoint.conjugate (F.Vi 1)) = 2 :=
    (card_map_of_injective (MulAut.conj c.endpoint.representative).injective).trans hz
  have hZZ : Disjoint (F.Vi 1) (c.endpoint.conjugate (F.Vi 1)) :=
    disjoint_iff.mpr (inf_eq_bot_of_card_two_of_ne _ _ hz hzop hne)
  have hd : Disjoint W C := disjoint_iff.mpr hdis
  have hdop : Disjoint (c.endpoint.conjugate W) (c.endpoint.conjugate C) :=
    disjoint_map (MulAut.conj c.endpoint.representative).injective hd
  have hZCop : c.endpoint.conjugate (F.Vi 1) ≤ c.endpoint.conjugate C := map_mono hZC
  have hp := split_commutator_point U W C (F.Vi 1) (c.endpoint.conjugate U)
    hWC hd hsplit hZC (hUopI.trans hIW) (hUopI.trans hIC) hAR hbase
  have hpop := split_commutator_point (c.endpoint.conjugate U)
    (c.endpoint.conjugate W) (c.endpoint.conjugate C) (c.endpoint.conjugate (F.Vi 1)) U
    hWCop hdop hsop hZCop hUIopW hUIopC
    (commutator_comm U (c.endpoint.conjugate U) ▸ hARop)
    (commutator_comm U (c.endpoint.conjugate U) ▸ hopp)
  rw [commutator_comm (c.endpoint.conjugate U) U] at hpop
  obtain ⟨hCZ,hCZop,hCC,hWZop,hWZ,hZopW,hZWop⟩ :=
    split_commutator_pair_points U W C (F.Vi 1) (c.endpoint.conjugate U)
      (c.endpoint.conjugate W) (c.endpoint.conjugate C) (c.endpoint.conjugate (F.Vi 1))
      hWC hd hsplit hZC hWCop hdop hsop hZCop
      (hUopI.trans hIW) (hUopI.trans hIC) hUIopW hUIopC hAR hARop hbase hopp hZZ
  have hP : Nat.card (A ⊓ W : Subgroup G) = 4 := by
    have hn : F.Vi 1 ≤ normalizer ((A ⊓ W : Subgroup G) : Set G) :=
      (hZC.trans ((le_centralizer_iff.mp hWC).trans (centralizer_le inf_le_right))).trans
        (Subgroup.centralizer_le_normalizer _)
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint (A ⊓ W) (F.Vi 1) hn hp.2.2.2.2
    rw [hp.2.2.2.1,hcard,hz] at hh
    omega
  have hPop : Nat.card (A ⊓ c.endpoint.conjugate W : Subgroup G) = 4 := by
    have hn : c.endpoint.conjugate (F.Vi 1) ≤
        normalizer ((A ⊓ c.endpoint.conjugate W : Subgroup G) : Set G) :=
      (hZCop.trans ((le_centralizer_iff.mp hWCop).trans (centralizer_le inf_le_right))).trans
        (Subgroup.centralizer_le_normalizer _)
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint
      (A ⊓ c.endpoint.conjugate W) (c.endpoint.conjugate (F.Vi 1)) hn hpop.2.2.2.2
    rw [hpop.2.2.2.1,hcard,hzop] at hh
    omega
  have hgen := split_commutator_pair_generation U W C (F.Vi 1)
    (c.endpoint.conjugate U) (c.endpoint.conjugate W) (c.endpoint.conjugate C)
    (c.endpoint.conjugate (F.Vi 1)) hWC hsplit hWCop hsop (hUopI.trans hIC)
    hUIopC hCZ hWZop
  let M := ⁅W,c.endpoint.conjugate W⁆
  have hMop : M ≤ c.endpoint.conjugate W :=
    le_normalizer_iff_commutator_le_right.mp (hWU.trans hUIopW)
  have hMZ : Disjoint M (c.endpoint.conjugate (F.Vi 1)) := hdop.mono hMop hZCop
  have hMP : M ⊔ c.endpoint.conjugate (F.Vi 1) = A ⊓ W := by
    have hh := commutator_sup_of_commuting_factors (c.endpoint.conjugate W)
      (c.endpoint.conjugate C) W hWCop (hWU.trans hUIopC)
    rw [hsop,commutator_comm (c.endpoint.conjugate U) W,
      commutator_comm (c.endpoint.conjugate W) W,
      commutator_comm (c.endpoint.conjugate C) W,hWZop,hp.2.2.1] at hh
    exact hh.symm
  have hmiddle : A ⊓ W ⊓ c.endpoint.conjugate W = M := by
    have hh := sup_inf_sup_eq_of_disjoint_commuting_factors
      (c.endpoint.conjugate W) (c.endpoint.conjugate C)
      M (c.endpoint.conjugate (F.Vi 1)) (c.endpoint.conjugate W) ⊥
      hdop hWCop hMop hZCop le_rfl bot_le
    simpa only [sup_bot_eq,inf_bot_eq,sup_bot_eq,inf_eq_left.mpr hMop,hMP] using hh
  have hMcard : Nat.card M = 2 := by
    have hn : c.endpoint.conjugate (F.Vi 1) ≤ normalizer (M : Set G) :=
      (hZCop.trans ((le_centralizer_iff.mp hWCop).trans (centralizer_le hMop))).trans
        (Subgroup.centralizer_le_normalizer _)
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint M
      (c.endpoint.conjugate (F.Vi 1)) hn hMZ
    rw [hMP,hP,hzop] at hh
    omega
  refine ⟨hCZ,hCZop,hCC,hWZop,hWZ,hZopW,hZWop,hp.1,hpop.1,
    hp.2.2.2.1,hpop.2.2.2.1,hP,hPop,?_,hgen,hmiddle,hMcard⟩
  intro he
  have hZopWop : c.endpoint.conjugate (F.Vi 1) ≤ c.endpoint.conjugate W :=
    (le_inf hopp hZopW).trans (he.le.trans inf_le_right)
  have hzbot : c.endpoint.conjugate (F.Vi 1) = ⊥ :=
    bot_unique ((le_inf hZopWop hZCop).trans (disjoint_iff.mp hdop).le)
  rw [hzbot,card_bot] at hzop
  omega

/-- On the original surviving witness, both fixed eights commute and
both original points lie in the opposite moved summands. The common eight
has two distinct literal moved planes of order four, whose intersection is
the order-two commutator of the moved summands. -/
theorem local_minimal_five_crossed_splitting
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ I : Subgroup G, I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      pCore 5 (HStar I) ≠ ⊥ ∧
      (∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
        pCore 5 (HStar E) = ⊥) ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          let : IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
          ∃ hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis,
            ∃ c : SelectedQuadraticEndpoint hf a,
              c.endpoint.representative ∉ F.H ∧
              let A := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
              Nat.card A = 8 ∧ F.Vi 1 ≤ A ∧ c.endpoint.conjugate (F.Vi 1) ≤ A ∧
              F.Vi 1 ≠ c.endpoint.conjugate (F.Vi 1) ∧
              I.pCoreIn 2 ≤ centralizer (A : Set G) ∧
              (c.endpoint.conjugate I).pCoreIn 2 ≤ centralizer (A : Set G) ∧
              ∃ Y : Subgroup I,
                Y.Normal ∧ IsPPerfect 2 Y ∧
                Y.map (QuotientGroup.mk' (pCore 2 I)) = pCore 5 (HStar I) ∧
                ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
                Nonempty ((Y ⧸ pCore 2 Y) ≃* pCore 5 (HStar I)) ∧
                ¬ Y.map I.subtype ≤ normalizer (L : Set G) ∧
                I = Y.map I.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∧
                (((F.UH I).normalizerMonoidHom.comp (inclusion a.normalizes)).comp Y.subtype).ker =
                  pCore 2 Y ∧
                let W := ⁅F.UH I,Y.map I.subtype⁆
                let C := F.UH I ⊓ centralizer (Y.map I.subtype : Set G)
                I ≤ normalizer (W : Set G) ∧ I ≤ normalizer (C : Set G) ∧
                W ⊔ C = F.UH I ∧ W ⊓ C = ⊥ ∧
                V ⊔ W = F.UH I ∧ V ⊓ W = ⊥ ∧ Nat.card C = 8 ∧
                V ⊓ C = F.Vi 1 ∧ C ≠ V ∧
                W ⊔ F.Vi 1 = F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G) ∧
                ⁅C,c.endpoint.conjugate (F.UH I)⁆ = F.Vi 1 ∧
                ⁅c.endpoint.conjugate C,F.UH I⁆ = c.endpoint.conjugate (F.Vi 1) ∧
                ⁅C,c.endpoint.conjugate C⁆ = ⊥ ∧
                ⁅W,c.endpoint.conjugate C⁆ = c.endpoint.conjugate (F.Vi 1) ∧
                ⁅c.endpoint.conjugate W,C⁆ = F.Vi 1 ∧
                c.endpoint.conjugate (F.Vi 1) ≤ W ∧ F.Vi 1 ≤ c.endpoint.conjugate W ∧
                A ⊓ C = F.Vi 1 ∧ A ⊓ c.endpoint.conjugate C = c.endpoint.conjugate (F.Vi 1) ∧
                (A ⊓ W) ⊔ F.Vi 1 = A ∧
                (A ⊓ c.endpoint.conjugate W) ⊔ c.endpoint.conjugate (F.Vi 1) = A ∧
                Nat.card (A ⊓ W : Subgroup G) = 4 ∧
                Nat.card (A ⊓ c.endpoint.conjugate W : Subgroup G) = 4 ∧
                A ⊓ W ≠ A ⊓ c.endpoint.conjugate W ∧
                (⁅W,c.endpoint.conjugate W⁆ ⊔ c.endpoint.conjugate (F.Vi 1)) ⊔ F.Vi 1 = A ∧
                A ⊓ W ⊓ c.endpoint.conjugate W = ⁅W,c.endpoint.conjugate W⁆ ∧
                Nat.card (⁅W,c.endpoint.conjugate W⁆ : Subgroup G) = 2 := by
  obtain ⟨I,hIJ,hI,hneI,hmin,hU,a,hf,c,hout,_f,_i,_hAi,_hAc,_hpre,_hCE,hAc,
      hbase,hopp,hnep,_htwo,hcentral,hcentralOpp⟩ :=
    local_minimal_five_simultaneous_cubic h hab structural previous faithful J hJ hne
  let := hU
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  obtain ⟨Y,hYn,hYp,hYm,hYk,he,hYout,hgen,_hU',_a',hk,hIW,hIC,hsplit,hdis,
      hVW,hVWdis,hCc,hVC,hCV,hrad⟩ :=
    local_minimal_five_split_lift h hab structural previous faithful I hI hneI hmin
  have hZC : F.Vi 1 ≤ F.UH I ⊓ centralizer (Y.map I.subtype : Set G) :=
    hVC.ge.trans inf_le_right
  have hb : 3 ≤ hf.b := (local_f9_critical_bounds h hab structural previous I hI).1
  have hcross := local_split_crossed_points I a hf c hb
    ⁅F.UH I,Y.map I.subtype⁆ (F.UH I ⊓ centralizer (Y.map I.subtype : Set G))
    hIW hIC hsplit hdis hZC hrad hbase hopp hnep hAc hcentral hcentralOpp
  exact ⟨I,hIJ,hI,hneI,hmin,hU,a,hf,c,hout,hAc,hbase,hopp,hnep,hcentral,hcentralOpp,
    Y,hYn,hYp,hYm,hYk,he,hYout,hgen,hk,hIW,hIC,hsplit,hdis,hVW,hVWdis,hCc,hVC,hCV,hrad,hcross⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Five-core vanishing and the original local Fitting subgroup

On the same minimal five-core witness, the normal point cubic excludes
transvections on U_I/V₁. The crossed splitting gives [Cᵍ,U_I] = V₁ᵍ,
with Cᵍ contained in I and V₁ᵍ distinct from V₁. The order-two bound forces
this commutator into V₁, contradicting the two distinct point lines.
Thus the five-core vanishes. The earlier large-prime reduction then gives
F(I/O₂(I)) = O₃(I/O₂(I)) for every original member of H_z.

The solvable-local applications discharge the large-prime alternative,
retaining the actual normal two-perfect lifts and their full two-core
kernels. These three-core branches still require exclusion; the component
reductions and four-input assembly remain open.

Source: Aschbacher–Smith 14.7.6 and its use in 14.7.27–29, printed
pp.1044–1045 and 1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter12.Section08 CriticalFusion.Source
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section04.LargerDimension.LocalAction.Components
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

/-- Minimality recovers point normality on the specified original witness.
The four-dimensional support excludes transvections on any supplied literal
quotient-action coordinates for that same witness. -/
theorem local_minimal_five_action_no_transvections
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar I) ≠ ⊥)
    (hmin : ∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
      pCore 5 (HStar E) = ⊥)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    ∀ t : HStar I, fixedCodim a.representation (zpowers t) ≠ 1 := by
  obtain ⟨I',X,Y,hI'I,hI',_,hXn,hXp,hcore,hcard,hminX,hYn,hYp,hYle,hYm,hYk,he,
      hout,hgen,hs,hn,hpoint,hm,hU',a',A,R,hAR,hA,hfaith,hR,hRE,hRc,hcub,hfixed,
      hcomm,hmove,hcompl,_⟩ :=
    local_minimal_five_point_normal h hab structural previous I hI hne
  have hXne : X ≠ ⊥ := by
    intro hz
    rcases hcard with hc | hc <;> rw [hz,card_bot] at hc <;> omega
  have heq : I' = I := by
    by_contra hh
    exact hXne (hcore.trans (hmin I' hI' (lt_of_le_of_ne hI'I hh)))
  subst I'
  have hdim : 2 < Module.finrank (ZMod 2)
      (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I))) := by
    have hh := Submodule.finrank_le (subspaceCommutator a'.representation ⊤ ⁅X,R⁆)
    rw [hmove] at hh
    omega
  exact local_normal_point_no_transvections h structural I
    (F.Li_one_le_of_mem_Hz hI) hn a hdim

/-- The crossed opposite fixed factor excludes the remaining simultaneous
cubic case, so the five-core vanishes on every original local quotient. -/
theorem local_five_core_eq_bot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    pCore 5 (HStar J) = ⊥ := by
  by_contra hne
  obtain ⟨I,hIJ,hI,hneI,hmin,hU,a,hf,c,houtc,hAc,hbase,hopp,hnep,hcentral,
      hcentralOpp,Y,hYn,hYp,hYm,hYk,he,hYout,hgen,hk,hIW,hIC,hsplit,hdis,
      hVW,hVWdis,hCc,hVC,hCV,hrad,hcross⟩ :=
    local_minimal_five_crossed_splitting h hab structural previous faithful J hJ hne
  let := hU
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  let C := F.UH I ⊓ centralizer (Y.map I.subtype : Set G)
  let B := c.endpoint.conjugate C
  let Z' := c.endpoint.conjugate (F.Vi 1)
  have hb : 3 ≤ hf.b := (local_f9_critical_bounds h hab structural previous I hI).1
  have hBI : B ≤ I := (map_mono (show C ≤ F.UH I from inf_le_left)).trans
    ((map_mono (conjugateSpanBy_mono hf.plus_le le_rfl)).trans (c.endpoint.large_le hb))
  have hZcard : Nat.card Z' = 2 :=
    (card_map_of_injective (MulAut.conj c.endpoint.representative).injective).trans
      (by simpa using F.card 1 (by decide))
  have hc : ⁅B,F.UH I⁆ = Z' := hcross.2.1
  have hno := local_minimal_five_action_no_transvections h hab structural previous
    I hI hneI hmin a
  let s := ModuleBound.OriginalF916.conjugationSection a hf.H_centralizes
  let b : BinaryConjugationSection I (F.UH I) (F.Vi 1)
      (a.representation.comp (QuotientGroup.mk' (pCore 2 I))) := {
    section_le := s.le
    kernel_le := s.line_le
    normalized := s.normalizes
    coordinates := s.quotient
    onto := s.surjective
    kernel_eq := s.kernel
    equivariant := fun x v => (s.conjugates x v).symm }
  have hbn : ∀ x : I, fixedCodim
      (a.representation.comp (QuotientGroup.mk' (pCore 2 I))) (zpowers x) ≠ 1 := by
    intro x
    rw [fixedCodim_zpowers_eq_displacement_rank]
    have hh := hno (QuotientGroup.mk' (pCore 2 I) x)
    rw [fixedCodim_zpowers_eq_displacement_rank] at hh
    exact hh
  have hZle : Z' ≤ F.Vi 1 := hc ▸
    b.commutator_le_kernel_of_card_two_of_no_transvections hbn B Z' hBI hZcard hc.le
  have hz : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  exact hnep (eq_of_le_of_card_ge hZle (by rw [hZcard, hz])).symm

/-- Every prime core above three vanishes on each original local quotient. -/
theorem local_large_prime_cores_vanish
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (p : ℕ) (hp : p.Prime) (hgt : 3 < p) : pCore p (HStar J) = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases he : p = 5
  · subst p
    exact local_five_core_eq_bot h hab structural previous faithful J hJ
  · exact local_largePrime_core_eq_bot h hab structural previous J hJ hgt he

/-- Source 14.7.6, with the literal Fitting subgroup and two-core quotient. -/
theorem local_fitting_eq_threeCore
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    fittingSubgroup (HStar J) = pCore 3 (HStar J) := by
  apply le_antisymm _ (pCore_le_fitting (HStar J) 3)
  rw [fitting_eq_sup_pCore]
  apply iSup_le
  intro p
  have hp : p.1.1.Prime := Nat.prime_of_mem_primeFactors p.1.property
  by_cases hp2 : p.1.1 = 2
  · rw [hp2,pCore_quotient_pCore_eq_bot 2]
    exact bot_le
  by_cases hp3 : p.1.1 = 3
  · rw [hp3]
  rw [local_large_prime_cores_vanish h hab structural previous faithful J hJ p.1.1 hp
    (by have := hp.two_le; omega)]
  exact bot_le

/-- The Fitting subgroup in the exact source statement is a three-group. -/
theorem local_fitting_isThreeGroup
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    IsPGroup 3 (fittingSubgroup (HStar J)) := by
  rw [local_fitting_eq_threeCore h hab structural previous faithful J hJ]
  exact pCore_isPGroup

/-- The actual solvable-local consumer now has no large-prime branch.
Its two possible normal lifts retain their full two-core quotient kernel. -/
theorem local_solvable_threeCore_source
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (X : Subgroup (pCore 3 (HStar J))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup J),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 J ∧
      Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y ∧
      (Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∨
        Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3)) :=
  local_solvable_threeCore_models h hab structural J hJ hs
    (local_large_prime_cores_vanish h hab structural previous faithful J hJ)

/-- At the original point normalizer, the only remaining solvable branches
are the elementary-nine lift and a proper Heisenberg lift. This discharges
the large-prime alternative of `original_solvable_reduction`. -/
theorem original_solvable_threeCore_source
    (d : Chapter13.Section08.TransvectionRecognition.Component.ModelExtension.Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (hs : Group.IsSolvable F.H) :
    ∃ (X : Subgroup (pCore 3 (HStar F.H))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup F.H),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 F.H ∧
      Y.map (starMap F) = X.map (pCore 3 (HStar F.H)).subtype ∧
      ((starMap F).comp Y.subtype).ker = pCore 2 Y ∧
      (Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧ Y < pResidual 2 F.H)) := by
  apply (original_solvable_reduction d h hab structural previous faithful earlier hs).resolve_left
  rintro ⟨p,hp,hgt,hne⟩
  exact hne (local_large_prime_cores_vanish h hab structural previous faithful F.H
    (F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)) p hp hgt)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end
