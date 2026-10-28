module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeComponentCover
public import Theory.GroupAction.FiveSixteenCentralizer
public import Theory.GroupAction.IndependentCoprimeSupports
public import Theory.Representation.BinaryOffender.IrreducibleDiagonal
public import Theory.GroupTheory.SubgroupTransport

/-!
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
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source ChapterD
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne

private theorem five_residual_of_ten {G : Type*} [Group G] [Finite G]
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

private theorem pair_factor_normalizer {G V : Type*} [Group G] [Finite G]
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


private theorem two_centralizer_fixes_five_support {G V : Type*} [Group G] [Finite G]
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

private theorem lifted_five_residual_image {G : Type*} [Group G] [Finite G]
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
  exact five_residual_of_ten B P hPB hB hP

private theorem lift_normalizer_mono {G : Type*} [Group G] [Finite G]
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

private theorem actor_commutes_of_two_commutator {G : Type*} [Group G] [Finite G]
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
    (le_inf hT1I inf_le_right).trans (lift_normalizer_mono I _ _
      (pair_factor_normalizer f i j hij htwo))
  have hT1K0 : T1 ≤ normalizer (K0 : Set G) :=
    hT1K2.trans (normalizer_le_normalizer_characteristic_image K2 (primeToResidual 5 K2))
  have hK2c : Nat.card (f.factor j) = 10 := by
    obtain ⟨e⟩ := f.model j
    exact (Nat.card_congr e.toEquiv).trans (DihedralGroup.nat_card (n := 5))
  have hK0m : actorImage I K0 = j.val :=
    lifted_five_residual_image I (f.factor j) j.val (f.contains j) hK2c j.property.2.1
  have hK0I : K0 ≤ I := (map_subtype_le _).trans (map_subtype_le _)
  obtain ⟨_,hcomm⟩ := local_other_factor_component_commutator a f i j A C hij hAi hC hCE hc hG D hD hm
  have hcent : actorImage I (T1 ⊓ DA) ≤ centralizer (j.val : Set (HStar I)) := by
    rw [←hK0m]
    exact actor_commutes_of_two_commutator I T1 DA K0 hT1I hK0I hT1K0 hcomm
      (IsPGroup.of_card (n := 1) (by rw [hK0m,j.property.2.1]; rfl))
  have htwoActor : IsPGroup 2 (actorImage I (T1 ⊓ DA)) :=
    ((S.isPGroup'.to_le (inf_le_left.trans inf_le_left)).comap_subtype).map
      (QuotientGroup.mk' (pCore 2 I))
  have hfix := two_centralizer_fixes_five_support (V := Multiplicative W) j.val
    (actorImage I (T1 ⊓ DA)) j.property.2.1 j.property.2.2 htwoActor hcent
  rw [BinaryGroupAction.commutator_eq,BinaryGroupAction.fixedPoints_eq] at hfix
  exact ⟨hT1K0,hK0m,hcent,BinaryGroupAction.submoduleEquivSubgroup.symm.monotone hfix⟩

private theorem normal_prime_centralized_of_fixed_space
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

private theorem commutator_le_core_of_actor_centralizes
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
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
  have hc := normal_prime_centralized_of_fixed_space a.representation Q (actorImage I B)
    hQ (local_point_fixedSpace_eq_bot h structural I hLI hn a) _
    (fun he => by rw [he,finrank_bot] at h4; omega) hstable hfixed
  exact ⟨hc,commutator_le_core_of_actor_centralizes I B (F.Li L 1) hBI hLI
    (hBI.trans ((normal_subgroupOf_iff_le_normalizer hLI).mp hn)) hc⟩


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
