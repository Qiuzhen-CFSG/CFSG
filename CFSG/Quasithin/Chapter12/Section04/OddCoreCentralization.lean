module

public import CFSG.Quasithin.Chapter12.Section04.OrdinaryLayerBalance
public import CFSG.Quasithin.ChapterA.Section01.RankActions.AutomorphismQuotient
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Automorphisms
public import Theory.SpecificGroups.SL2.OddCoreAndRank
public import Theory.SpecificGroups.SL2.SmallOddComparisons
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import GorensteinWalter.LinearRingEquiv
public import CFSG.Quasithin.FermatMersenne

/-!
# The PSL₂ seed centralizes the whole odd core in 12.4.8

The source's seed is the centerless group PSL₂(q), with q a Fermat or
Mersenne prime. Its ordinary-component hypothesis supplies perfectness;
this excludes q = 3, so the seed is simple and has two-rank two.

For each odd normal p-subgroup of rank at most two, the completed A.1.25
action embeds its automorphism group in GL₂(p) modulo a p-group kernel.
A perfect simple seed of two-rank two has trivial image: determinant one
puts a nontrivial faithful image in SL₂(p), whose two-rank is one. The
remaining p-group image is perfect and therefore trivial. Thus the seed
centralizes every ambient odd prime core. The completed A.1.9 detector
then centralizes the whole odd core for its actual Sylow two-subgroup;
simplicity and normality extend centralization to the whole seed.

This proves precisely the A.1.29 consequence used on printed p.815, while
preserving the distinction between PSL₂ and its quasisimple double cover.
SL₂(p) acting on its natural p-plane is not covered by the simple-seed
argument. No cover-rigidity, B₂, or whole-odd-core centralization premise
is added. The final 12.4.8 layer application retains only the genuine
earlier S₂ and GLS 5.22 orbit inputs and the source's actual model input.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
A.1.9, A.1.25, A.1.29 and Lemma 12.4.8, printed pp.21,25,27,815.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter12.Section04.OddCoreCentralization
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
universe u

private theorem linear_action_eq_one
    {A : Type u} [Group A] [Finite A] [IsSimpleGroup A] [Group.IsPerfect A]
    (hr : 2 ≤ primeRank 2 A) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (g : A →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) : g = 1 := by
  have hd (a : A) : (g a).det = 1 :=
    Abelianization.commutator_subset_ker (Matrix.GeneralLinearGroup.det.comp g)
      Group.IsPerfect.mem_commutator
  let f : A →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
    { toFun := fun a => ⟨(g a : Matrix (Fin 2) (Fin 2) (ZMod p)),
        congrArg Units.val (hd a)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro a b; apply Subtype.ext; exact congrArg Units.val (g.map_mul a b) }
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hk | hk
  · have hi := (MonoidHom.ker_eq_bot_iff f).mp hk
    have hle := Theory.GroupTheory.primeRank_le_of_injective 2 f hi
    have hpne : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hp
    have hpge := (Fact.out : p.Prime).two_le
    have hchar : (2 : ZMod p) ≠ 0 := by
      intro he
      exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p)
        ((ZMod.natCast_eq_zero_iff 2 p).mp he)
    rw [Matrix.SpecialLinearGroup.primeRank_two_eq_one hchar] at hle
    omega
  · have hf : f = 1 := MonoidHom.ker_eq_top_iff.mp hk
    apply MonoidHom.ext
    intro a
    apply Units.ext
    exact congrArg Subtype.val (DFunLike.congr_fun hf a)

private theorem odd_pGroup_action_eq_one
    {A : Type u} [Group A] [Finite A] [IsSimpleGroup A] [Group.IsPerfect A]
    (hr : 2 ≤ primeRank 2 A) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (P : Type u) [Group P] [Finite P] (hP : IsPGroup p P) (hrP : primeRank p P ≤ 2)
    (a : A →* MulAut P) : a = 1 := by
  obtain ⟨f, hf⟩ := ChapterA.RankActions.smallRankAutomorphismRepresentation p hp P hP hrP
  have hg : f.comp a = 1 := linear_action_eq_one hr hp (f.comp a)
  have hker : a.range ≤ f.ker := by
    rintro _ ⟨x, rfl⟩
    exact DFunLike.congr_fun hg x
  have hprange : IsPGroup p a.range := hf.to_le hker
  let : Group.IsNilpotent a.range := hprange.isNilpotent
  let : Group.IsPerfect a.range := Group.IsPerfect.range a
  have hs : Subsingleton a.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent a.range inferInstance
  apply MonoidHom.ext
  intro x
  exact congrArg Subtype.val (hs.elim (a.rangeRestrict x) 1)

private theorem simple_seed_centralizes_oddCore
    {H : Type u} [Group H] [Finite H] (hH : IsStronglyQuasithin H)
    (K : Subgroup H) [IsSimpleGroup K] [Group.IsPerfect K]
    (hr : 2 ≤ primeRank 2 K) : K ≤ centralizer (pPrimeCore 2 H : Set H) := by
  have hc (p : ℕ) [Fact p.Prime] (hp : Odd p) :
      K ≤ centralizer (pCore p H : Set H) := by
    let a : K →* MulAut (pCore p H) := MulAut.conjNormal.comp K.subtype
    have ha : a = 1 := odd_pGroup_action_eq_one hr hp (pCore p H) pCore_isPGroup
      ((Theory.GroupTheory.primeRank_le_of_injective p (pCore p H).subtype Subtype.val_injective).trans
        (hH p Fact.out hp)) a
    intro k hk x hx
    have he := congrArg (fun b : MulAut (pCore p H) => (b ⟨x, hx⟩ : H))
      (DFunLike.congr_fun ha ⟨k, hk⟩)
    change k * x * k⁻¹ = x at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  let S : Sylow 2 K := Classical.choice inferInstance
  let V := (S : Subgroup K).map K.subtype
  have hVK : V ≤ K := map_subtype_le _
  have hVO : V ≤ centralizer (pPrimeCore 2 H : Set H) :=
    ChapterA.centralizes_oddCore_of_centralizes_odd_pCores V (S.isPGroup'.map K.subtype)
      (fun p _ hp => hVK.trans (hc p hp))
  let C := centralizer (pPrimeCore 2 H : Set H)
  let : (C.subgroupOf K).Normal := inferInstance
  have hSC : (S : Subgroup K) ≤ C.subgroupOf K := map_le_iff_le_comap.mp hVO
  rcases (inferInstance : (C.subgroupOf K).Normal).eq_bot_or_eq_top with hC | hC
  · have hb : (S : Subgroup K) = ⊥ := le_bot_iff.mp (hSC.trans hC.le)
    have hcyc : IsCyclic S := by
      rw [hb]
      infer_instance
    have hle := S.primeRank_le_one_of_isCyclic hcyc
    omega
  · intro k hk
    have hm : (⟨k, hk⟩ : K) ∈ C.subgroupOf K := by rw [hC]; trivial
    exact hm

private theorem fermatMersenne_odd {p : ℕ} (hp : IsFermatOrMersennePrime p) : Odd p := by
  apply hp.1.odd_of_ne_two
  rintro rfl
  rcases hp.2 with ⟨a, ha⟩ | ⟨a, ha⟩
  · have hlow : 2 ≤ 2 ^ (2 ^ a) := Nat.le_pow (by norm_num)
    omega
  · have hd : 2 ∣ 2 ^ a := dvd_pow_self _ (by rintro rfl; norm_num at ha)
    omega

/-- The exact centerless PSL₂ model in source 12.4.8 centralizes the entire
odd core. The ordinary seed's perfectness excludes PSL₂(3); the primes
five and seven are included. No model action or centralization is assumed. -/
theorem fermatMersenne_seed_centralizes_oddCore
    {H : Type u} [Group H] [Finite H] (hH : IsStronglyQuasithin H)
    (K : Subgroup H) [IsQuasisimple K] {q : ℕ}
    (hq : IsFermatOrMersennePrime q) (hmodel : ClassicalGroup.IsPSL K 2 q) :
    K ≤ centralizer (pPrimeCore 2 H : Set H) := by
  obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ := hmodel
  let : Fact q.Prime := ⟨hq.1⟩
  let : Fintype F := Fintype.ofFinite F
  have hqodd := fermatMersenne_odd hq
  have hq3 : q ≠ 3 := by
    intro he
    let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three
      (hF.trans he) inferInstance
  have hq2 : q ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hqodd
  have hqge := hq.1.two_le
  have hlarge : 3 < q := by omega
  let eF : F ≃+* ZMod q := (ZMod.ringEquivOfPrime F hq.1
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let eK : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod q) :=
    e.trans (GorensteinWalter.psl2RingEquiv eF)
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod q)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by simpa using (show 4 ≤ q by omega))
  let : IsSimpleGroup K := (MulEquiv.isSimpleGroup_congr eK).mpr inferInstance
  have hr : 2 ≤ primeRank 2 K := by
    rw [primeRank_equiv 2 eK, Theory.PSL2.primeField_two_rank hlarge]
  exact simple_seed_centralizes_oddCore hH K hr

private theorem source_centralizer_sqtk
    {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (U₀ : Subgroup G) (hne : U₀ ≠ ⊥) (hp : IsPGroup 2 U₀) :
    IsSQTK CFSG.KnownSimple.IsKnownSimple (centralizer (U₀ : Set G)) := by
  have hN : IsSQTK CFSG.KnownSimple.IsKnownSimple (normalizer (U₀ : Set G)) :=
    hG.twoLocal_sqtk ⟨U₀, hne, hp, rfl⟩
  let f := inclusion (centralizer_le_normalizer (U₀ : Set G))
  exact ⟨hN.stronglyQuasithin.of_injective f (inclusion_injective _),
    hN.isKGroup.of_injective f (inclusion_injective _)⟩

/-- Discharge the preceding A.1.29 premise of OrdinaryLayerBalance using
the actual source H = C_G(U₀), seed K in C_G(U), and original odd-core map. -/
theorem source_12_4_8_seed_centralizes_oddCore
    {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (U U₀ K : Subgroup G) (hU : IsPGroup 2 U)
    (hU₀U : U₀ ≤ U) (hU₀ : U₀ ≠ ⊥)
    (hK : IsComponentIn K (centralizer (U : Set G)))
    {q : ℕ} (hq : IsFermatOrMersennePrime q) (hmodel : ClassicalGroup.IsPSL K 2 q) :
    K ≤ centralizer (((pPrimeCore 2 (centralizer (U₀ : Set G))).map
      (centralizer (U₀ : Set G)).subtype) : Set G) := by
  let H := centralizer (U₀ : Set G)
  have hKH : K ≤ H := hK.1.trans (centralizer_le hU₀U)
  let D := K.subgroupOf H
  let : IsQuasisimple K := hK.quasisimple
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hKH).symm
  have hHD := source_centralizer_sqtk hG U₀ hU₀ (hU.to_le hU₀U)
  have hmodelD : ClassicalGroup.IsPSL D 2 q := hmodel.of_mulEquiv (subgroupOfEquivOfLe hKH)
  have hDO := fermatMersenne_seed_centralizes_oddCore hHD.stronglyQuasithin D hq hmodelD
  intro k hk x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact congrArg Subtype.val (hDO (show (⟨k, hKH hk⟩ : H) ∈ D from hk) y hy)

/-- The 12.4.8 ordinary-layer conclusion from its actual PSL₂ seed. Only
the independently owned universal S₂ and GLS 5.22 orbit inputs remain;
the whole-odd-core centralization premise is proved here. -/
theorem source_12_4_8_seed_layer_of_fermatMersenne
    (sourceS2 : ChapterI.OrdinaryBalance.SimpleSylowFixerSolvability.{u})
    (source522 : OrdinaryLayerBalance.TwoComponentOrbit522.{u})
    {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (U U₀ K : Subgroup G) [IsMulCommutative U]
    (hU : IsPGroup 2 U) (hU₀U : U₀ ≤ U) (hU₀ : U₀ ≠ ⊥)
    (hK : IsComponentIn K (centralizer (U : Set G)))
    {q : ℕ} (hq : IsFermatOrMersennePrime q) (hmodel : ClassicalGroup.IsPSL K 2 q) :
    IsSQTK CFSG.KnownSimple.IsKnownSimple (centralizer (U₀ : Set G)) ∧
      K ≤ (componentLayer (centralizer (U₀ : Set G))).map
        (centralizer (U₀ : Set G)).subtype :=
  OrdinaryLayerBalance.source_12_4_8_seed_layer_and_sqtk sourceS2 source522 hG
    U U₀ K hU hU₀U hU₀ hK
    (source_12_4_8_seed_centralizes_oddCore hG U U₀ K hU hU₀U hU₀ hK hq hmodel)

end CFSG.Quasithin.Chapter12.Section04.OddCoreCentralization
