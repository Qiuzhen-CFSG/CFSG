module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.SmallMathieu
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.MathieuTwentyFour
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Held
public import Theory.Mathieu.M24.Properties.CubicExponent
public import Theory.SpecificGroups.Held.TwoRank.Intrinsic
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismOrder
public import Theory.SpecificGroups.SL2.BinaryOddRank

/-!
# Closing the M₂₄ and Held relative-component exclusions

For M₂₄, the actual order leaves fields four and eight. The certified
exponent-three Sylow subgroup excludes the latter, since a PSL₂(8)
section has an element of order nine. The former is excluded by the
full-Sylow local A₅ theorem, separately retaining a trivial or nontrivial
smaller two-core.

For Held, a trivial smaller core gives a faithful full-Sylow action on
PSL₂(2ⁿ). The intrinsic rank-six bound and the certified two-subgroup of
order at least 1024 contradict the binary automorphism order. With a
nontrivial core, the native maximal two-local catalogue gives either a
solvable-kernel quotient onto S₆ or a local of order 21504. Neither can
contain the original local PSL₂ section. No ambient Held order theorem
or new finite enumeration is needed.

The quotient and relative-group transports preserve the smaller two-core
and the original Sylow actor. The resulting source-derived simple-quotient
classification is exhaustive at both flag normalizers and every eligible
nontrivial subspace of V₁; it retains the original full V₂. Central covers,
nonquasisimple components, the remaining second-component refinements and
the triangle remain with qt-d-1222-natural-relative-components. The preceding
flag markings and line action belong to qt-d-1222-natural-flag-cartan,
with discharge by qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith A.3.12 and 11.1.1, printed pp.47--48,761,
combined manuscript of 1 March 2004; GLS3 Tables 5.3e and 5.3p.
The imported concrete ATLAS models and certificates retain their attribution
and licenses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin CFSG.Quasithin.ChapterA.Section03
open CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
open SourceEmbeddings SourceEmbeddings.FiveLocalFF.SolvableQuotients
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

private theorem binary_aut_dvd (B : Subgroup G) [Group.IsPerfect B]
    (P : Sylow 2 G) (hPB : (P : Subgroup G) ≤ normalizer (B : Set G))
    (hE : IsEvenCharacteristicAt P) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL B 2 (2^n)) :
    Nat.card P ∣ (2^n * ((2^n)^2-1)) * n := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa using hF)
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
    rw [hF]
    exact (show (4:ℕ) = 2^2 from rfl).le.trans (Nat.pow_le_pow_right (by decide) hn))
  let : IsSimpleGroup B := e.isSimpleGroup
  have hz : center B = ⊥ := by
    rcases (inferInstance : (center B).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp hz)).elim
  let : IsQuasisimple B :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  let J := B ⊔ (P : Subgroup G)
  let C := B.subgroupOf J
  let a : C ≃* B := subgroupOfEquivOfLe le_sup_left
  let : C.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le B.le_normalizer hPB)
  have hC : IsComponent J C := ⟨(inferInstance : C.Normal).isSubnormal,
    IsQuasisimple.of_mulEquiv a.symm⟩
  have hlocal : B ∈ localCComponents P := hC.isCComponent
  have hf := sylow_centralizer_eq_bot_of_evenCharacteristic P hE hlocal hPB
  let φ := B.normalizerMonoidHom.comp (inclusion hPB)
  have hi : Function.Injective φ := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hf]
    refine ⟨x.property,?_⟩
    change inclusion hPB x ∈ B.normalizerMonoidHom.ker at hx
    rw [normalizerMonoidHom_ker] at hx
    exact hx
  have ha : Nat.card (MulAut B) ∣ (2^n * ((2^n)^2-1)) * n := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact Theory.PSL2.BinaryAutomorphismOrder.aut_card_dvd hF
  exact (card_dvd_of_injective φ hi).trans ha


private theorem binary_section_map (q : G →* H) [Group.IsSolvable q.ker]
    {S : Subgroup G} (B : Subgroup G) (hB : B ∈ localCComponents S)
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) :
    ClassicalGroup.IsPSL ((B.map q) ⧸ pCore 2 (B.map q)) 2 (2^n) := by
  let := local_perfect hB
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
    rw [hF]
    exact (show (4:ℕ) = 2^2 from rfl).le.trans (Nat.pow_le_pow_right (by decide) hn))
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e.isSimpleGroup
  let f := q.subgroupMap B
  let : Group.IsSolvable f.ker := by
    change Group.IsSolvable (q.subgroupMap B).ker
    rw [Subgroup.ker_subgroupMap]
    exact Group.isSolvable_of_isSolvable_injective
      (f := B.subtype.subgroupComap q.ker) (fun a b he => Subtype.ext (Subtype.ext
        (congrArg (fun x : q.ker => (x : G)) he)))
  exact ⟨F,inferInstance,inferInstance,hF,
    ⟨(PerfectCoreTwoExtension.solvableKernelQuotientEquiv f
      (q.subgroupMap_surjective B)).symm.trans e⟩⟩

private theorem binary_not_local_equiv (e : G ≃* H)
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hex : ∀ (T : Sylow 2 H) (A : Subgroup H), A ∈ localCComponents T →
      ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 2 (2^n) → False) : False := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  exact hex (S.mapSurjective (f := e.toMonoidHom) e.surjective) (B.map e.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hB e.toMonoidHom)
    (binary_section_map e.toMonoidHom B hB hn hm)

omit [Finite G] in
private theorem binary_four_alt (B : Subgroup G)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^2)) :
    Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (show Nat.card F = 4 by simpa using hF)
  exact ⟨e.trans a⟩

private theorem symmetric_six_not_binary
    (S : Sylow 2 (Equiv.Perm (Fin 6))) (B : Subgroup (Equiv.Perm (Fin 6)))
    (hl : B ∈ localCComponents S) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) : False := by
  have hd := (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
  rw [binary_card hm] at hd
  simp only [Nat.card_perm, Nat.card_fin, show Nat.factorial 6 = 720 from rfl] at hd
  have hp : 2^n ∣ 720 := (dvd_mul_right _ _).trans hd
  have hb : n < 5 := by
    by_contra! h
    have hh := (show 2^5 ∣ 2^n from pow_dvd_pow 2 h).trans hp
    norm_num at hh
  have hn2 : n = 2 := by
    interval_cases n <;> norm_num at hn ⊢ <;> norm_num at hd
  subst n
  exact symmetric_six_not_section S B hl (binary_four_alt B hm).some

private theorem held_candidate_not_binary (i : Fin 3)
    (S : Sylow 2 (Held.TwoLocalCandidates.subgroup i))
    (B : Subgroup (Held.TwoLocalCandidates.subgroup i))
    (hl : B ∈ localCComponents S) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) : False := by
  have max34 (i : Bool)
      (S : Sylow 2 (Held.LocalPairs.PairCoverage.localOvergroup i))
      (B : Subgroup (Held.LocalPairs.PairCoverage.localOvergroup i))
      (hl : B ∈ localCComponents S)
      (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) : False := by
    open Held.LocalPairs.PairCoverage Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner in
    let q := localQuotientMap i
    open Held.LocalPairs.PairCoverage in
    let f := SixPoint.quotientAction i
    have hp : IsPGroup 3 f.ker := isPGroup_iff_card_dvd_pow.mpr
      ⟨1, by simpa only [pow_one] using
        Held.TwoLocalCandidates.ThreeCoreBounds.quotientAction_kernel_card_dvd_three i⟩
    let : Group.IsNilpotent f.ker := hp.isNilpotent
    let : Group.IsSolvable f.ker := inferInstance
    let : Group.IsSolvable q.ker := by
      change Group.IsSolvable (QuotientGroup.mk' (pCore 2 _)).ker
      rw [QuotientGroup.ker_mk']
      let : Group.IsNilpotent (pCore 2 (Held.LocalPairs.PairCoverage.localOvergroup i)) := pCore_isPGroup.isNilpotent
      infer_instance
    let : Group.IsSolvable (f.comp q).ker := by
      change Group.IsSolvable (f.ker.comap q)
      exact isSolvable_comap_of_solvable_ker q f.ker
    have hq : Function.Surjective (f.comp q) :=
      (Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.SixPoint.quotientAction_surjective i).comp
        (QuotientGroup.mk'_surjective (pCore 2 (Held.LocalPairs.PairCoverage.localOvergroup i)))
    apply symmetric_six_not_binary (S.mapSurjective (f := f.comp q) hq) (B.map (f.comp q))
      (Chapter1.Section02.localCComponents_map_of_solvable_ker hl (f.comp q)) hn
    exact binary_section_map (f.comp q) B hl hn hm
  fin_cases i
  · exact max34 false S B hl hm
  · exact max34 true S B hl hm
  · have hd := (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
    rw [binary_card hm] at hd
    change 2^n * ((2^n)^2-1) ∣ Nat.card Held.TwoLocalCandidates.max5 at hd
    rw [Held.InvolutionFixedData.TwoB.max5_card] at hd
    have hp : 2^n ∣ 21504 := (dvd_mul_right _ _).trans hd
    have hb : n < 11 := by
      by_contra! h
      have hh := (show 2^11 ∣ 2^n from pow_dvd_pow 2 h).trans hp
      norm_num at hh
    interval_cases n <;> norm_num at hn <;> norm_num at hd

private theorem held_fixed_not_binary (T : Sylow 2 Held.He)
    (hcatalogue : ∀ R : Subgroup T, R ≠ ⊥ → R.Normal → IsElementaryAbelian 2 R →
      IsMaximalTwoLocal (normalizer (R.map (T : Subgroup Held.He).subtype : Set Held.He)) →
      ∃ (i : Fin 3) (g : Held.He),
        normalizer (R.map (T : Subgroup Held.He).subtype : Set Held.He) =
          (Held.TwoLocalCandidates.subgroup i).map (MulAut.conj g).toMonoidHom)
    (B : Subgroup Held.He) (hl : B ∈ localCComponents T)
    (hnorm : (T : Subgroup Held.He) ≤ normalizer (B : Set Held.He))
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) : False := by
  have hc : pCore 2 B ≠ ⊥ := by
    intro hz
    let a : (B ⧸ pCore 2 B) ≃* B :=
      (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
    have hmB := hm.of_mulEquiv a.symm
    have hnr : n ≤ 6 := (binary_rank_lower hmB).trans
      ((Theory.GroupTheory.primeRank_le_of_injective 2 B.subtype B.subtype_injective).trans Held.primeRank_two_le_six)
    let := local_perfect hl
    have hd := binary_aut_dvd B T hnorm (MainConverse.SporadicLocal.he_evenCharacteristic T) hn hmB
    open Held.LocalPairs.SylowGeometry.Calculations in
    obtain ⟨r,hr⟩ := representative_isPGroup.exists_card_eq
    have hbound := Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.representative_card_ge_of_orbit_labels
      Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.orbitSizeLabel_eq_card_orbit
    have h10 : 10 ≤ r := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hr ▸ hbound)
    have hdiv : 2^10 ∣ Nat.card Held.He := by
      apply dvd_trans _ Held.LocalPairs.SylowGeometry.Calculations.representative.card_subgroup_dvd_card
      rw [hr]
      exact pow_dvd_pow 2 h10
    have bad := (T.pow_dvd_card_of_pow_dvd_card (n := 10) hdiv).trans hd
    interval_cases n <;> norm_num at hn <;> norm_num at bad
  obtain ⟨N,hN,hBN,hTN⟩ := exists_maximal_two_local T B hnorm hc
  obtain ⟨R,hR,hRn,hRe,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le T hN hTN
  obtain ⟨i,g,hg⟩ := hcatalogue R hR hRn hRe (hNR ▸ hN)
  have hN' : N = (Held.TwoLocalCandidates.subgroup i).map (MulAut.conj g).toMonoidHom :=
    hNR.trans hg
  let d : N ≃* Held.TwoLocalCandidates.subgroup i :=
    (MulEquiv.subgroupCongr hN').trans ((MulAut.conj g).subgroupMap _).symm
  let a := subgroupOfEquivOfLe hBN
  exact binary_not_local_equiv d (T.subtype hTN) (B.subgroupOf N)
    (local_restrict hl hBN) hn
    (hm.of_mulEquiv (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)))
    (fun S A hA hmA => held_candidate_not_binary i S A hA hn hmA)

private theorem held_not_binary (e : G ≃* Held.He)
    (S : Sylow 2 G) (B : Subgroup G) (hl : B ∈ localCComponents S)
    (hnorm : (S : Subgroup G) ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) : False := by
  obtain ⟨T,hcatalogue⟩ := Held.TwoLocalCandidates.MaximalNormalizerCatalogue.exists_sylow_catalogue
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Held.He Q T
  let f := e.trans (MulAut.conj g)
  have hS : (S : Subgroup G).map f.toMonoidHom = (T : Subgroup Held.He) := by
    have he := congrArg (fun P : Sylow 2 Held.He => (P : Subgroup Held.He)) hg
    change ((S : Subgroup G).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at he
    have hf : f.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by ext x; rfl
    rw [hf,←map_map]
    exact he
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [f.toMonoidHom.ker_eq_bot f.injective]
    infer_instance
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl f.toMonoidHom
  have hn' := (map_mono (f := f.toMonoidHom) hnorm).trans (B.le_normalizer_map f.toMonoidHom)
  rw [hS] at hl' hn'
  exact held_fixed_not_binary T hcatalogue (B.map f.toMonoidHom) hl' hn' hn
    (binary_section_map f.toMonoidHom B hl hn hm)

private theorem m24_not_eight (B : Subgroup Sporadic.Mathieu.M24)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^3)) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := 3) (by simpa using hF)
  let a := e.trans (BenderSuzuki.ZD.Linear.sl2QuotientEquiv F).symm
  let f := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))
  have hf : Function.Surjective f := a.surjective.comp (QuotientGroup.mk'_surjective _)
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 SL(2,F) := Classical.choice inferInstance
  let : IsCyclic P := Matrix.SL2.odd_pGroup_isCyclic_of_injective P.isPGroup'
    (by decide : 3 ≠ 2) (P : Subgroup SL(2,F)).subtype
    (P : Subgroup SL(2,F)).subtype_injective
  have h9 : 3^2 ∣ Nat.card SL(2,F) := by
    rw [GorensteinWalter.sl2_card_formula,hF]
    norm_num
  have h9P := P.pow_dvd_card_of_pow_dvd_card h9
  obtain ⟨x,hx⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic P)
  obtain ⟨b,hb⟩ := hf x
  have h9x : 9 ∣ orderOf (x : SL(2,F)) := by rwa [orderOf_coe,hx]
  have h9b := h9x.trans (hb ▸ orderOf_map_dvd f b)
  exact Sporadic.Mathieu.m24_not_nine_dvd_orderOf b (by simpa only [orderOf_coe] using h9b)

private theorem m24_not_binary (e : G ≃* Sporadic.Mathieu.M24)
    (S : Sylow 2 G) (B : Subgroup G) (hl : B ∈ localCComponents S)
    (hnorm : (S : Subgroup G) ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) : False := by
  have hd := (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
  rw [binary_card hm,Nat.card_congr e.toEquiv,Sporadic.Mathieu.m24_order] at hd
  have hp : 2^n ∣ 244823040 := (dvd_mul_right _ _).trans hd
  have hb : n < 11 := by
    by_contra! h
    have hh := (show 2^11 ∣ 2^n from pow_dvd_pow 2 h).trans hp
    norm_num at hh
  have hn23 : n = 2 ∨ n = 3 := by
    interval_cases n <;> norm_num at hn ⊢ <;> norm_num at hd
  rcases hn23 with rfl | rfl
  · let a := (binary_four_alt B hm).some
    by_cases hc : pCore 2 B = ⊥
    · let b : B ≃* alternatingGroup (Fin 5) := QuotientGroup.quotientBot.symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hc).symm.trans a)
      exact SourceEmbeddings.AlternatingFive.not_sporadic S hl hnorm b .m24 (by intro h; cases h) ⟨e⟩
    · exact SourceEmbeddings.FiveLocalFF.MathieuTwentyFour.not_section e S B hl hnorm hc a
  · exact binary_not_local_equiv e S B hl (by decide) hm
      (fun _ A _ hA => m24_not_eight A hA)


/-- The two large sporadic candidates remaining in the simple-carrier reduction. -/
@[expose] def LargeSporadicCarrier (A : Type*) [Group A] : Prop :=
  Nonempty (A ≃* Sporadic.Mathieu.M24) ∨ Nonempty (A ≃* Held.He)

/-- Neither M₂₄ nor Held contains a normalized local component whose own
 two-core quotient is a nonbinary PSL₂. -/
theorem not_local_large_sporadic
    (S : Sylow 2 G) (B : Subgroup G) (hl : B ∈ localCComponents S)
    (hnorm : (S : Subgroup G) ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hmodel : LargeSporadicCarrier G) : False := by
  rcases hmodel with h | h
  · exact m24_not_binary h.some S B hl hnorm hn hm
  · exact held_not_binary h.some S B hl hnorm hn hm

private theorem local_not_large_sporadic
    (P : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents P) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hPB : (P : Subgroup G) ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hmodel : LargeSporadicCarrier (K ⧸ pCore 2 K)) : False := by
  obtain ⟨R,hPR,hR⟩ := SourceEmbeddings.exists_local_sylow_restriction P hB hBK hK.subnormal
  let C := B.subgroupOf K
  have hnR : (R : Subgroup K) ≤ normalizer (C : Set K) := by
    rw [hPR]
    intro x hx
    apply mem_normalizer_iff.mpr
    intro b
    exact mem_normalizer_iff.mp (hPB hx) (b : G)
  let q := QuotientGroup.mk' (pCore 2 K)
  let : Group.IsNilpotent (pCore 2 K) := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  have hk : IsPGroup 2 (q.subgroupMap C).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let b := subgroupOfEquivOfLe hBK
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let a := (q.subgroupMap C).quotientPCoreEquivOfSurjective (q.subgroupMap_surjective C) hk
  exact not_local_large_sporadic (R.mapSurjective (QuotientGroup.mk'_surjective _))
    (C.map q) (Chapter1.Section02.localCComponents_map_of_solvable_ker hR q)
    ((map_mono (f := q) hnR).trans (C.le_normalizer_map q)) hn
    (hm.of_mulEquiv (a.symm.trans bq)) hmodel

/-- The actual smaller two-core and relative Sylow are retained when
excluding M₂₄ and Held for the containing component. -/
theorem relative_not_large_sporadic
    {H B K P : Subgroup G} (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    (hPB : P ≤ normalizer (B : Set G)) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) :
    ¬ LargeSporadicCarrier (K ⧸ pCore 2 K) := by
  intro hmodel
  obtain ⟨P₀,hP₀⟩ := hP
  have hPH : P ≤ H := hP₀ ▸ map_subtype_le (P₀ : Subgroup H)
  have hBH : B ≤ H := hBK.trans hK.1
  have hlocal : B.subgroupOf H ∈ localCComponents P₀ := by
    have hh := (Chapter1.mem_LIn_iff_subgroupOf hPH hBH).mp ⟨hBH,hB⟩
    have he : P.subgroupOf H = (P₀ : Subgroup H) := by
      rw [←hP₀]
      exact comap_map_eq_self_of_injective H.subtype_injective _
    rw [he] at hh
    exact hh.1
  have hnP : (P₀ : Subgroup H) ≤ normalizer (B.subgroupOf H : Set H) := by
    intro x hx
    have hxP : (x : G) ∈ P := hP₀ ▸ mem_map_of_mem H.subtype hx
    apply mem_normalizer_iff.mpr
    intro b
    exact mem_normalizer_iff.mp (hPB hxP) (b : G)
  let b := subgroupOfEquivOfLe hBH
  let k := subgroupOfEquivOfLe hK.1
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let kq := QuotientGroup.congr _ _ k (pCore_map_iso 2 k)
  apply local_not_large_sporadic P₀ hlocal hK.2 (comap_mono hBK) hnP hn
    (hm.of_mulEquiv bq)
  rcases hmodel with hmodel | hmodel
  all_goals obtain ⟨e⟩ := hmodel
  · exact .inl ⟨kq.trans e⟩
  · exact .inr ⟨kq.trans e⟩

/-- The exhaustive simple-quotient branch of source 11.1.1. The actual
SQTK hypothesis supplies the catalogue and all its excluded rows are discharged. -/
theorem relative_simple_component_alternative
    {H B K P : Subgroup G} (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    (hPB : P ≤ normalizer (B : Set G)) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    [IsSimpleGroup (K ⧸ pCore 2 K)] : ComponentAlternative B K n := by
  rcases relative_simple_source_without_small_mathieu hH hP hB hK hBK hPB hn hm with h | h
  · exact h
  · exact (relative_not_large_sporadic hP hB hK hBK hPB hn hm h).elim

open CFSG.Quasithin.Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The excluded M₂₄ and Held rows at both original flag normalizers. -/
theorem flag_not_large_sporadic (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) : ¬ LargeSporadicCarrier (K ⧸ pCore 2 K) := by
  have hTV : (T : Subgroup G) ≤ normalizer (f.Vi i.castSucc : Set G) := f.invariant i.castSucc
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      (normalizer (f.Vi i.castSucc : Set G)) :=
    ⟨T.subtype hTV,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTV]⟩
  exact relative_not_large_sporadic hs (flag_mem_local_of_model D S f i hm)
    hK hLK (f.sylow_normalizes_Li i) S.nonbinary hm

/-- The arbitrary nontrivial subspace clause retains the source's literal
N_T(U) Sylow subgroup and the pointwise action on V₁. -/
theorem subspace_not_large_sporadic
    (U : Subgroup G) (hU : U ≠ ⊥) (hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K) : ¬ LargeSporadicCarrier (K ⧸ pCore 2 K) := by
  let : IsElementaryAbelian 2 (f.Vi 0) :=
    D.centralQuotientPreimage_elementary (c.binarySubspace (f.space 0))
  have htwo : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 (f.Vi 0)).to_le hUV
  have hUL : f.Li 0 ≤ normalizer (U : Set G) :=
    (hfix.trans (centralizer_le hUV)).trans (Subgroup.centralizer_le_normalizer _)
  let P := (T : Subgroup G) ⊓ normalizer (U : Set G)
  have hUP : U ≤ P := le_inf
    (hUV.trans ((D.centralQuotientPreimage_le _).trans D.le_sylow)) U.le_normalizer
  have hcore : U ≤ (f.Li 0 ⊔ P).pCoreIn 2 :=
    le_pCoreIn_of_normalizes htwo (hUP.trans le_sup_right) (sup_le hUL inf_le_right)
  have hlocal := flag_mem_local_of_model D S f 0 hm
  have hlocalP : f.Li 0 ∈ Chapter1.L G P :=
    ⟨hlocal.1.subgroupOf_of_le le_sup_left (sup_le_sup_left inf_le_left _),
      hSyl.restrict le_sup_right (sup_le hUL inf_le_right),
      fun he => hU (bot_unique (he ▸ hcore))⟩
  exact relative_not_large_sporadic hSyl hlocalP hK hLK (inf_le_left.trans (f.sylow_normalizes_Li 0)) S.nonbinary hm

/-- Complete the simple-quotient embedding list at both original flag
normalizers, retaining the original coordinate flag and full V₂. -/
theorem flag_simple_component_alternative (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) [IsSimpleGroup (K ⧸ pCore 2 K)] :
    ComponentAlternative (f.Li i) K S.field.degree := by
  rcases flag_simple_source_without_small_mathieu D S f i hm hK hLK with h | h
  · exact h
  · exact (flag_not_large_sporadic D S f i hm hK hLK h).elim

/-- The complete simple-quotient embedding list for each eligible nontrivial
subspace of V₁, with the literal N_T(U) Sylow condition. -/
theorem subspace_simple_component_alternative
    (U : Subgroup G) (hU : U ≠ ⊥) (hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K) [IsSimpleGroup (K ⧸ pCore 2 K)] :
    ComponentAlternative (f.Li 0) K S.field.degree := by
  rcases subspace_simple_source_without_small_mathieu D S f U hU hUV hSyl hm hfix hK hLK with h | h
  · exact h
  · exact (subspace_not_large_sporadic D S f U hU hUV hSyl hm hfix hK hLK h).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
