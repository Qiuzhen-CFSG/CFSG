module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.CenterlessSource
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.IndecomposableFactors
public import Theory.GroupTheory.PResidual.NormalizedSupplement

/-!
# Normalizer action on the odd axes of commuting residual factors

Two commuting conjugate factors split an odd complement of order p² into
its order-p intersections. The two-residuals of the corresponding intersections
with X generate X. Their images in X/Z(X) have at most one odd prime factor
in their orders; two-perfectness makes them directly indecomposable. The
centerless product theorem then permutes these images, and the odd trace
recovers the literal complement axes.

This argument uses no Sylow irreducibility for a smaller point centralizer.
Source: Aschbacher--Smith, 13.1.12(3), p.875; the residual-factor proof of
1.3.8, p.514, and the centerless case of A.1.15, p.23.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.RadicalExclusions Chapter1.RadicalExclusions.BlockRigidity

private theorem indecomposable_of_card_dvd {D : Type*} [Group D] [Finite D]
    {p n : ℕ} (hp : p.Prime) (ho : Odd p) (hD : IsPPerfect 2 D)
    (hne : Nontrivial D) (hc : Nat.card D ∣ 2 ^ n * p) : DirectlyIndecomposable D := by
  refine ⟨hne, fun A B hd hcomm hgen => ?_⟩
  obtain ⟨e₀, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  let e : A × B ≃* D := e₀.trans ((MulEquiv.subgroupCongr hgen).trans topEquiv)
  have hcard : Nat.card A * Nat.card B = Nat.card D :=
    (Nat.card_prod A B).symm.trans (Nat.card_congr e.toEquiv)
  have hA : IsPPerfect 2 A := hD.of_surjective
    ((MonoidHom.fst A B).comp e.symm.toMonoidHom)
    (fun a => ⟨e (a, 1), by simp⟩)
  have hB : IsPPerfect 2 B := hD.of_surjective
    ((MonoidHom.snd A B).comp e.symm.toMonoidHom)
    (fun b => ⟨e (1, b), by simp⟩)
  have hbot (C : Subgroup D) (hC : IsPPerfect 2 C) (hpc : ¬ p ∣ Nat.card C) : C = ⊥ := by
    have hdiv : Nat.card C ∣ 2 ^ n :=
      (hp.coprime_iff_not_dvd.mpr hpc).symm.dvd_of_dvd_mul_right
        (C.card_subgroup_dvd_card.trans hc)
    have he := hC.hom_eq_one_of_isPGroup (IsPGroup.of_card_dvd_pow hdiv) (MonoidHom.id C)
    apply eq_bot_iff.mpr
    intro c hc
    exact congrArg Subtype.val (DFunLike.congr_fun he ⟨c, hc⟩)
  by_cases ha : p ∣ Nat.card A
  · by_cases hb : p ∣ Nat.card B
    · have hdvd : p * p ∣ 2 ^ n * p := (hcard ▸ Nat.mul_dvd_mul ha hb).trans hc
      have hp2 : p ∣ 2 ^ n := Nat.dvd_of_mul_dvd_mul_right hp.pos hdvd
      exact False.elim (hp.ne_one (Nat.eq_one_of_dvd_coprimes (ho.coprime_two_right.pow_right n) dvd_rfl hp2))
    · exact Or.inr (hbot B hB hb)
  · exact Or.inl (hbot A hA ha)


private theorem odd_inf_sup_center {D : Type*} [Group D]
    {p : ℕ} {P W : Subgroup D} [W.Normal]
    (hp : Odd p) (hP : IsPGroup p P) (hZ : IsPGroup 2 (center D)) :
    P ⊓ (W ⊔ center D) = P ⊓ W := by
  apply le_antisymm ?_ (inf_le_inf_left _ le_sup_left)
  intro a ha
  let q := QuotientGroup.mk' W
  have hqaP : q a ∈ P.map q := mem_map.mpr ⟨a, ha.1, rfl⟩
  have hqaZ : q a ∈ (center D).map q := by
    have hm : q a ∈ (W ⊔ center D).map q := mem_map.mpr ⟨a, ha.2, rfl⟩
    simpa only [Subgroup.map_sup, q, QuotientGroup.map_mk'_self, bot_sup_eq] using hm
  have he : q a = 1 := disjoint_def.mp
    ((hP.map q).disjoint_of_coprime (hZ.map q) hp.coprime_two_right) hqaP hqaZ
  exact ⟨ha.1, (QuotientGroup.eq_one_iff a).mp he⟩


variable {G : Type*} [Group G] [Finite G]

/-- Commuting conjugate factors force the actual normalizer to permute the
order-p intersections. All cores and residuals remain on their literal carriers. -/
theorem normalizer_permutates_commuting_odd_axes
    {p : ℕ} [Fact p.Prime] {X P K : Subgroup G} {t : G}
    (ho : Odd p) (hXP : IsPPerfect 2 X)
    (hPX : P ≤ X) (hP : IsPGroup p P)
    (hsup : X.pCoreIn 2 ⊔ P = X) (hdis : Disjoint (X.pCoreIn 2) P)
    (hcard : Nat.card P = p ^ 2) (haxis : Nat.card (P ⊓ K : Subgroup G) = p)
    (hXK : X ≤ normalizer (K : Set G)) (htX : t ∈ normalizer (X : Set G))
    (htP : t ∈ normalizer (P : Set G))
    (hgenP : P = (P ⊓ K) ⊔ (P ⊓ K).conjBy t)
    (hcommK : ⁅K,K.conjBy t⁆ = ⊥)
    (hZ : IsPGroup 2 (center X)) (hz : center (X ⧸ center X) = ⊥) :
    ∀ g ∈ normalizer (X : Set G) ⊓ normalizer (P : Set G),
      (P ⊓ K).conjBy g = P ⊓ K ∨
        (P ⊓ K).conjBy g = (P ⊓ K).conjBy t := by
  let W := blockResidual X K
  let V := W.conjBy t
  let Z := (center X).map X.subtype
  have hWX : W ≤ X := (blockResidual_le X K).trans inf_le_left
  have hWtwo : IsPPerfect 2 W := blockResidual_isPPerfect X K
  have hXW : X ≤ normalizer W := normalizes_blockResidual X.le_normalizer hXK
  have htXe : X.map (MulAut.conj t).toMonoidHom = X :=
    mem_normalizer_iff_map_conj_eq.mp htX
  have hVX : V ≤ X := by
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hWX
    rwa [htXe] at hh
  have hXV : X ≤ normalizer V := by
    have hh := (map_mono (f := (MulAut.conj t).toMonoidHom) hXW).trans
      (W.le_normalizer_map (MulAut.conj t).toMonoidHom)
    rwa [htXe] at hh
  have hPW : P ⊓ K ≤ W := by
    intro a ha
    refine mem_map.mpr ⟨⟨a,hPX ha.1,ha.2⟩,mem_pResidual_of_orderOf_coprime ?_,rfl⟩
    have hc := (hP.orderOf_coprime ho.coprime_two_right ⟨a,ha.1⟩).symm
    simpa only [← Subgroup.orderOf_coe] using hc
  have htraceW : P ⊓ W = P ⊓ K := le_antisymm
    (inf_le_inf_left P ((blockResidual_le X K).trans inf_le_right))
    (le_inf inf_le_left hPW)
  have hPV : P ≤ W ⊔ V := hgenP ▸ sup_le_sup hPW
    (map_mono (f := (MulAut.conj t).toMonoidHom) hPW)
  have hXWV : X ≤ normalizer (W ⊔ V : Subgroup G) :=
    (le_inf hXW hXV).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hgen : W ⊔ V = X := by
    apply le_antisymm (sup_le hWX hVX)
    apply le_of_isPPerfect_of_le_sup_of_normalizes X (W ⊔ V) (X.pCoreIn 2)
      hXP (isPGroup_pCoreIn 2 _) ((pCoreIn_le 2 _).trans hXWV)
    exact hsup.symm.le.trans (sup_le le_sup_right (hPV.trans le_sup_left))
  have hcomm : ⁅W,V⁆ = ⊥ := blockResidual_commute hcommK
  have htrace : P ⊓ (W ⊔ Z) = P ⊓ K := by
    let _ : (W.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer hXW
    have he := odd_inf_sup_center (P := P.subgroupOf X) (W := W.subgroupOf X)
      ho hP.comap_subtype hZ
    have hm := congrArg (map X.subtype) he
    rw [map_inf _ _ _ X.subtype_injective,Subgroup.map_sup,
      map_subgroupOf_eq_of_le hPX,map_subgroupOf_eq_of_le hWX,
      map_inf _ _ _ X.subtype_injective,map_subgroupOf_eq_of_le hPX,
      map_subgroupOf_eq_of_le hWX] at hm
    exact hm.trans htraceW
  have hWcard : ∃ n, Nat.card W ∣ 2 ^ n * p := by
    have hi : W ⊓ P = P ⊓ K := (inf_comm W P).trans htraceW
    have hw := card_mul_eq_card_inf_mul_card_sup_of_normalizes W P (hPX.trans hXW)
    rw [hi,haxis,hcard] at hw
    have hw' : Nat.card W * p = Nat.card (W ⊔ P : Subgroup G) := by
      nlinarith [(Fact.out : p.Prime).pos]
    obtain ⟨n,hn⟩ := (isPGroup_pCoreIn 2 X).exists_card_eq
    have hcX : Nat.card X = 2 ^ n * p ^ 2 := by
      rw [← hsup,card_sup_eq_mul_of_normalizes_of_disjoint]
      · rw [hn,hcard]
      · exact hPX.trans (X.le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
      · exact hdis
    refine ⟨n,Nat.dvd_of_mul_dvd_mul_right (Fact.out : p.Prime).pos ?_⟩
    rw [hw',mul_assoc,← pow_two,← hcX]
    exact card_dvd_of_le (sup_le hWX hPX)
  have hn : Nontrivial (centerFactor X W) := by
    apply (nontrivial_iff_ne_bot _).mpr
    intro hb
    have he := centerFactor_preimage hWX
    rw [hb,MonoidHom.comap_bot,QuotientGroup.ker_mk'] at he
    have hh := htrace
    rw [← he] at hh
    have hd := hP.disjoint_of_coprime (hZ.map X.subtype) ho.coprime_two_right
    have hbot : P ⊓ K = ⊥ := hh.symm.trans hd.eq_bot
    rw [hbot,Subgroup.card_bot] at haxis
    exact (Fact.out : p.Prime).ne_one haxis.symm
  obtain ⟨n,hncard⟩ := hWcard
  have hW : DirectlyIndecomposable (centerFactor X W) :=
    indecomposable_of_card_dvd (Fact.out : p.Prime) ho
      (centerFactor_isPPerfect hWX hWtwo) hn ((centerFactor_card_dvd hWX).trans hncard)
  obtain ⟨ev,_⟩ := centerFactor_conjBy_equiv hWX htX
  let _ := hn
  have hvn : Nontrivial (centerFactor X V) := ev.injective.nontrivial
  have hcV : Nat.card (centerFactor X V) ∣ 2 ^ n * p := by
    rw [← Nat.card_congr ev.toEquiv]
    exact (centerFactor_card_dvd hWX).trans hncard
  have hV : DirectlyIndecomposable (centerFactor X V) :=
    indecomposable_of_card_dvd (Fact.out : p.Prime) ho
      ((centerFactor_isPPerfect hWX hWtwo).of_surjective ev.toMonoidHom ev.surjective) hvn hcV
  have hpair := centerFactor_pair_of_centerless hgen hcomm hW hV hz
  have hZt : Z.conjBy t = Z := mem_normalizer_iff_map_conj_eq.mp
    (normalizer_le_normalizer_characteristic_image X (center X) htX)
  have htraceV : P ⊓ (V ⊔ Z) = (P ⊓ K).conjBy t := by
    rw [← htrace]
    change _ = (P ⊓ (W ⊔ Z)).map (MulAut.conj t).toMonoidHom
    rw [map_inf _ _ _ (MulAut.conj t).injective,Subgroup.map_sup]
    change _ = P.conjBy t ⊓ (V ⊔ Z.conjBy t)
    rw [show P.conjBy t = P from mem_normalizer_iff_map_conj_eq.mp htP,hZt]
  intro g hg
  have he : (P ⊓ K).conjBy g = P ⊓ (W ⊔ Z).conjBy g := by
    rw [← htrace]
    change (P ⊓ (W ⊔ Z)).map (MulAut.conj g).toMonoidHom = _
    rw [map_inf _ _ _ (MulAut.conj g).injective]
    change P.conjBy g ⊓ (W ⊔ Z).conjBy g = _
    rw [show P.conjBy g = P from mem_normalizer_iff_map_conj_eq.mp hg.2]
  rcases (hpair g hg.1).1 with ha | hb
  · exact Or.inl (he.trans ((congrArg (fun A => P ⊓ A) ha).trans htrace))
  · exact Or.inr (he.trans ((congrArg (fun A => P ⊓ A) hb).trans htraceV))

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
