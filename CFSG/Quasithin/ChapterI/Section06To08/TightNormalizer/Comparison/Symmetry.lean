module

public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Basic
public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Comparison.Proper

/-!
# Symmetric Sylow comparison

This module supplies the conditional order comparison used in I.7.7(2--3).
The lower bound for every setup remains an explicit input, to be discharged
by the assembly owner from the proper and full-normalizer branches.

Extend the first normalizer factor `S₁` to a Sylow image `S₂` in
`Kᵍ ∩ N_G(K)`. The lower bound makes `S₂` nontrivial. Conjugate tightness
and inverse conjugation permit the reversed setup, using a Sylow overgroup
of `S₂` in `KS₂`. Its first factor lies in `K ∩ N_G(Kᵍ)`, so its order
is at most that of the given Sylow subgroup `R`. Thus
`|R| ≤ |S₁| ≤ |S₂| ≤ |R|`, and containment with equal orders gives `S₁ = S₂`.
All Sylow witnesses below are actual subgroups of the specified normalizers.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, I.7.7 proof, printed p.427 (PDF p.438).
As in `TightNormalizer.Basic`, conjugation is left conjugation.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem tight_map_equiv {G' : Type*} [Group G']
    {K : Subgroup G} (hK : Theory.GroupTheory.IsTightlyEmbedded K) (e : G ≃* G') :
    Theory.GroupTheory.IsTightlyEmbedded (K.map e.toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · simpa only [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective] using hK.1
  · intro g hg
    have hn : e.symm g ∉ normalizer (K : Set G) := by
      intro hn
      apply hg
      rw [← Subgroup.map_equiv_normalizer_eq K e]
      exact ⟨e.symm g, hn, e.apply_symm_apply g⟩
    have heq : (K.map e.toMonoidHom) ⊓
        (K.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom =
        (K ⊓ K.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_inf _ _ e.toMonoidHom e.injective]
      congr 1
      ext x
      simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
        map_mul, map_inv]
    rw [heq, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact hK.2 _ hn

private theorem card_le_sylow_of_isPGroup {L T : Subgroup G}
    (hT : IsPGroup 2 T) (P : Sylow 2 L) (hTL : T ≤ L) :
    Nat.card T ≤ Nat.card P := by
  let T' := T.subgroupOf L
  have hT' : IsPGroup 2 T' := hT.of_equiv (subgroupOfEquivOfLe hTL).symm
  obtain ⟨Q, hTQ⟩ := hT'.exists_le_sylow
  have hc : Nat.card Q = Nat.card P := by
    rw [Sylow.card_eq_multiplicity Q, Sylow.card_eq_multiplicity P]
  have hTP : Nat.card T' ≤ Nat.card Q := card_le_of_le hTQ
  have heq : Nat.card T' = Nat.card T := by
    simpa only [T'] using Nat.card_congr (subgroupOfEquivOfLe hTL).toEquiv
  rw [heq, hc] at hTP
  exact hTP

omit [Finite G] in
private theorem image_maximal (L : Subgroup G) (P : Sylow 2 L)
    (T : Subgroup G) (hp : IsPGroup 2 T) (hT : T ≤ L)
    (hPT : (P : Subgroup L).map L.subtype ≤ T) :
    T ≤ (P : Subgroup L).map L.subtype := by
  have heq := P.is_maximal'
    (hp.of_equiv (subgroupOfEquivOfLe hT).symm) (map_le_iff_le_comap.mp hPT)
  rw [← map_subgroupOf_eq_of_le hT, heq]

omit [Finite G] in
private theorem sylow_of_maximal {A L : Subgroup G}
    (hp : IsPGroup 2 A) (hle : A ≤ L)
    (hm : ∀ T : Subgroup G, IsPGroup 2 T → T ≤ L → A ≤ T → T ≤ A) :
    ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = A := by
  obtain ⟨P, hP⟩ := (hp.of_equiv (subgroupOfEquivOfLe hle).symm).exists_le_sylow
  have ha : A ≤ (P : Subgroup L).map L.subtype := by
    rw [← map_subgroupOf_eq_of_le hle]
    exact map_mono hP
  exact ⟨P, le_antisymm (hm _ (P.isPGroup'.map _) (map_subtype_le _) ha) ha⟩

/-- Symmetric comparison for a fixed setup, conditional on the lower bound
for every setup. The displayed Sylow subgroup is an actual Sylow subgroup
of the opposite normalizer whose ambient image is the first factor. -/
theorem TightNormalizerSetup.symmetric_comparison
    (lower : ∀ (K : Subgroup G) (g : G) (R S : Subgroup G),
      TightNormalizerSetup K g R S →
      Nat.card R ≤ Nat.card ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)))
    {K : Subgroup G} {g : G} {R S : Subgroup G}
    (h : TightNormalizerSetup K g R S) :
    let S1 := (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)
    Nat.card S1 = Nat.card R ∧
      ∃ P : Sylow 2 ↥(conjSubgroup K g ⊓ normalizer (K : Set G)),
        (P : Subgroup _).map
          (conjSubgroup K g ⊓ normalizer (K : Set G)).subtype = S1 := by
  let S1 : Subgroup G := (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)
  let A : Subgroup G := conjSubgroup K g ⊓ normalizer (K : Set G)
  let B : Subgroup G := K ⊓ normalizer (conjSubgroup K g : Set G)
  have hS1A : S1 ≤ A := h.factor_le_opposite
  have hS1S : S1 ≤ S := inf_le_left.trans inf_le_left
  have hS1p : IsPGroup 2 S1 :=
    (h.hSp.to_subgroup (S1.subgroupOf S)).of_equiv (subgroupOfEquivOfLe hS1S)
  obtain ⟨P, hS1P⟩ := (hS1p.of_equiv (subgroupOfEquivOfLe hS1A).symm).exists_le_sylow
  let S2 : Subgroup G := (P : Subgroup A).map A.subtype
  have hS1map : S1 ≤ S2 := by
    rw [← map_subgroupOf_eq_of_le hS1A]
    exact map_mono hS1P
  have hlow : Nat.card R ≤ Nat.card S1 := lower K g R S h
  have hS1S2card : Nat.card S1 ≤ Nat.card S2 := card_le_of_le hS1map
  have hS2ne : S2 ≠ ⊥ := by
    intro hz
    have hRcard : 1 < Nat.card R := R.one_lt_card_iff_ne_bot.mpr h.hRne
    have hh : Nat.card R ≤ 1 := by
      simpa [hz] using hlow.trans hS1S2card
    omega
  let C : Subgroup G := K ⊔ S2
  have hS2p : IsPGroup 2 S2 := P.isPGroup'.map A.subtype
  have hS2C : S2 ≤ C := le_sup_right
  obtain ⟨U, hS2U⟩ := (hS2p.of_equiv (subgroupOfEquivOfLe hS2C).symm).exists_le_sylow
  let S' : Subgroup G := (U : Subgroup C).map C.subtype
  have hS2S' : S2 ≤ S' := by
    rw [← map_subgroupOf_eq_of_le hS2C]
    exact map_mono hS2U
  have hgrev : g⁻¹ ∉ normalizer (conjSubgroup K g : Set G) := by
    intro hg'
    have heq := mem_normalizer_iff_map_conj_eq.mp hg'
    change conjSubgroup (conjSubgroup K g) g⁻¹ = conjSubgroup K g at heq
    rw [conjSubgroup_inv] at heq
    exact h.hg (mem_normalizer_iff_map_conj_eq.mpr heq.symm)
  have hrev : TightNormalizerSetup (conjSubgroup K g) g⁻¹ S2 S' := by
    refine ⟨tight_map_equiv h.hK (MulAut.conj g), hgrev, hS2p, hS2ne,
      ?_, ?_, U.isPGroup'.map C.subtype, ?_, hS2S', ?_⟩
    · simpa only [conjSubgroup_inv] using (map_subtype_le (P : Subgroup A))
    · simpa only [conjSubgroup_inv] using image_maximal A P
    · simpa only [conjSubgroup_inv] using (map_subtype_le (U : Subgroup C))
    · simpa only [conjSubgroup_inv] using image_maximal C U
  let T : Subgroup G := (S' ⊓ conjSubgroup (conjSubgroup K g) g⁻¹) ⊓
    normalizer (S2 : Set G)
  have hrev_low : Nat.card S2 ≤ Nat.card T := lower _ _ _ _ hrev
  have hTB : T ≤ B := by
    simpa only [T, B, conjSubgroup_inv] using hrev.factor_le_opposite
  have hTS : T ≤ S' := inf_le_left.trans inf_le_left
  have hTp : IsPGroup 2 T :=
    (hrev.hSp.to_subgroup (T.subgroupOf S')).of_equiv (subgroupOfEquivOfLe hTS)
  obtain ⟨RP, hRP⟩ := sylow_of_maximal h.hRp h.hRle h.hRmax
  have hRPcard : Nat.card RP = Nat.card R := by
    rw [← hRP, card_map_of_injective B.subtype_injective]
  have hupper : Nat.card T ≤ Nat.card R := by
    exact (card_le_sylow_of_isPGroup hTp RP hTB).trans_eq hRPcard
  have hS2R : Nat.card S2 ≤ Nat.card R := hrev_low.trans hupper
  have heq : Nat.card S1 = Nat.card R :=
    Nat.le_antisymm (hS1S2card.trans hS2R) hlow
  exact ⟨heq, P, (eq_of_le_of_card_ge hS1map (hS2R.trans hlow)).symm⟩

end CFSG.Quasithin.ChapterI.Section06To08
