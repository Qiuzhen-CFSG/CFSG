module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.LocalStructure.Elementary
public import BenderSuzuki.SE.StrongEmbeddingCounting
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Normalizers and the inverted odd core of the proper residual subgroup

Write `L = ⟨z,t,[O₂′(D),t]⟩`, `D = M ∩ Mᵗ`, `B = M ∩ L`,
`E = D ∩ L`, and let `T` be the ambient image of `O₂(B)`. The local
model inputs are that `E` has odd order and is inverted by `t`, that
`B = TE` as a set product, and that `B` conjugates `t` to every involution
of `L` outside `M`. Together with `D ≤ N_G(L)`, these give the normalizer
products `N_G(L) = LD` and `M ∩ N_G(L) = TD`, and `D ≤ N_G(T)`.

For the product argument, conjugacy corrects an element of `M ∩ N_G(L)`
by an element of `B` so that it centralizes `t` and hence lies in `D`.
The elementary normalizer factorization then gives `LD`. Characteristicity
of the two-core gives normalization of `T`. Relative normality and oddness
put `E` inside `O₂′(D)`. The residual commutator lies in `E`, and odd
powering of inverted elements proves the reverse inclusion and the equality
with the inverted set in `O₂′(D)`.

These are conditional group-theoretic steps for GLS, Volume 4, Chapter 2,
Lemma 12.2(d,f), using the Borel geometry of Chapter 4, Lemma 3.2(c,d,i).
The parent must supply the stated model inputs and the cyclicity and order
of `E`; this module does not assert the full source Lemma 12.2.
Source: `refs/KGroup/GLS4/Chapter2.tex` and `refs/KGroup/GLS4/Chapter4.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
/-- Borel conjugacy of outside involutions corrects the local normalizer into the pair stabilizer. -/
public theorem residual_inter_normalizer_eq_borel_mul_pair
    {z t : G} (ht : PFAppendixIII.IsInvolution t) (htM : t ∉ M)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (htrans : ∀ v ∈ residualGenerated M z t, v ∉ M → PFAppendixIII.IsInvolution v →
      ∃ b ∈ M ⊓ residualGenerated M z t, v = MulAut.conj b t) :
    ((M ⊓ normalizer (residualGenerated M z t : Set G) : Subgroup G) : Set G) =
      ((M ⊓ residualGenerated M z t : Subgroup G) : Set G) *
        (residualPairStabilizer M t : Set G) := by
  let L := residualGenerated M z t
  have htL : t ∈ L := (show zpowers t ≤ L from le_sup_right.trans le_sup_left) (mem_zpowers t)
  ext m
  constructor
  · rintro ⟨hmM, hmN⟩
    have hvL : MulAut.conj m t ∈ L := (mem_normalizer_iff.mp hmN t).mp htL
    have hvM : MulAut.conj m t ∉ M := by
      intro hv
      apply htM
      have hh := M.mul_mem (M.mul_mem (M.inv_mem hmM) hv) hmM
      simpa [MulAut.conj_apply, mul_assoc] using hh
    obtain ⟨b, hb, he⟩ := htrans _ hvL hvM
      (BenderSuzuki.IsInvolution.map_of_injective ht (MulAut.conj m).toMonoidHom
        (MulAut.conj m).injective)
    have hc : (b⁻¹ * m) * t = t * (b⁻¹ * m) := by
      have hh := congrArg (fun x : G => b⁻¹ * x * m) he
      simpa [MulAut.conj_apply, mul_assoc] using hh
    have hdM : b⁻¹ * m ∈ M := M.mul_mem (M.inv_mem hb.1) hmM
    have hd : b⁻¹ * m ∈ residualPairStabilizer M t := by
      refine ⟨hdM, ?_⟩
      change b⁻¹ * m ∈ rightConjugate M t
      rw [rightConjugate, Subgroup.conjBy, mem_map]
      refine ⟨b⁻¹ * m, hdM, ?_⟩
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
      rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
    exact Set.mem_mul.mpr ⟨b, hb, b⁻¹ * m, hd, by group⟩
  · rintro ⟨b, hb, d, hd, rfl⟩
    exact ⟨M.mul_mem hb.1 hd.1, (normalizer (L : Set G)).mul_mem
      (L.le_normalizer hb.2) (hDN hd)⟩

/-- The ambient normalizer is the genuine product `LD`, using local Borel conjugacy. -/
public theorem residual_normalizer_eq_mul_pair
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (htrans : ∀ v ∈ residualGenerated M z t, v ∉ M → PFAppendixIII.IsInvolution v →
      ∃ b ∈ M ⊓ residualGenerated M z t, v = MulAut.conj b t) :
    (normalizer (residualGenerated M z t : Set G) : Set G) =
      (residualGenerated M z t : Set G) * (residualPairStabilizer M t : Set G) := by
  have hzL : z ∈ residualGenerated M z t :=
    (show zpowers z ≤ residualGenerated M z t from le_sup_left.trans le_sup_left)
      (mem_zpowers z)
  rw [normalizer_eq_mul_inter_of_local_strongEmbedding h.disconnected _
      (stronglyEmbedded_in_proper_residualGenerated h.disconnected r hz hzM ht htM hL)
      hz hzM hzL,
    residual_inter_normalizer_eq_borel_mul_pair (h.disconnected.involutions t ht) htM hDN htrans,
    ← mul_assoc]
  have habsorb : (residualGenerated M z t : Set G) *
      ((M ⊓ residualGenerated M z t : Subgroup G) : Set G) =
        (residualGenerated M z t : Set G) := by
    ext x
    constructor
    · rintro ⟨l, hl, b, hb, rfl⟩
      exact (residualGenerated M z t).mul_mem hl hb.2
    · intro hx
      exact ⟨x, hx, 1, (M ⊓ residualGenerated M z t).one_mem, mul_one x⟩
  rw [habsorb]

omit [Finite G] in
/-- The Borel product `B = TE` refines the normalizer intersection to `TD`. -/
public theorem residual_inter_normalizer_eq_twoCore_mul_pair
    {z t : G} (ht : PFAppendixIII.IsInvolution t) (htM : t ∉ M)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (hB : ((M ⊓ residualGenerated M z t : Subgroup G) : Set G) =
      (((pCore 2 (M ⊓ residualGenerated M z t : Subgroup G)).map
        (M ⊓ residualGenerated M z t).subtype : Subgroup G) : Set G) *
      ((residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G) : Set G))
    (htrans : ∀ v ∈ residualGenerated M z t, v ∉ M → PFAppendixIII.IsInvolution v →
      ∃ b ∈ M ⊓ residualGenerated M z t, v = MulAut.conj b t) :
    ((M ⊓ normalizer (residualGenerated M z t : Set G) : Subgroup G) : Set G) =
      (((pCore 2 (M ⊓ residualGenerated M z t : Subgroup G)).map
        (M ⊓ residualGenerated M z t).subtype : Subgroup G) : Set G) *
      (residualPairStabilizer M t : Set G) := by
  rw [residual_inter_normalizer_eq_borel_mul_pair ht htM hDN htrans, hB, mul_assoc]
  congr 1
  ext x
  constructor
  · rintro ⟨e, he, d, hd, rfl⟩
    exact (residualPairStabilizer M t).mul_mem he.1 hd
  · intro hx
    exact ⟨1, (residualPairStabilizer M t ⊓ residualGenerated M z t).one_mem,
      x, hx, one_mul x⟩

omit [Finite G] in
/-- The pair stabilizer preserves the characteristic two-core of the local Borel. -/
public theorem residual_pair_le_normalizer_borel_twoCore
    {z t : G}
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G)) :
    residualPairStabilizer M t ≤ normalizer
      (((pCore 2 (M ⊓ residualGenerated M z t : Subgroup G)).map
        (M ⊓ residualGenerated M z t).subtype : Subgroup G) : Set G) := by
  apply le_trans ?_ (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  exact (le_inf (inf_le_left.trans M.le_normalizer) hDN).trans
    inf_normalizer_le_normalizer_inf

omit [Finite G] in
/-- Oddness and relative normality put the local pair intersection in the pair's odd core. -/
public theorem residual_local_pair_le_oddCore
    {z t : G}
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (hodd : Odd (Nat.card (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G))) :
    residualPairStabilizer M t ⊓ residualGenerated M z t ≤
      (pPrimeCore 2 (residualPairStabilizer M t)).map (residualPairStabilizer M t).subtype := by
  let D := residualPairStabilizer M t
  let E := D ⊓ residualGenerated M z t
  have hED : E ≤ D := inf_le_left
  have hn : D ≤ normalizer (E : Set G) :=
    (le_inf D.le_normalizer hDN).trans inf_normalizer_le_normalizer_inf
  have hnormal : (E.subgroupOf D).Normal :=
    (normal_subgroupOf_iff_le_normalizer hED).mpr hn
  have hcard : Nat.card (E.subgroupOf D) = Nat.card E :=
    Nat.card_congr (subgroupOfEquivOfLe hED).toEquiv
  have hcore : E.subgroupOf D ≤ pPrimeCore 2 D :=
    le_sSup ⟨hnormal, by rw [hcard]; exact hodd.coprime_two_left⟩
  change E ≤ (pPrimeCore 2 D).map D.subtype
  rw [← map_subgroupOf_eq_of_le hED]
  exact map_mono hcore

omit [Finite G] in
private theorem pair_involution_normalizes {t : G} (ht : PFAppendixIII.IsInvolution t) :
    t ∈ normalizer (residualPairStabilizer M t : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (M ⊓ M.conjBy t⁻¹).map (MulAut.conj t).toMonoidHom = M ⊓ M.conjBy t⁻¹
  rw [map_inf _ _ _ (MulAut.conj t).injective]
  change M.conjBy t ⊓ (M.conjBy t⁻¹).conjBy t = M ⊓ M.conjBy t⁻¹
  rw [conjBy_inv', ht.inv_eq_self, inf_comm]

omit [Finite G] in
private theorem residual_commutator_le_odd_core {t : G} (ht : PFAppendixIII.IsInvolution t) :
    residualCommutator M t ≤
      (pPrimeCore 2 (residualPairStabilizer M t)).map (residualPairStabilizer M t).subtype := by
  apply le_normalizer_iff_commutator_le_left.mp
  exact (zpowers_le.mpr (pair_involution_normalizes ht)).trans
    (normalizer_le_normalizer_characteristic_image _ _)

/-- The local inverted odd intersection is exactly the residual action commutator. -/
public theorem residualCommutator_eq_local_pair
    {z t : G} (ht : PFAppendixIII.IsInvolution t)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (hodd : Odd (Nat.card (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G)))
    (hinv : ∀ x ∈ residualPairStabilizer M t ⊓ residualGenerated M z t,
      rightConjugateElem x t = x⁻¹) :
    residualCommutator M t = residualPairStabilizer M t ⊓ residualGenerated M z t := by
  apply le_antisymm
  · exact le_inf ((residual_commutator_le_odd_core ht).trans (map_subtype_le _)) le_sup_right
  · intro x hx
    exact IsStronglyEmbedded.mem_commutator_zpowers_of_mem_peterfalviKSet _
      (by rw [card_map_of_injective Subtype.val_injective]
          exact Nat.coprime_two_left.mp pPrimeCore_coprime_card) ht
      ⟨residual_local_pair_le_oddCore hDN hodd hx, hinv x hx⟩

/-- The inverted-set equality is in `O₂′(D)`, with no inversion claim about all of `D`. -/
public theorem residualCommutator_eq_oddCore_invertedSet
    {z t : G} (ht : PFAppendixIII.IsInvolution t)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (hodd : Odd (Nat.card (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G)))
    (hinv : ∀ x ∈ residualPairStabilizer M t ⊓ residualGenerated M z t,
      rightConjugateElem x t = x⁻¹) :
    (residualCommutator M t : Set G) = {x | x ∈
      (pPrimeCore 2 (residualPairStabilizer M t)).map (residualPairStabilizer M t).subtype ∧
      rightConjugateElem x t = x⁻¹} := by
  ext x
  constructor
  · intro hx
    exact ⟨residual_commutator_le_odd_core ht hx,
      hinv x ((residualCommutator_eq_local_pair ht hDN hodd hinv) ▸ hx)⟩
  · intro hx
    exact IsStronglyEmbedded.mem_commutator_zpowers_of_mem_peterfalviKSet _
      (by rw [card_map_of_injective Subtype.val_injective]
          exact Nat.coprime_two_left.mp pPrimeCore_coprime_card) ht hx

end BenderSuzuki.ZD
