module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha.Geometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha.XiFusion.InvolutionReduction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation.NormalizerAction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.SNormalizer.Overgroups
public import Theory.GroupAction.FiveSixteenCentralizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Orbit reduction for Held's S-fusions

Under pi--mu nonfusion and lambda separation, the pi orbit of the actual
normalizer of S has one or nine elements. The displayed Sylow action has
blocks of sizes 1, 1, 2, 4, 4, 4. Nonfusion excludes the two-element block,
and lambda separation excludes taking both lambda blocks. This leaves orbit
sizes 1, 5, 9. Size five would give an automorphism subgroup of order forty
on S. Its Sylow five-subgroup is normal, but the normalizer of an order-five
subgroup in Aut(S) has order dividing sixty, a contradiction.

In a nine-element orbit pi is fused with tau and exactly one lambda choice.
If mu were not fused with the other choice, its class in S would consist
only of mu and pi*mu. Every S-normalizer would then fix their product pi,
contradicting the nontrivial pi orbit. This proves all three required fusions.
The existing tau-centralizer overgroup construction closes the tau branch.

The source step producing an initial S-fusion from the xi separation, and
the lambda-centralizer overgroup's normalization of S, remain separate
obligations. No theorem here claims the complete separation-only contract.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemmas 2.9--2.11, printed pp.229--230.
The five-normalizer argument replaces the source's A8 subgroup exclusion;
the two-element class argument replaces the extra structural claims in 2.11.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
open Coordinates Fusion Fusion.LambdaSeparation

private theorem aut_subgroup_card_ne_forty {V : Type*} [Group V] [Finite V]
    (hV : Nat.card V = 16) (K : Subgroup (MulAut V)) : Nat.card K ≠ 40 := by
  intro hK
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P : Sylow 5 K := default
  have hP : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, hK, show (40 : ℕ) = 2 ^ 3 * 5 by decide,
      Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization, (show Nat.Prime 5 by decide).factorization]
  have hindex : P.index = 8 := by
    have h := P.toSubgroup.card_mul_index
    rw [hP, hK] at h
    omega
  have hn : Nat.card (Sylow 5 K) = 1 := by
    have hd := P.card_dvd_index
    rw [hindex] at hd
    have hm := card_sylow_modEq_one 5 K
    have hmem := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    have hdiv : (8 : ℕ).divisors = {1, 2, 4, 8} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    change Nat.card (Sylow 5 K) % 5 = 1 % 5 at hm
    omega
  have hnormal : P.Normal := by
    have hidx : (normalizer (P : Set K)).index = 1 :=
      (P.card_eq_index_normalizer).symm.trans hn
    exact normalizer_eq_top_iff.mp (index_eq_one.mp hidx)
  let A := P.toSubgroup.map K.subtype
  have hA : Nat.card A = 5 := by
    rw [card_map_of_injective K.subtype_injective]
    exact hP
  have hKN : K ≤ normalizer (A : Set (MulAut V)) := by
    intro k hk
    apply mem_normalizer_iff.mpr
    intro a
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(⟨k, hk⟩ : K) * p * (⟨k, hk⟩ : K)⁻¹,
        hnormal.conj_mem p hp ⟨k, hk⟩, rfl⟩
    · intro ha
      obtain ⟨p, hp, he⟩ := ha
      refine ⟨(⟨k, hk⟩ : K)⁻¹ * p * (⟨k, hk⟩ : K),
        hnormal.conj_mem p hp (⟨k, hk⟩ : K)⁻¹, ?_⟩
      change k⁻¹ * (p : MulAut V) * k = a
      change (p : MulAut V) = k * a * k⁻¹ at he
      rw [he]
      group
  have hN : Nat.card (normalizer (A : Set (MulAut V))) ∣ 60 := by
    let : IsCyclic A := isCyclic_of_prime_card hA
    have hAut : Nat.card (MulAut A) = 4 := by
      rw [IsCyclic.card_mulAut, hA]
      decide
    let f := A.normalizerMonoidHom
    have hrange : Nat.card f.range ∣ 4 := hAut ▸ f.range.card_subgroup_dvd_card
    have hker : Nat.card f.ker ∣ 15 := by
      have hc := card_centralizer_five_dvd_fifteen (V := V) A hA hV
      have heq : Nat.card f.ker = Nat.card (centralizer (A : Set (MulAut V))) := by
        rw [normalizerMonoidHom_ker,
          Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (A : Set (MulAut V)))).toEquiv]
      rwa [heq]
    have hh := Nat.mul_dvd_mul hker hrange
    have hprod := f.ker.card_mul_index
    rw [index_ker] at hprod
    simpa only [hprod] using hh
  have hd := (card_dvd_of_le hKN).trans hN
  rw [hK] at hd
  norm_num at hd


private def selected (b : Fin 3 → Bool) (a : BaseCode) : Prop :=
  elementaryClass 1 a = 1 ∨ (elementaryClass 1 a = 3 ∧ b 0 = true) ∨
    (elementaryClass 1 a = 4 ∧ b 1 = true) ∨ (elementaryClass 1 a = 5 ∧ b 2 = true)
private instance (b : Fin 3 → Bool) (a : BaseCode) : Decidable (selected b a) := by
  unfold selected
  infer_instance

private theorem selected_nine : ∀ b : Fin 3 → Bool,
    ¬ (b 1 = true ∧ b 2 = true) →
    9 ≤ Fintype.card {a : BaseCode // selected b a} →
    b 0 = true ∧ (b 1 = true ∨ b 2 = true) := by decide +kernel

private theorem class_count_nine (p : H → Prop)
    (hconj : ∀ {x y : H}, IsConj x y → (p x ↔ p y))
    (hone : ¬ p 1) (hpi : p Coordinates.pi) (hmu : ¬ p Coordinates.mu)
    (hlam : ¬ (p lam ∧ p (Coordinates.pi * lam)))
    (hc : 9 ≤ Nat.card {a : BaseCode // p (elementaryWord 1 a)}) :
    p tau ∧ (p lam ∨ p (Coordinates.pi * lam)) := by
  classical
  let b : Fin 3 → Bool := ![decide (p tau), decide (p lam), decide (p (Coordinates.pi * lam))]
  have hs (a : BaseCode) : p (elementaryWord 1 a) ↔ selected b a := by
    rw [← hconj (elementaryWord_isConj 1 a)]
    have hb : (elementaryClass 1 a).val < 6 := by
      have h : ∀ a : BaseCode, (elementaryClass 1 a).val < 6 := by decide +kernel
      exact h a
    unfold selected
    generalize elementaryClass 1 a = i at *
    fin_cases i <;> simp [localRepresentative, b, hone, hpi, hmu]
    all_goals norm_num at hb
  have he := Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl BaseCode) hs)
  rw [he, Nat.card_eq_fintype_card] at hc
  have hb : ¬ (b 1 = true ∧ b 2 = true) := by simpa [b] using hlam
  simpa [b] using selected_nine b hb hc

private theorem class_mu_pair (p : H → Prop)
    (hconj : ∀ {x y : H}, IsConj x y → (p x ↔ p y))
    (hone : ¬ p 1) (hpi : ¬ p Coordinates.pi) (htau : ¬ p tau)
    (hlam : ¬ p lam) (hpiLam : ¬ p (Coordinates.pi * lam))
    {x : H} (hx : x ∈ modelS) (hp : p x) :
    x = Coordinates.mu ∨ x = Coordinates.pi * Coordinates.mu := by
  obtain ⟨a, rfl⟩ := (mem_elementary 1 x).mp hx
  have hl := (hconj (elementaryWord_isConj 1 a)).mpr hp
  have hb : (elementaryClass 1 a).val < 6 := by
    have h : ∀ a : BaseCode, (elementaryClass 1 a).val < 6 := by decide +kernel
    exact h a
  have hm : ∀ a : BaseCode, elementaryClass 1 a = 2 →
      elementaryWord 1 a = Coordinates.mu ∨
        elementaryWord 1 a = Coordinates.pi * Coordinates.mu := by decide +kernel
  generalize hi : elementaryClass 1 a = i at hl hb
  fin_cases i
  · exact (hone hl).elim
  · exact (hpi hl).elim
  · exact hm a hi
  · exact (htau hl).elim
  · exact (hlam hl).elim
  · exact (hpiLam hl).elim
  all_goals norm_num at hb

private theorem lambda_choices (b : Bit) :
    (lam = normalizedLam b ∧ Coordinates.pi * lam = Coordinates.pi * normalizedLam b) ∨
    (lam = Coordinates.pi * normalizedLam b ∧ Coordinates.pi * lam = normalizedLam b) := by
  revert b
  decide +kernel

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

private noncomputable def sWord (a : BaseCode) : ambientElementary D e 1 :=
  ⟨D.a10ModelEmbedding e (elementaryWord 1 a),
    mem_map_of_mem _ ((mem_elementary _ _).mpr ⟨a, rfl⟩)⟩

omit [Finite G] in
private theorem sWord_bijective : Function.Bijective (sWord D e) := by
  constructor
  · intro a b hab
    apply (elementaryWord_bijective 1).injective
    apply Subtype.ext
    exact D.a10ModelEmbedding_injective e (congrArg (fun x : ambientElementary D e 1 => (x : G)) hab)
  · rintro ⟨y, t, ht, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_elementary 1 t).mp ht
    exact ⟨a, rfl⟩

private theorem pi_class_card_ge_orbit :
    (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard ≤
      Nat.card {a : BaseCode // IsConj D.z (D.a10ModelEmbedding e (elementaryWord 1 a))} := by
  let C : Set (ambientElementary D e 1) := {x | IsConj D.z (x : G)}
  have hsub : MulAction.orbit (sNormalizer D e) (piPoint D e) ⊆ C := by
    intro x hx
    obtain ⟨n, hn⟩ := MulAction.mem_orbit_iff.mp hx
    exact isConj_iff.mpr ⟨(n : G), congrArg Subtype.val hn⟩
  have he : {a : BaseCode // IsConj D.z (D.a10ModelEmbedding e (elementaryWord 1 a))} ≃ C :=
    Equiv.subtypeEquiv (Equiv.ofBijective (sWord D e) (sWord_bijective D e)) (fun _ => Iff.rfl)
  have hc : Nat.card {a : BaseCode // IsConj D.z (D.a10ModelEmbedding e (elementaryWord 1 a))} = C.ncard :=
    (Nat.card_congr he).trans (Nat.card_coe_set_eq _)
  rw [hc]
  exact Set.ncard_le_ncard hsub

private theorem tau_lambda_fusion_of_orbit_nine
    (hf : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hl : ¬ (IsConj D.z (D.a10ModelEmbedding e lam) ∧
      IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * lam))))
    (hn : (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard = 9) :
    IsConj D.z (D.a10ModelEmbedding e tau) ∧
      (IsConj D.z (D.a10ModelEmbedding e lam) ∨
        IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * lam))) := by
  apply class_count_nine (fun x => IsConj D.z (D.a10ModelEmbedding e x))
  · intro x y h
    exact ⟨fun hx => hx.trans ((D.a10ModelEmbedding e).map_isConj h),
      fun hy => hy.trans ((D.a10ModelEmbedding e).map_isConj h.symm)⟩
  · intro h
    rw [map_one] at h
    exact D.z_ne_one (isConj_one_left.mp h)
  · rw [D.a10ModelEmbedding_central e]
  · exact hf
  · exact hl
  · simpa only [hn] using pi_class_card_ge_orbit D e

private theorem mu_lambda_fusion_of_moving_pi (b : Bit)
    (hf : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (ht : IsConj D.z (D.a10ModelEmbedding e tau))
    (hpl : IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * normalizedLam b)))
    (hn : 1 < (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard) :
    IsConj (D.a10ModelEmbedding e Coordinates.mu) (D.a10ModelEmbedding e (normalizedLam b)) := by
  by_contra hl
  let f := D.a10ModelEmbedding e
  change ¬ IsConj D.z (f Coordinates.mu) at hf
  have hpl' : ¬ IsConj (f Coordinates.mu) (f (Coordinates.pi * normalizedLam b)) :=
    fun h => hf (hpl.trans h.symm)
  have hll : ¬ IsConj (f Coordinates.mu) (f lam) := by
    rcases lambda_choices b with ⟨h, _⟩ | ⟨h, _⟩
    · simpa only [h] using hl
    · simpa only [h] using hpl'
  have hll' : ¬ IsConj (f Coordinates.mu) (f (Coordinates.pi * lam)) := by
    rcases lambda_choices b with ⟨_, h⟩ | ⟨_, h⟩
    · simpa only [h] using hpl'
    · simpa only [h] using hl
  have hmu1 : f Coordinates.mu ≠ 1 := by
    intro h
    have hm : Coordinates.mu ≠ 1 := by decide +kernel
    exact hm (D.a10ModelEmbedding_injective e (h.trans (map_one f).symm))
  have hpair (x : H) (hx : x ∈ modelS) (hm : IsConj (f Coordinates.mu) (f x)) :
      x = Coordinates.mu ∨ x = Coordinates.pi * Coordinates.mu := by
    apply class_mu_pair (fun x => IsConj (f Coordinates.mu) (f x)) (fun h =>
      ⟨fun hx => hx.trans (f.map_isConj h), fun hy => hy.trans (f.map_isConj h.symm)⟩)
      (fun h => hmu1 (isConj_one_left.mp (by simpa only [map_one] using h)))
      (fun h => hf (by simpa only [f, D.a10ModelEmbedding_central e] using h.symm))
      (fun h => hf (ht.trans h.symm)) hll hll' hx hm
  have hmu : Coordinates.mu ∈ modelS := mu_mem_elementary 1
  have hpmu : Coordinates.pi * Coordinates.mu ∈ modelS :=
    modelS.mul_mem (pi_mem_elementary 1) hmu
  have hconj : IsConj Coordinates.mu (Coordinates.pi * Coordinates.mu) := by
    apply isConj_iff.mpr
    exact ⟨taup, by decide +kernel⟩
  have hprod : Coordinates.mu * (Coordinates.pi * Coordinates.mu) = Coordinates.pi := by
    decide +kernel
  have hprod' : (Coordinates.pi * Coordinates.mu) * Coordinates.mu = Coordinates.pi := by
    decide +kernel
  have hne : f Coordinates.mu ≠ f (Coordinates.pi * Coordinates.mu) := by
    intro h
    have hm : Coordinates.mu ≠ Coordinates.pi * Coordinates.mu := by decide +kernel
    exact hm (D.a10ModelEmbedding_injective e h)
  have hfix (n : sNormalizer D e) : n • piPoint D e = piPoint D e := by
    let c := MulAut.conj (n : G)
    have hmap (x : H) (hx : x ∈ modelS) (hm : IsConj Coordinates.mu x) :
        c (f x) = f Coordinates.mu ∨ c (f x) = f (Coordinates.pi * Coordinates.mu) := by
      have hxS : f x ∈ ambientElementary D e 1 := mem_map_of_mem f hx
      have hyS : c (f x) ∈ ambientElementary D e 1 :=
        (n • (⟨f x, hxS⟩ : ambientElementary D e 1)).property
      obtain ⟨y, hy, he⟩ := hyS
      have hyc : IsConj (f Coordinates.mu) (f y) := by
        rw [he]
        exact (f.map_isConj hm).trans (isConj_iff.mpr ⟨(n : G), rfl⟩)
      rcases hpair y hy hyc with h | h
      · exact Or.inl (he.symm.trans (congrArg f h))
      · exact Or.inr (he.symm.trans (congrArg f h))
    have h1 := hmap Coordinates.mu hmu (IsConj.refl _)
    have h2 := hmap (Coordinates.pi * Coordinates.mu) hpmu hconj
    have hcp : c (f Coordinates.pi) = f Coordinates.pi := by
      rw [← hprod, map_mul, map_mul]
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact (hne (c.injective (h1.trans h2.symm))).elim
      · rw [h1, h2]
      · rw [h1, h2, ← map_mul, hprod', ← map_mul, hprod]
      · exact (hne (c.injective (h1.trans h2.symm))).elim
    apply Subtype.ext
    change c D.z = D.z
    simpa only [f, D.a10ModelEmbedding_central e] using hcp
  have hsub : MulAction.orbit (sNormalizer D e) (piPoint D e) ⊆ {piPoint D e} := by
    intro x hx
    obtain ⟨n, rfl⟩ := MulAction.mem_orbit_iff.mp hx
    exact hfix n
  have hc := Set.ncard_le_ncard hsub
  rw [Set.ncard_singleton] at hc
  omega

/-- The nine-point pi orbit forces precisely the three S-fusions needed later.
This does not assert the normalizer argument producing that orbit. -/
public theorem exists_s_fusion_of_orbit_nine
    (hf : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hl : ¬ (IsConj D.z (D.a10ModelEmbedding e lam) ∧
      IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * lam))))
    (hn : (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard = 9) :
    ∃ b : Bit, IsConj D.z (D.a10ModelEmbedding e tau) ∧
      IsConj (D.a10ModelEmbedding e Coordinates.mu)
        (D.a10ModelEmbedding e (normalizedLam b)) ∧
      IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * normalizedLam b)) := by
  obtain ⟨ht, hchoices⟩ := tau_lambda_fusion_of_orbit_nine D e hf hl hn
  have hn' : 1 < (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard := by omega
  rcases hchoices with h | h
  · have hp : IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * normalizedLam 1)) := by
      have he : Coordinates.pi * normalizedLam 1 = lam := by decide +kernel
      rwa [he]
    exact ⟨1, ht, mu_lambda_fusion_of_moving_pi D e 1 hf ht hp hn', hp⟩
  · have hp : IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * normalizedLam 0)) := by
      simpa only [normalizedLam, Fin.val_zero, pow_zero, one_mul] using h
    exact ⟨0, ht, mu_lambda_fusion_of_moving_pi D e 0 hf ht hp hn', hp⟩


private abbrev SConjCode := Fin 2 × Fin 2 × Fin 2
private def sConjugator (b : SConjCode) : H := mup ^ b.1.val * taup ^ b.2.1.val * xi ^ b.2.2.val

private theorem sConjugator_mem (b : SConjCode) : sConjugator b ∈ modelD := by
  have h (i : Fin 7) : (![Coordinates.pi, Coordinates.mu, mup, tau, taup, lam, xi] : Fin 7 → H) i ∈ modelD :=
    subset_closure ⟨i, rfl⟩
  exact modelD.mul_mem (modelD.mul_mem (modelD.pow_mem (h 2) _)
    (modelD.pow_mem (h 4) _)) (modelD.pow_mem (h 6) _)

private theorem sConjugator_table : ∀ a : BaseCode, ∃ b : SConjCode,
    sConjugator b * localRepresentative (elementaryClass 1 a) * (sConjugator b)⁻¹ =
      elementaryWord 1 a := by decide +kernel

private theorem selected_sizes : ∀ b : Fin 3 → Bool,
    ¬ (b 1 = true ∧ b 2 = true) →
    Fintype.card {a : BaseCode // selected b a} = 1 ∨
    Fintype.card {a : BaseCode // selected b a} = 5 ∨
    Fintype.card {a : BaseCode // selected b a} = 9 := by decide +kernel

private theorem class_code_sizes (p : H → Prop)
    (hconj : ∀ (g : H), g ∈ modelD → ∀ x, p (g * x * g⁻¹) ↔ p x)
    (hone : ¬ p 1) (hpi : p Coordinates.pi) (hmu : ¬ p Coordinates.mu)
    (hlam : ¬ (p lam ∧ p (Coordinates.pi * lam))) :
    Nat.card {a : BaseCode // p (elementaryWord 1 a)} = 1 ∨
    Nat.card {a : BaseCode // p (elementaryWord 1 a)} = 5 ∨
    Nat.card {a : BaseCode // p (elementaryWord 1 a)} = 9 := by
  classical
  let b : Fin 3 → Bool := ![decide (p tau), decide (p lam), decide (p (Coordinates.pi * lam))]
  have hs (a : BaseCode) : p (elementaryWord 1 a) ↔ selected b a := by
    obtain ⟨c, hc⟩ := sConjugator_table a
    have he : p (elementaryWord 1 a) ↔ p (localRepresentative (elementaryClass 1 a)) := by
      rw [← hc]
      exact hconj _ (sConjugator_mem c) _
    rw [he]
    have hb : (elementaryClass 1 a).val < 6 := by
      have h : ∀ a : BaseCode, (elementaryClass 1 a).val < 6 := by decide +kernel
      exact h a
    unfold selected
    generalize elementaryClass 1 a = i at *
    fin_cases i <;> simp [localRepresentative, b, hone, hpi, hmu]
    all_goals norm_num at hb
  have he := Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl BaseCode) hs)
  rw [he, Nat.card_eq_fintype_card]
  exact selected_sizes b (by simpa [b] using hlam)

private def piOrbit (y : G) : Prop :=
  ∃ n : sNormalizer D e, (n : G) * D.z * (n : G)⁻¹ = y

private theorem piOrbit_iff (y : ambientElementary D e 1) :
    piOrbit D e (y : G) ↔ y ∈ MulAction.orbit (sNormalizer D e) (piPoint D e) := by
  constructor
  · rintro ⟨n, hn⟩
    exact MulAction.mem_orbit_iff.mpr ⟨n, Subtype.ext hn⟩
  · intro hy
    obtain ⟨n, hn⟩ := MulAction.mem_orbit_iff.mp hy
    exact ⟨n, congrArg Subtype.val hn⟩

omit [Finite G] in
private theorem piOrbit_isConj {y : G} (hy : piOrbit D e y) : IsConj D.z y := by
  obtain ⟨n, hn⟩ := hy
  exact isConj_iff.mpr ⟨(n : G), hn⟩

omit [Finite G] in
private theorem piOrbit_conj (g : sNormalizer D e) (y : G) :
    piOrbit D e ((g : G) * y * (g : G)⁻¹) ↔ piOrbit D e y := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨g⁻¹ * n, ?_⟩
    change ((g : G)⁻¹ * (n : G)) * D.z * ((g : G)⁻¹ * (n : G))⁻¹ = y
    calc
      _ = (g : G)⁻¹ * ((n : G) * D.z * (n : G)⁻¹) * (g : G) := by group
      _ = y := by rw [hn]; group
  · rintro ⟨n, hn⟩
    refine ⟨g * n, ?_⟩
    change ((g : G) * (n : G)) * D.z * ((g : G) * (n : G))⁻¹ = _
    calc
      _ = (g : G) * ((n : G) * D.z * (n : G)⁻¹) * (g : G)⁻¹ := by group
      _ = _ := by rw [hn]

/-- Under pi--mu nonfusion and lambda separation, pi's S-normalizer orbit has
one or nine elements. The excluded size five would give an automorphism
subgroup of order forty on S, contradicting the five-normalizer bound. -/
public theorem sNormalizer_pi_orbit_eq_one_or_nine
    (hf : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hl : ¬ (IsConj D.z (D.a10ModelEmbedding e lam) ∧
      IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * lam)))) :
    (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard = 1 ∨
    (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard = 9 := by
  let p (y : H) := piOrbit D e (D.a10ModelEmbedding e y)
  have hc (g : H) (hg : g ∈ modelD) (y : H) : p (g * y * g⁻¹) ↔ p y := by
    let n : sNormalizer D e := ⟨D.a10ModelEmbedding e g,
      ambientSylow_le_normalizer_S D e (mem_map_of_mem _ hg)⟩
    simpa only [p, map_mul, map_inv] using piOrbit_conj D e n (D.a10ModelEmbedding e y)
  have hone : ¬ p 1 := by
    intro h
    have hh := piOrbit_isConj D e h
    rw [map_one] at hh
    exact D.z_ne_one (isConj_one_left.mp hh)
  have hpi : p Coordinates.pi := by
    refine ⟨1, ?_⟩
    simp [D.a10ModelEmbedding_central e]
  have hmu : ¬ p Coordinates.mu := fun h => hf (piOrbit_isConj D e h)
  have hlam : ¬ (p lam ∧ p (Coordinates.pi * lam)) :=
    fun h => hl ⟨piOrbit_isConj D e h.1, piOrbit_isConj D e h.2⟩
  have hs := class_code_sizes p hc hone hpi hmu hlam
  have he := Equiv.subtypeEquiv (Equiv.ofBijective (sWord D e) (sWord_bijective D e))
    (fun a => piOrbit_iff D e (sWord D e a))
  have hcard : Nat.card {a : BaseCode // p (elementaryWord 1 a)} =
      (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard :=
    (Nat.card_congr he).trans (Nat.card_coe_set_eq _)
  rw [hcard] at hs
  rcases hs with h | h | h
  · exact Or.inl h
  · exfalso
    apply aut_subgroup_card_ne_forty (ambientElementary_card D e 1)
      (ambientElementary D e 1).normalizerMonoidHom.range
    rw [← Nat.card_congr (quotientEquivAction D e).toEquiv, quotient_card, h]
  · exact Or.inr h

/-- A non-two S-normalizer supplies the required fusions, under exactly the
pi--mu and lambda separations. Constructing such a normalizer remains a
separate source argument. -/
public theorem exists_s_fusion_of_normalizer_not_two
    (hf : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hl : ¬ (IsConj D.z (D.a10ModelEmbedding e lam) ∧
      IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * lam))))
    (hn : ¬ IsPGroup 2 (sNormalizer D e)) :
    ∃ b : Bit, IsConj D.z (D.a10ModelEmbedding e tau) ∧
      IsConj (D.a10ModelEmbedding e Coordinates.mu)
        (D.a10ModelEmbedding e (normalizedLam b)) ∧
      IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * normalizedLam b)) := by
  apply exists_s_fusion_of_orbit_nine D e hf hl
  rcases sNormalizer_pi_orbit_eq_one_or_nine D e hf hl with h | h
  · exfalso
    apply hn
    apply IsPGroup.of_card (n := 7)
    rw [normalizer_card, h]
    decide
  · exact h

/-- The tau branch is complete: its centralizer overgroup makes N_G(S)
non-two, and orbit counting supplies all three normalized S-fusions. -/
public theorem exists_s_fusion_of_tau
    (hf : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hl : ¬ (IsConj D.z (D.a10ModelEmbedding e lam) ∧
      IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * lam))))
    (ht : IsConj D.z (D.a10ModelEmbedding e tau)) :
    ∃ b : Bit, IsConj D.z (D.a10ModelEmbedding e tau) ∧
      IsConj (D.a10ModelEmbedding e Coordinates.mu)
        (D.a10ModelEmbedding e (normalizedLam b)) ∧
      IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * normalizedLam b)) := by
  obtain ⟨P, hP, _, hPC, hPN⟩ := exists_tau_overgroup_in_normalizer D e ht
  exact exists_s_fusion_of_normalizer_not_two D e hf hl
    (sCase_overgroup_normalizer_not_isPGroup D e 0 P hP hPC hPN)

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
