module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AmbientGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Bounds

/-!
# Local fusion tables for the additional-fusion argument

The sixty-four elementary normal forms are assigned to the identity or one
of Held's eight local involution classes by explicit conjugating permutations.
If pi is fused to mu while lambda and the five additional representatives
are separated from pi, the four elementary subgroups contain respectively
seven, three, three and three pi-fused elements. Conjugacy preserves these
counts, so M is weakly closed in the displayed ambient Sylow subgroup.

The four local conjugates of xi generate M. The pointwise centralizers of
these four elements, and of the even pair flips pi, mu, mu', are exactly M
in both the concrete local calculation and the required ambient setting.
These are kernel calculations for the later normalizer actions; they do not
assume a normalizer order or construct its odd-order actors.

All finite calculations use the actual permutation coordinates and kernel
reduction. Source: D. Held, "A Characterization of some multiply transitive
permutation groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Section 1, p.225 and Lemma 2.6, p.228.
The source convention x^g is g^-1*x*g; the displayed witness equations below
use Lean's conjugation g*x*g^-1.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates

/-- Identity followed by the eight local involution representatives in source order. -/
@[expose] public def localRepresentative : Fin 9 → H :=
  ![1, pi, mu, tau, lam, pi * lam, xi, pi * xi, tau * lam * xi]

/-- The five alternatives in the first part of Held Lemma 2.6. -/
@[expose] public def additionalRepresentative : Fin 5 → H :=
  ![tau, pi * lam, xi, pi * xi, tau * lam * xi]

@[expose] public def elementaryBinaryIndex (a : BaseCode) : Fin 16 :=
  ⟨8 * a.1.val + 4 * a.2.1.val + 2 * a.2.2.1.val + a.2.2.2.val, by omega⟩

@[expose] public def elementaryClassRow : Fin 4 → Fin 16 → Fin 9 :=
  ![![0, 6, 2, 6, 2, 6, 2, 7, 1, 7, 2, 7, 2, 7, 2, 6],
    ![0, 4, 3, 4, 2, 4, 3, 5, 1, 5, 3, 5, 2, 5, 3, 4],
    ![0, 6, 4, 8, 2, 7, 4, 8, 1, 7, 5, 8, 2, 6, 5, 8],
    ![0, 6, 4, 8, 2, 6, 5, 8, 1, 7, 5, 8, 2, 7, 4, 8]]

private def elementaryActorRow : Fin 4 → Fin 16 → Code :=
  ![![((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 0, 1, 0)), ((0, 0, 0, 0), (0, 0, 1, 0)), ((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 0, 0, 1)), ((0, 0, 0, 0), (0, 0, 2, 0)), ((0, 0, 0, 0), (0, 1, 0, 1)), ((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (1, 0, 1, 0)), ((0, 0, 0, 0), (0, 0, 1, 0)), ((0, 0, 0, 0), (0, 1, 0, 0)), ((0, 0, 0, 0), (0, 0, 0, 1)), ((0, 0, 0, 0), (0, 1, 2, 0)), ((0, 0, 0, 0), (0, 1, 0, 1))],
    ![((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 1, 0, 0)), ((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 1), (0, 0, 0, 0)), ((0, 0, 0, 1), (0, 0, 0, 0)), ((0, 0, 1, 0), (0, 1, 0, 0)), ((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 1, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 1, 0, 0)), ((0, 0, 0, 0), (0, 1, 0, 0)), ((0, 0, 0, 1), (0, 0, 0, 0)), ((0, 0, 1, 1), (0, 0, 0, 0)), ((0, 0, 1, 0), (0, 1, 0, 0))],
    ![((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 0, 1, 0)), ((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 1, 0, 0)), ((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 1, 0, 1)), ((0, 0, 0, 1), (0, 0, 0, 0)), ((0, 0, 0, 1), (0, 1, 0, 0)), ((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 0, 1, 0)), ((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 1), (0, 1, 0, 1)), ((0, 0, 0, 0), (0, 1, 0, 0)), ((0, 0, 0, 0), (0, 1, 0, 1)), ((0, 0, 0, 1), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 1, 0, 1))],
    ![((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 1, 0, 0)), ((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 0, 0, 1)), ((0, 0, 1, 0), (0, 1, 0, 0)), ((0, 0, 0, 0), (0, 0, 0, 1)), ((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 0, 0, 0)), ((0, 0, 0, 0), (0, 1, 0, 0)), ((0, 0, 1, 0), (0, 0, 0, 1)), ((0, 0, 0, 0), (0, 1, 0, 0)), ((0, 0, 0, 0), (0, 0, 0, 1)), ((0, 0, 1, 0), (0, 1, 0, 0)), ((0, 0, 1, 0), (0, 0, 0, 0))]]


/-- The exact H-class of each of the sixty-four elementary normal forms. -/
@[expose] public def elementaryClass (k : Fin 4) (a : BaseCode) : Fin 9 :=
  elementaryClassRow k (elementaryBinaryIndex a)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem elementary_conjugator : ∀ (k : Fin 4) (a : BaseCode),
    word (elementaryActorRow k (elementaryBinaryIndex a)) * localRepresentative (elementaryClass k a) *
      (word (elementaryActorRow k (elementaryBinaryIndex a)))⁻¹ = elementaryWord k a := by
  decide +kernel

public theorem elementaryWord_isConj (k : Fin 4) (a : BaseCode) :
    IsConj (localRepresentative (elementaryClass k a)) (elementaryWord k a) :=
  isConj_iff.mpr ⟨_, elementary_conjugator k a⟩

public theorem elementaryWord_bijective (k : Fin 4) :
    Function.Bijective (fun a : BaseCode =>
      (⟨elementaryWord k a, (mem_elementary k _).mpr ⟨a, rfl⟩⟩ : elementary k)) := by
  have hs : Function.Surjective (fun a : BaseCode =>
      (⟨elementaryWord k a, (mem_elementary k _).mpr ⟨a, rfl⟩⟩ : elementary k)) := by
    rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := (mem_elementary k x).mp hx
    exact ⟨a, rfl⟩
  apply hs.bijective_of_nat_card_le
  rw [elementary_card]
  simp [BaseCode]

/-- The four single-pair flips, the complete local class of xi. -/
@[expose] public def xiConjugate : Fin 4 → H :=
  ![xi, mu * xi, mup * xi, pi * mu * mup * xi]

public theorem xiConjugate_injective : Function.Injective xiConjugate := by decide +kernel

public theorem xiConjugate_isConj (i : Fin 4) : IsConj xi (xiConjugate i) := by
  have hc : ∀ i : Fin 4,
      (![1, tau, taup, tau * taup] : Fin 4 → H) i * xi *
        ((![1, tau, taup, tau * taup] : Fin 4 → H) i)⁻¹ = xiConjugate i := by
    decide +kernel
  exact isConj_iff.mpr ⟨_, hc i⟩

public theorem xiConjugate_mem (i : Fin 4) : xiConjugate i ∈ modelM := by
  have hc : ∀ i : Fin 4, ∃ a : BaseCode, elementaryWord 0 a = xiConjugate i := by
    decide +kernel
  exact (mem_elementary 0 _).mpr (hc i)

private def xiWord (a : BaseCode) : H :=
  xiConjugate 0 ^ a.1.val * xiConjugate 1 ^ a.2.1.val *
    xiConjugate 2 ^ a.2.2.1.val * xiConjugate 3 ^ a.2.2.2.val

private theorem xiWord_spans : ∀ a : BaseCode,
    ∃ b : BaseCode, xiWord b = elementaryWord 0 a := by decide +kernel

/-- These four conjugates generate all of M, including pi. -/
public theorem xiConjugates_generate : closure (Set.range xiConjugate) = modelM := by
  apply le_antisymm
  · rw [closure_le]
    rintro x ⟨i, rfl⟩
    exact xiConjugate_mem i
  · intro x hx
    obtain ⟨a, rfl⟩ := (mem_elementary 0 x).mp hx
    obtain ⟨b, hb⟩ := xiWord_spans a
    rw [← hb, xiWord]
    let K := closure (Set.range xiConjugate)
    have hm (j : Fin 4) : xiConjugate j ∈ K := subset_closure ⟨j, rfl⟩
    exact K.mul_mem (K.mul_mem (K.mul_mem (K.pow_mem (hm 0) _)
      (K.pow_mem (hm 1) _)) (K.pow_mem (hm 2) _)) (K.pow_mem (hm 3) _)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem xi_conjugation_table : ∀ a : Code,
    ∃ i : Fin 4, word a * xi * (word a)⁻¹ = xiConjugate i := by decide +kernel

/-- Exhaustion of the xi class in H, with no assertion about fusion in G. -/
public theorem xi_isConj_iff (x : H) : IsConj xi x ↔ ∃ i, xiConjugate i = x := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    obtain ⟨a, ha⟩ := word_bijective.surjective g
    obtain ⟨i, hi⟩ := xi_conjugation_table a
    refine ⟨i, hi.symm.trans ?_⟩
    rw [ha]
    exact hg
  · rintro ⟨i, rfl⟩
    exact xiConjugate_isConj i

/-- The two four-element local classes in M are disjoint. -/
public theorem xiConjugate_ne_pi_mul : ∀ i j, xiConjugate i ≠ pi * xiConjugate j := by
  decide +kernel

/-- Generators of the even pair-flip subgroup of order eight. -/
@[expose] public def evenFlipGenerator : Fin 3 → H := ![pi, mu, mup]

public theorem elementaryClass_M_fused_iff (a : BaseCode) :
    (elementaryClass 0 a = 1 ∨ elementaryClass 0 a = 2) ↔
      a.2.2.2 = 0 ∧ a ≠ 0 := by
  have h : ∀ a : BaseCode, (elementaryClass 0 a = 1 ∨ elementaryClass 0 a = 2) ↔
      a.2.2.2 = 0 ∧ a ≠ 0 := by decide +kernel
  exact h a

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem evenFlip_centralizer_table : ∀ a : Code,
    (∀ i, evenFlipGenerator i * word a = word a * evenFlipGenerator i) ↔ a.2 = 0 := by
  decide +kernel

/-- The action on the even pair flips has kernel M already in the local group. -/
public theorem evenFlip_centralizer : centralizer (Set.range evenFlipGenerator) = modelM := by
  ext x
  obtain ⟨a, rfl⟩ := word_bijective.surjective x
  constructor
  · intro hx
    have ht : ∀ i, evenFlipGenerator i * word a = word a * evenFlipGenerator i :=
      fun i => mem_centralizer_iff.mp hx _ ⟨i, rfl⟩
    have ha := (evenFlip_centralizer_table a).mp ht
    apply (mem_elementary 0 _).mpr
    refine ⟨a.1, ?_⟩
    simp only [word, ha, actorWord]
    rfl
  · intro hx
    have he : Set.range evenFlipGenerator ⊆ (modelM : Set H) := by
      rintro y ⟨i, rfl⟩
      fin_cases i
      · exact elementaryGenerators_mem 0 0
      · exact elementaryGenerators_mem 0 1
      · exact elementaryGenerators_mem 0 2
    exact centralizer_le he (by
      change word a ∈ centralizer (elementary 0 : Set H)
      rwa [elementary_selfCentralizing 0])

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- Absence of the five additional fusions; lambda separation remains a separate premise. -/
@[expose] public def NoAdditionalFusion : Prop :=
  ∀ i, ¬ IsConj D.z (D.a10ModelEmbedding e (additionalRepresentative i))

public theorem localRepresentative_fusion
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (hno : NoAdditionalFusion D e) (i : Fin 9) :
    IsConj D.z (D.a10ModelEmbedding e (localRepresentative i)) ↔ i = 1 ∨ i = 2 := by
  have hp : D.a10ModelEmbedding e pi = D.z := D.a10ModelEmbedding_central e
  fin_cases i
  · change IsConj D.z (D.a10ModelEmbedding e 1) ↔ ((0 : Fin 9) = 1 ∨ 0 = 2)
    simp [D.z_ne_one]
  · change IsConj D.z (D.a10ModelEmbedding e pi) ↔ ((1 : Fin 9) = 1 ∨ 1 = 2)
    rw [hp]
    exact ⟨fun _ => Or.inl rfl, fun _ => IsConj.refl _⟩
  · simpa [localRepresentative, mu, LocalData.a10NoncentralInvolution] using hmu
  · simpa [localRepresentative, additionalRepresentative] using hno 0
  · simpa [localRepresentative] using hlam
  · simpa [localRepresentative, additionalRepresentative] using hno 1
  · simpa [localRepresentative, additionalRepresentative] using hno 2
  · simpa [localRepresentative, additionalRepresentative] using hno 3
  · simpa [localRepresentative, additionalRepresentative] using hno 4

public theorem elementaryWord_fusion
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (hno : NoAdditionalFusion D e) (k : Fin 4) (a : BaseCode) :
    IsConj D.z (D.a10ModelEmbedding e (elementaryWord k a)) ↔
      elementaryClass k a = 1 ∨ elementaryClass k a = 2 := by
  rw [← localRepresentative_fusion D e hmu hlam hno]
  have hc := (D.a10ModelEmbedding e).map_isConj (elementaryWord_isConj k a)
  exact ⟨fun h => h.trans hc.symm, fun h => h.trans hc⟩

/-- The subset of a subgroup belonging to an ambient conjugacy class. -/
@[expose] public def fusedElements (A : Subgroup G) (x : G) : Set A := {a | IsConj x (a : G)}

public theorem ambientElementary_fused_card
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (hno : NoAdditionalFusion D e) (k : Fin 4) :
    (fusedElements (ambientElementary D e k) D.z).ncard =
      (![7, 3, 3, 3] : Fin 4 → ℕ) k := by
  let b := Equiv.ofBijective _ (elementaryWord_bijective k)
  let c := (elementary k).equivMapOfInjective (D.a10ModelEmbedding e)
    (D.a10ModelEmbedding_injective e)
  have he : Nat.card {a : BaseCode // elementaryClass k a = 1 ∨ elementaryClass k a = 2} =
      (fusedElements (ambientElementary D e k) D.z).ncard := by
    apply Nat.card_congr (Equiv.subtypeEquiv (b.trans c.toEquiv) ?_)
    intro a
    exact (elementaryWord_fusion D e hmu hlam hno k a).symm
  rw [← he, Nat.card_eq_fintype_card]
  have hc : ∀ k, Fintype.card {a : BaseCode //
      elementaryClass k a = 1 ∨ elementaryClass k a = 2} =
        (![7, 3, 3, 3] : Fin 4 → ℕ) k := by decide +kernel
  exact hc k

omit [Finite G] in
/-- Conjugating a subgroup preserves the number of its elements in a fixed ambient class. -/
public theorem fusedElements_map_conj_card (A : Subgroup G) (x g : G) :
    (fusedElements (A.map (MulAut.conj g).toMonoidHom) x).ncard =
      (fusedElements A x).ncard := by
  symm
  apply Nat.card_congr (Equiv.subtypeEquiv
    (A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv ?_)
  intro a
  change IsConj x (a : G) ↔ IsConj x (g * (a : G) * g⁻¹)
  have hc : IsConj (a : G) (g * (a : G) * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  exact ⟨fun h => h.trans hc, fun h => h.trans hc.symm⟩

/-- Under the contrary fusion assumptions, M cannot be conjugated to any other catalogue entry. -/
public theorem ambientM_not_conjugate_other
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (hno : NoAdditionalFusion D e) (k : Fin 4) (hk : k ≠ 0) (g : G) :
    (ambientElementary D e 0).map (MulAut.conj g).toMonoidHom ≠
      ambientElementary D e k := by
  intro he
  have hc := fusedElements_map_conj_card (ambientElementary D e 0) D.z g
  rw [he, ambientElementary_fused_card D e hmu hlam hno,
    ambientElementary_fused_card D e hmu hlam hno] at hc
  fin_cases k <;> simp_all

/-- M is the unique elementary sixteen in the displayed Sylow with seven pi-fused elements. -/
public theorem ambientM_unique_fused_seven
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (hno : NoAdditionalFusion D e) (A : Subgroup G)
    (hAT : A ≤ ambientSylow D e) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card A = 16) (hfused : (fusedElements A D.z).ncard = 7) :
    A = ambientElementary D e 0 := by
  obtain ⟨k, rfl⟩ := ambient_elementary_sixteen D e A hAT hA hcard
  rw [ambientElementary_fused_card D e hmu hlam hno] at hfused
  fin_cases k <;> simp_all

/-- Under the contrary assumptions, M is weakly closed in the displayed Sylow subgroup. -/
public theorem ambientM_weakly_closed
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (hno : NoAdditionalFusion D e) (g : G)
    (hg : (ambientElementary D e 0).map (MulAut.conj g).toMonoidHom ≤ ambientSylow D e) :
    (ambientElementary D e 0).map (MulAut.conj g).toMonoidHom = ambientElementary D e 0 := by
  apply ambientM_unique_fused_seven D e hmu hlam hno _ hg
  · let := ambientElementary_isElementaryAbelian D e 0
    exact IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  · rw [card_map_of_injective (MulAut.conj g).injective, ambientElementary_card]
  · rw [fusedElements_map_conj_card, ambientElementary_fused_card D e hmu hlam hno]
    rfl

omit [Finite G] in
public theorem ambient_xiConjugates_generate :
    closure (Set.range (fun i => D.a10ModelEmbedding e (xiConjugate i))) =
      ambientElementary D e 0 := by
  rw [Set.range_comp', ← MonoidHom.map_closure, xiConjugates_generate]
  rfl

/-- Pointwise fixation of the four xi-conjugates has kernel precisely M. -/
public theorem ambient_centralizer_xiConjugates :
    centralizer (Set.range (fun i => D.a10ModelEmbedding e (xiConjugate i))) =
      ambientElementary D e 0 := by
  rw [← centralizer_closure, ambient_xiConjugates_generate,
    ambientElementary_selfCentralizing]

/-- Faithfulness on the even pair flips: the full ambient pointwise centralizer is M. -/
public theorem ambient_evenFlip_centralizer :
    centralizer (Set.range (fun i => D.a10ModelEmbedding e (evenFlipGenerator i))) =
      ambientElementary D e 0 := by
  let f := D.a10ModelEmbedding e
  ext x
  constructor
  · intro hx
    have hxH : x ∈ D.centralizer := by
      apply mem_centralizer_singleton_iff.mpr
      rw [← D.a10ModelEmbedding_central e]
      exact (mem_centralizer_iff.mp hx (f pi) ⟨0, rfl⟩).symm
    obtain ⟨y, rfl⟩ := (show x ∈ f.range by rwa [D.a10ModelEmbedding_range e])
    apply mem_map_of_mem
    change y ∈ modelM
    rw [← evenFlip_centralizer]
    apply mem_centralizer_iff.mpr
    rintro _ ⟨i, rfl⟩
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul] using mem_centralizer_iff.mp hx
      (f (evenFlipGenerator i)) ⟨i, rfl⟩
  · intro hx
    have he : Set.range (fun i => f (evenFlipGenerator i)) ⊆
        (ambientElementary D e 0 : Set G) := by
      rintro y ⟨i, rfl⟩
      apply mem_map_of_mem
      fin_cases i
      · exact elementaryGenerators_mem 0 0
      · exact elementaryGenerators_mem 0 1
      · exact elementaryGenerators_mem 0 2
    exact centralizer_le he (by rwa [ambientElementary_selfCentralizing D e 0])

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
