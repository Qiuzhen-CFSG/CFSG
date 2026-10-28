module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section41Nu.InitialActor.Geometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section41Nu.InitialActor.Normalization

/-!
# The marked order-three action on Held's S

Assume the earlier S-fusions pi~tau, mu~lambda, and pi~pi*lambda, with
pi and mu not conjugate. In the binary basis (pi,mu,tau,lambda), these
hypotheses identify the nine-element pi class. Any order-three element
of N_G(S) fixing mu preserves that class and cannot fix pi, whose stabilizer
has order 128. A finite calculation leaves exactly two actions, inverse to
each other. Replacing the element by its inverse selects the required
pi and tau images and proves that it centralizes lambda.

The calculation uses 4096 binary column triples. Testing their class labels
before the full action and cube conditions reduces the kernel check to about
four seconds. All word identities are checked in the concrete local model;
the ambient group itself is neither enumerated nor identified.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, first paragraph of Lemma 4.1, printed p.232.
This result leaves the earlier fusion hypotheses and three-element explicit.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
open Coordinates Fusion Fusion.LambdaSeparation

private def markedWord (b : Bit) (j : BaseCode) : H :=
  Coordinates.pi ^ j.1.val * Coordinates.mu ^ j.2.1.val *
    tau ^ j.2.2.1.val * normalizedLam b ^ j.2.2.2.val
private def reCode (b : Bit) (j : BaseCode) : BaseCode :=
  (j.1 + b * j.2.2.2, j.2.1, j.2.2.1, j.2.2.2)
private theorem word_reCode : ∀ b j,
    markedWord b j = elementaryWord 1 (reCode b j) := by decide +kernel
private theorem reCode_twice : ∀ b j, reCode b (reCode b j) = j := by decide +kernel
private theorem word_injective : ∀ b, Function.Injective (markedWord b) := by decide +kernel
private theorem word_add : ∀ b i j, markedWord b (i + j) = markedWord b i * markedWord b j := by
  decide +kernel
private theorem word_zero : ∀ b, markedWord b 0 = 1 := by decide +kernel
private theorem word_mu : ∀ b (i : Bit), markedWord b (0,i,0,0) = Coordinates.mu ^ i.val := by
  decide +kernel
private theorem word_basis : ∀ b,
    markedWord b (1,0,0,0) = Coordinates.pi ∧
    markedWord b (0,1,0,0) = Coordinates.mu ∧
    markedWord b (0,0,1,0) = tau ∧
    markedWord b (0,0,0,1) = normalizedLam b := by decide +kernel

private theorem zero_code : (0,0,0,0) = (0 : BaseCode) := rfl

private def linearImage (p t l j : BaseCode) : BaseCode :=
  (if j.1 = 0 then 0 else p) + (0, j.2.1, 0, 0) +
    (if j.2.2.1 = 0 then 0 else t) + (if j.2.2.2 = 0 then 0 else l)
private def piClass (j : BaseCode) : Bool :=
  decide (j = (1,0,0,0) ∨ (j.2.2.2 = 0 ∧ j.2.2.1 = 1) ∨
    (j.2.2.2 = 1 ∧ j.1 ≠ j.2.1 * j.2.2.1))
set_option synthInstance.maxSize 512 in
set_option maxRecDepth 4096 in
private theorem action_table : ∀ p t l : BaseCode,
    p ≠ (1,0,0,0) →
    piClass p = true → piClass t = true → piClass l = false →
    (∀ j, piClass (linearImage p t l j) = piClass j) →
    (∀ j, linearImage p t l (linearImage p t l (linearImage p t l j)) = j) →
    (p = (1,0,1,1) ∧ t = (1,1,0,1) ∧ l = (0,0,0,1)) ∨
    (p = (0,1,1,1) ∧ t = (1,1,1,0) ∧ l = (0,0,0,1)) := by
  decide +kernel

private def classRep (b : Bit) (j : BaseCode) : H :=
  if j = 0 then 1 else
  if j.2.2.2 = 0 then
    if j.2.2.1 = 1 then tau else if j.2.1 = 1 then Coordinates.mu else Coordinates.pi
  else if j.1 = j.2.1 * j.2.2.1 then normalizedLam b else Coordinates.pi * normalizedLam b
private def conjugator (c : Bit × Bit × Bit) : H :=
  mup ^ c.1.val * taup ^ c.2.1.val * xi ^ c.2.2.val
private theorem class_conjugator : ∀ b j, ∃ c : Bit × Bit × Bit,
    conjugator c * classRep b j * (conjugator c)⁻¹ = markedWord b j := by decide +kernel

private theorem word_linearImage (b : Bit) (p t l j : BaseCode) :
    markedWord b (linearImage p t l j) = markedWord b p ^ j.1.val *
      Coordinates.mu ^ j.2.1.val * markedWord b t ^ j.2.2.1.val * markedWord b l ^ j.2.2.2.val := by
  rcases j with ⟨a,c,d,h⟩
  fin_cases a <;> fin_cases c <;> fin_cases d <;> fin_cases h <;>
    simp [linearImage, word_add, word_mu, pow_zero, pow_one]

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

private theorem word_isConj_pi_iff (b : Bit)
    (hf : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (ht : IsConj D.z (D.a10ModelEmbedding e tau))
    (hl : IsConj (D.a10ModelEmbedding e Coordinates.mu) (D.a10ModelEmbedding e (normalizedLam b)))
    (hpl : IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * normalizedLam b)))
    (j : BaseCode) : IsConj D.z (D.a10ModelEmbedding e (markedWord b j)) ↔ piClass j = true := by
  let f := D.a10ModelEmbedding e
  obtain ⟨c, hc⟩ := class_conjugator b j
  have hh : IsConj (f (classRep b j)) (f (markedWord b j)) :=
    f.map_isConj (isConj_iff.mpr ⟨conjugator c, hc⟩)
  have hiff : IsConj D.z (f (classRep b j)) ↔ IsConj D.z (f (markedWord b j)) :=
    ⟨fun h => h.trans hh, fun h => h.trans hh.symm⟩
  change IsConj D.z (f (markedWord b j)) ↔ _
  rw [← hiff]
  have hzero : ¬ IsConj D.z (f 1) := by
    rw [map_one]
    exact fun h => D.z_ne_one (isConj_one_left.mp h)
  have hpi : IsConj D.z (f Coordinates.pi) := by rw [D.a10ModelEmbedding_central]
  have hmu : ¬ IsConj D.z (f Coordinates.mu) := hf
  have hlam : ¬ IsConj D.z (f (normalizedLam b)) := fun h => hf (h.trans hl.symm)
  change IsConj D.z (f tau) at ht
  change IsConj D.z (f (Coordinates.pi * normalizedLam b)) at hpl
  rcases j with ⟨a,c,d,h⟩
  fin_cases a <;> fin_cases c <;> fin_cases d <;> fin_cases h
  all_goals first
    | exact iff_of_false hzero (by decide)
    | exact iff_of_true hpi (by decide)
    | exact iff_of_false hmu (by decide)
    | exact iff_of_false hlam (by decide)
    | exact iff_of_true ht (by decide)
    | exact iff_of_true hpl (by decide)

omit [Finite G] in
private theorem cube_conj (v : G) (hv : v ^ 3 = 1) (x : G) :
    (MulAut.conj v⁻¹) ((MulAut.conj v⁻¹) ((MulAut.conj v⁻¹) x)) = x := by
  have he : v * v * v = 1 := by simpa only [pow_succ, pow_zero, one_mul] using hv
  simp only [MulAut.conj_apply, inv_inv]
  calc
    _ = (v * v * v)⁻¹ * x * (v * v * v) := by group
    _ = x := by rw [he]; group

omit [Finite G] in
private theorem conj_twice (v : G) (hv : v ^ 3 = 1) (x : G) :
    (MulAut.conj v⁻¹) ((MulAut.conj v⁻¹) x) = v * x * v⁻¹ := by
  have h : v⁻¹ * (MulAut.conj v⁻¹) ((MulAut.conj v⁻¹) x) * v = x := by
    simpa only [MulAut.conj_apply, inv_inv] using cube_conj v hv x
  calc
    _ = v * (v⁻¹ * (MulAut.conj v⁻¹) ((MulAut.conj v⁻¹) x) * v) * v⁻¹ := by group
    _ = _ := by rw [h]

omit [Finite G] in
private theorem commute_of_conj {v x : G} (h : v⁻¹ * x * v = x) : Commute v x := by
  change v * x = x * v
  calc
    _ = v * (v⁻¹ * x * v) := by rw [h]
    _ = x * v := by group

omit [Finite G] in
private theorem marked_action_images (b : Bit) (v : G)
    (hvN : v ∈ sNormalizer D e) (hvm : Commute v (D.a10ModelEmbedding e Coordinates.mu)) :
    ∃ p t l : BaseCode, ∀ j,
      (MulAut.conj v⁻¹) (D.a10ModelEmbedding e (markedWord b j)) =
        D.a10ModelEmbedding e (markedWord b (linearImage p t l j)) := by
  let f := D.a10ModelEmbedding e
  let A := MulAut.conj v⁻¹
  have images (x : H) (hx : x ∈ modelS) : ∃ j, A (f x) = f (markedWord b j) := by
    let n : sNormalizer D e := ⟨v⁻¹, inv_mem hvN⟩
    let s : ambientElementary D e 1 := ⟨f x, mem_map_of_mem f hx⟩
    have hmem : A (f x) ∈ ambientElementary D e 1 := (n • s).property
    obtain ⟨y, hy, he⟩ := hmem
    obtain ⟨j, rfl⟩ := (mem_elementary 1 y).mp hy
    refine ⟨reCode b j, ?_⟩
    rw [word_reCode, reCode_twice]
    exact he.symm
  have word_mem (j : BaseCode) : markedWord b j ∈ modelS := by
    rw [word_reCode]
    exact (mem_elementary 1 _).mpr ⟨_, rfl⟩
  obtain ⟨p, hp⟩ := images Coordinates.pi (by simpa only [(word_basis b).1] using word_mem (1,0,0,0))
  obtain ⟨t, ht⟩ := images tau (by simpa only [(word_basis b).2.2.1] using word_mem (0,0,1,0))
  obtain ⟨l, hl⟩ := images (normalizedLam b)
    (by simpa only [(word_basis b).2.2.2] using word_mem (0,0,0,1))
  have hm : A (f Coordinates.mu) = f Coordinates.mu := by
    simp only [A, MulAut.conj_apply, inv_inv]
    change Commute v (f Coordinates.mu) at hvm
    rw [mul_assoc, ← hvm.eq, inv_mul_cancel_left]
  refine ⟨p,t,l, fun j => ?_⟩
  change A (f (markedWord b j)) = f (markedWord b (linearImage p t l j))
  rw [word_linearImage]
  simp only [markedWord, map_mul, map_pow, hp, ht, hl, hm]

/-- An order-three element in the actual S-normalizer centralizing mu has
one of the two marked actions, once the earlier three S-fusions are supplied.
Replacing it by its inverse chooses the source orientation. -/
public theorem nonempty_nuAction_of_initial_three (b : Bit)
    (hf : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (ht : IsConj D.z (D.a10ModelEmbedding e tau))
    (hl : IsConj (D.a10ModelEmbedding e Coordinates.mu) (D.a10ModelEmbedding e (normalizedLam b)))
    (hpl : IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * normalizedLam b)))
    (v : G) (hvN : v ∈ sNormalizer D e) (hv3 : orderOf v = 3)
    (hvm : Commute v (D.a10ModelEmbedding e Coordinates.mu)) :
    Nonempty (NuActionRelations D e b) := by
  let f := D.a10ModelEmbedding e
  let A := MulAut.conj v⁻¹
  have hv : v ^ 3 = 1 := by simpa only [hv3] using pow_orderOf_eq_one v
  obtain ⟨p,t,l,hImage⟩ := marked_action_images D e b v hvN hvm
  change ∀ j, A (f (markedWord b j)) = f (markedWord b (linearImage p t l j)) at hImage
  have hP : A (f Coordinates.pi) = f (markedWord b p) := by
    simpa [linearImage, zero_code, (word_basis b).1] using hImage (1,0,0,0)
  have hT : A (f tau) = f (markedWord b t) := by
    simpa [linearImage, zero_code, (word_basis b).2.2.1] using hImage (0,0,1,0)
  have hL : A (f (normalizedLam b)) = f (markedWord b l) := by
    simpa [linearImage, zero_code, (word_basis b).2.2.2] using hImage (0,0,0,1)
  have hp : p ≠ (1,0,0,0) := by
    intro hp
    have hc : Commute v (f Coordinates.pi) := commute_of_conj (by
      simpa only [hp, (word_basis b).1, A, MulAut.conj_apply, inv_inv] using hP)
    have hv3' : orderOf (⟨v,hvN⟩ : sNormalizer D e) = 3 :=
      (Subgroup.orderOf_coe ⟨v,hvN⟩).symm.trans hv3
    exact normalizer_three_not_centralize_pi D e ⟨v,hvN⟩ hv3'
      (by simpa only [f, D.a10ModelEmbedding_central e] using hc.eq)
  have hclass (j : BaseCode) : piClass (linearImage p t l j) = piClass j := by
    have hc : IsConj (f (markedWord b j)) (f (markedWord b (linearImage p t l j))) :=
      isConj_iff.mpr ⟨v⁻¹, by simpa only [A, MulAut.conj_apply, inv_inv] using hImage j⟩
    have hh : (piClass (linearImage p t l j) = true) ↔ (piClass j = true) := by
      rw [← word_isConj_pi_iff D e b hf ht hl hpl, ← word_isConj_pi_iff D e b hf ht hl hpl]
      exact ⟨fun h => h.trans hc.symm, fun h => h.trans hc⟩
    exact Bool.eq_iff_iff.mpr hh
  have hcube (j : BaseCode) : linearImage p t l (linearImage p t l (linearImage p t l j)) = j := by
    apply word_injective b
    apply D.a10ModelEmbedding_injective e
    change f _ = f _
    calc
      _ = A (A (A (f (markedWord b j)))) := by rw [hImage, hImage, hImage]
      _ = f (markedWord b j) := cube_conj v hv _
  have hpc : piClass p = true := by simpa [linearImage, zero_code, piClass] using hclass (1,0,0,0)
  have htc : piClass t = true := by simpa [linearImage, zero_code, piClass] using hclass (0,0,1,0)
  have hlc : piClass l = false := by simpa [linearImage, zero_code, piClass] using hclass (0,0,0,1)
  rcases action_table p t l hp hpc htc hlc hclass hcube with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · have hpi : markedWord b (1,0,1,1) = Coordinates.pi * tau * normalizedLam b := by
      simp [markedWord]
    have htau : markedWord b (1,1,0,1) = Coordinates.pi * Coordinates.mu * normalizedLam b := by
      simp [markedWord]
    have hlamfix : Commute v (f (normalizedLam b)) := commute_of_conj (by
      simpa only [(word_basis b).2.2.2, A, MulAut.conj_apply, inv_inv] using hL)
    refine ⟨⟨v,hv,hvm,hlamfix,?_,?_⟩⟩
    · simpa only [hpi, A, MulAut.conj_apply, inv_inv] using hP
    · simpa only [htau, A, MulAut.conj_apply, inv_inv] using hT
  · have hlamfix : Commute v (f (normalizedLam b)) := commute_of_conj (by
      simpa only [(word_basis b).2.2.2, A, MulAut.conj_apply, inv_inv] using hL)
    have hpi : markedWord b (linearImage (0,1,1,1) (1,1,1,0) (0,0,0,1) (0,1,1,1)) =
        Coordinates.pi * tau * normalizedLam b := by simp [linearImage, markedWord]
    have htau : markedWord b (linearImage (0,1,1,1) (1,1,1,0) (0,0,0,1) (1,1,1,0)) =
        Coordinates.pi * Coordinates.mu * normalizedLam b := by simp [linearImage, markedWord]
    refine ⟨⟨v⁻¹, by rw [inv_pow, hv, inv_one], hvm.inv_left, hlamfix.inv_left, ?_, ?_⟩⟩
    · change (v⁻¹)⁻¹ * f Coordinates.pi * v⁻¹ = _
      rw [inv_inv, ← conj_twice v hv]
      change A (A (f Coordinates.pi)) = _
      rw [hP, hImage, hpi]
    · change (v⁻¹)⁻¹ * f tau * v⁻¹ = _
      rw [inv_inv, ← conj_twice v hv]
      change A (A (f tau)) = _
      rw [hT, hImage, htau]

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
