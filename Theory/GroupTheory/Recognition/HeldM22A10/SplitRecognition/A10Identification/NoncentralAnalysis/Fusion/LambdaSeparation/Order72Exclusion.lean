module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation.NormalizerAction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation.Order72Exclusion.WeakClosure

/-!
# Excluding the order-72 configuration in Held's lambda separation

Assume both lambda and pi*lambda are ambient conjugates of pi, and the
actual quotient N_G(S)/S has order 72. The weak-closure calculation corrects
both fusions to conjugation inside N_G(S). Conjugating by the displayed
Sylow subgroup then supplies nine distinct points of the pi orbit: pi and
all eight binary words with lambda-coordinate one. Orbit-stabilizer says
that these are the whole orbit.

Their product is pi. Since every automorphism in the normalizer action
permutes this orbit, it fixes that product. Thus the supplied element of
order three centralizes pi, contradicting the pi stabilizer order 128.
The finite certificates involve only the sixteen binary words and eight
explicit Sylow conjugators, and use kernel reduction.

This supplies a case-free alternative to both order-72 cases in Held's
printed proof. In particular it proves the needed ambient fusion control
from the elementary-subgroup catalogue, rather than assuming a quotient
structure or ambient pi--mu nonfusion. The original explicit premises,
including simplicity and the given three-element centralizer witness, are
retained in the public theorem; some are stronger than this argument needs.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.4, printed p.227.
Source conjugation is g⁻¹*x*g; the witnesses here use g*x*g⁻¹.
-/

open Subgroup Equiv
open scoped IsMulCommutative
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation
open Coordinates

private abbrev BinaryS := Multiplicative BaseCode
private abbrev binaryPi : BinaryS := Multiplicative.ofAdd (1,0,0,0)
private def lambdaNine : Finset BinaryS :=
  Finset.univ.filter (fun a => a = binaryPi ∨ a.toAdd.2.2.2 = 1)
private theorem lambdaNine_card : lambdaNine.card = 9 := by decide +kernel
private theorem lambdaNine_prod : ∏ a ∈ lambdaNine, a = binaryPi := by decide +kernel

private abbrev ConjCode := Fin 2 × Fin 2 × Fin 2
private def conjugator (b : ConjCode) : H := mup ^ b.1.val * taup ^ b.2.1.val * xi ^ b.2.2.val
private def lambdaSeed : Fin 3 → H := ![pi,lam,pi*lam]

private theorem conjugator_mem (b : ConjCode) : conjugator b ∈ modelD := by
  have h (i : Fin 7) : (![pi,mu,mup,tau,taup,lam,xi] : Fin 7 → H) i ∈ modelD :=
    subset_closure ⟨i,rfl⟩
  exact modelD.mul_mem (modelD.mul_mem (modelD.pow_mem (h 2) _) (modelD.pow_mem (h 4) _))
    (modelD.pow_mem (h 6) _)

private theorem lambdaNine_conjugate : ∀ a : BinaryS, a ∈ lambdaNine →
    ∃ b : ConjCode, ∃ i : Fin 3,
      conjugator b * lambdaSeed i * (conjugator b)⁻¹ = elementaryWord 1 a.toAdd := by
  decide +kernel

private theorem s_word_mul : ∀ a b : BaseCode,
    elementaryWord 1 (a + b) = elementaryWord 1 a * elementaryWord 1 b := by
  decide +kernel

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

private noncomputable def binarySEquiv : BinaryS ≃* ambientElementary D e 1 :=
  { (Equiv.ofBijective _ (elementaryWord_bijective 1)).trans
      ((elementary 1).equivMapOfInjective (D.a10ModelEmbedding e)
        (D.a10ModelEmbedding_injective e)).toEquiv with
    map_mul' a b := by
      apply Subtype.ext
      change D.a10ModelEmbedding e (elementaryWord 1 (a.toAdd + b.toAdd)) =
        D.a10ModelEmbedding e (elementaryWord 1 a.toAdd) *
          D.a10ModelEmbedding e (elementaryWord 1 b.toAdd)
      rw [s_word_mul, map_mul] }

private theorem binarySEquiv_pi : binarySEquiv D e binaryPi = piPoint D e := by
  apply Subtype.ext
  change D.a10ModelEmbedding e (elementaryWord 1 (1,0,0,0)) = D.z
  have h : elementaryWord 1 (1,0,0,0) = pi := by decide +kernel
  rw [h, D.a10ModelEmbedding_central e]

private noncomputable def ninePoints : Finset (ambientElementary D e 1) :=
  lambdaNine.map (binarySEquiv D e).toEquiv.toEmbedding

omit [Finite G] in
private theorem ninePoints_card : (ninePoints D e).card = 9 := by
  rw [ninePoints, Finset.card_map, lambdaNine_card]

private theorem ninePoints_prod :
    letI := ambientElementary_isElementaryAbelian D e 1
    ∏ a ∈ ninePoints D e, a = piPoint D e := by
  let := ambientElementary_isElementaryAbelian D e 1
  change ∏ a ∈ lambdaNine.map (binarySEquiv D e).toEquiv.toEmbedding, a = piPoint D e
  rw [Finset.prod_map]
  change ∏ a ∈ lambdaNine, binarySEquiv D e a = piPoint D e
  rw [← map_prod, lambdaNine_prod, binarySEquiv_pi]

private theorem ninePoints_subset_orbit
    (hl : ∃ n : sNormalizer D e, (n : G) * D.z * (n : G)⁻¹ = D.a10ModelEmbedding e lam)
    (hpl : ∃ n : sNormalizer D e, (n : G) * D.z * (n : G)⁻¹ = D.a10ModelEmbedding e (pi*lam)) :
    (ninePoints D e : Set (ambientElementary D e 1)) ⊆
      MulAction.orbit (sNormalizer D e) (piPoint D e) := by
  have hseed (i : Fin 3) : ∃ n : sNormalizer D e,
      (n : G) * D.z * (n : G)⁻¹ = D.a10ModelEmbedding e (lambdaSeed i) := by
    fin_cases i
    · refine ⟨1, ?_⟩
      simpa [lambdaSeed] using (D.a10ModelEmbedding_central e).symm
    · exact hl
    · exact hpl
  intro y hy
  obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hy
  obtain ⟨b,i,hi⟩ := lambdaNine_conjugate a ha
  obtain ⟨n,hn⟩ := hseed i
  let t : sNormalizer D e := ⟨D.a10ModelEmbedding e (conjugator b),
    ambientSylow_le_normalizer_S D e (mem_map_of_mem _ (conjugator_mem b))⟩
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨t*n, Subtype.ext ?_⟩
  change ((t : G) * (n : G)) * D.z * ((t : G) * (n : G))⁻¹ =
    D.a10ModelEmbedding e (elementaryWord 1 a.toAdd)
  calc
    _ = (t : G) * ((n : G) * D.z * (n : G)⁻¹) * (t : G)⁻¹ := by group
    _ = _ := by
      rw [hn]
      change D.a10ModelEmbedding e (conjugator b) * D.a10ModelEmbedding e (lambdaSeed i) *
        (D.a10ModelEmbedding e (conjugator b))⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul, hi]

private theorem orbit_eq_ninePoints
    (h72 : Nat.card (sNormalizerQuotient D e) = 72)
    (hl : ∃ n : sNormalizer D e, (n : G) * D.z * (n : G)⁻¹ = D.a10ModelEmbedding e lam)
    (hpl : ∃ n : sNormalizer D e, (n : G) * D.z * (n : G)⁻¹ = D.a10ModelEmbedding e (pi*lam)) :
    MulAction.orbit (sNormalizer D e) (piPoint D e) = (ninePoints D e : Set _) := by
  have hq := quotient_card D e
  rw [h72] at hq
  have hcard : (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard = 9 := by omega
  symm
  apply Set.eq_of_subset_of_ncard_le (ninePoints_subset_orbit D e hl hpl)
  rw [hcard, Set.ncard_coe_finset, ninePoints_card]

/-- The two proposed lambda fusions cannot coexist with the order-72 normalizer quotient. -/
public theorem lambda_order72_false [IsSimpleGroup G]
    (h : IsConj D.z (D.a10ModelEmbedding e lam) ∧
      IsConj D.z (D.a10ModelEmbedding e (pi*lam)))
    (x : sNormalizer D e) (hx : orderOf x = 3)
    (_hc : Commute (x : G) (D.a10ModelEmbedding e (pi*mu)))
    (h72 : Nat.card (sNormalizerQuotient D e) = 72) : False := by
  let := ambientElementary_isElementaryAbelian D e 1
  have hz := z_mem_ambientElementary D e 1
  have hlm : D.a10ModelEmbedding e lam ∈ ambientElementary D e 1 :=
    mem_map_of_mem _ (elementaryGenerators_mem 1 3)
  have hl := s_controls_fusion_of_order72 D e h72 hz hlm h.1
  have hplm : D.a10ModelEmbedding e (pi*lam) ∈ ambientElementary D e 1 := by
    rw [map_mul, D.a10ModelEmbedding_central e]
    exact mul_mem hz hlm
  have hpl := s_controls_fusion_of_order72 D e h72 hz hplm h.2
  have he := orbit_eq_ninePoints D e h72 hl hpl
  have hperm : ∀ a : ambientElementary D e 1,
      a ∈ ninePoints D e ↔ (ambientElementary D e 1).normalizerMonoidHom x a ∈ ninePoints D e := by
    intro a
    change a ∈ (ninePoints D e : Set _) ↔
      x • a ∈ (ninePoints D e : Set _)
    rw [← he]
    constructor
    · intro ha
      obtain ⟨n,rfl⟩ := MulAction.mem_orbit_iff.mp ha
      exact MulAction.mem_orbit_iff.mpr ⟨x*n, mul_smul _ _ _⟩
    · intro ha
      obtain ⟨n,hn⟩ := MulAction.mem_orbit_iff.mp ha
      exact MulAction.mem_orbit_iff.mpr ⟨x⁻¹*n, by rw [mul_smul,hn]; simp⟩
  have hp : (ambientElementary D e 1).normalizerMonoidHom x
      (∏ a ∈ ninePoints D e, a) = ∏ a ∈ ninePoints D e, a := by
    rw [map_prod]
    apply Finset.prod_equiv ((ambientElementary D e 1).normalizerMonoidHom x).toEquiv hperm
    intro a _
    rfl
  rw [ninePoints_prod] at hp
  apply normalizer_three_not_centralize_pi D e x hx
  have heq := congrArg Subtype.val hp
  change (x : G) * D.z * (x : G)⁻¹ = D.z at heq
  exact mul_inv_eq_iff_eq_mul.mp heq

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation
