module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.AmbientTorus
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.LinearWitness
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.CosetLinearWitness.OddRootModels
public import Theory.SpecificGroups.SU3.SylowOmega
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.Conjugation

/-!
# The odd torus action in the coset centralizer

Write A = ⟨Z ∩ M⟩ and v = zu. Shearing transports the genuine unitary
cover from Lᵤ to Lᵥ. The elementary subgroup A has order q, and the
unitary Sylow omega calculation identifies A with the center of a Sylow
subgroup of Lᵥ. The ambient fixed torus acts on this precise group by
conjugation and fixes its Sylow center pointwise.

The intrinsic odd-order root-fixer theorem supplies a subgroup PSL₂(q)
containing that center and fixed by a generator of the cyclic torus. Its
image in G therefore centralizes the whole torus and zu, and contains z.
The final exports discharge the model premise of the conditional adapters
and apply the distinguished-linear-witness consumer, obtaining strict
containment and the actual second unitary cover with the same field size.
Only centralization of L by the ambient torus remains an explicit geometric
input, supplied independently in the final Lemma 13.2 assembly.

Source: GLS4, Chapter 2, proof of Lemma 13.2, and Chapter 4, Lemma 3.6(c,d).
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion.CosetLinearWitness
open Subgroup Theory.GroupTheory PFchapter1section1
open _root_.BenderSuzuki.MatrixGroups

universe w
variable {G : Type w} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t u : G} {n : ℕ}

private def conjugateClosureEquiv
    (h : IsProductDisconnected Z M) {v : G} (huv : IsConj u v) :
    centralizerClosure Z u ≃* centralizerClosure Z v := by
  let g := Classical.choose (isConj_iff.mp huv)
  have hg' : MulAut.conj g u = v := Classical.choose_spec (isConj_iff.mp huv)
  have hgi : MulAut.conj g⁻¹ v = u := by
    rw [← hg']
    simp [MulAut.conj_apply, mul_assoc]
  exact {
    toFun := fun x => ⟨MulAut.conj g x, hg' ▸ centralizerClosure_conj_mem h g u x.property⟩
    invFun := fun x => ⟨MulAut.conj g⁻¹ x, hgi ▸ centralizerClosure_conj_mem h g⁻¹ v x.property⟩
    left_inv := fun x => Subtype.ext (by simp [MulAut.conj_apply, mul_assoc])
    right_inv := fun x => Subtype.ext (by simp [MulAut.conj_apply, mul_assoc])
    map_mul' := fun x y => Subtype.ext ((MulAut.conj g).map_mul x y) }

private theorem cover_of_equiv {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) (hc : IsUnitaryCentralizerCoverAt n H) :
    IsUnitaryCentralizerCoverAt n K := by
  obtain ⟨E, _, _, J, hJ, hcard, hfixed, hp | hs⟩ := hc
  · exact ⟨E, inferInstance, inferInstance, J, hJ, hcard, hfixed,
      Or.inl ⟨e.symm.trans hp.some⟩⟩
  · exact ⟨E, inferInstance, inferInstance, J, hJ, hcard, hfixed,
      Or.inr ⟨e.symm.trans hs.some⟩⟩

omit [Finite G] in
private theorem pair_centralizes_linear
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u) :
    u ∈ centralizer (residualGenerated M z t : Set G) := by
  intro x hx
  exact mem_centralizer_singleton_iff.mp
    (centralizerClosure_le Z u ((hunitary u huD hu).1.le hx))

omit [Finite G] in
/-- Shearing preserves the actual special/projective cover and both field orders. -/
public theorem coset_unitary_cover
    (h : IsProductDisconnected Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (hshear : ResidualCentralizerShearing Z M t)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u) :
    IsUnitaryCentralizerCoverAt n (centralizerClosure Z (z * u)) := by
  have hzL : z ∈ residualGenerated M z t :=
    (show zpowers z ≤ residualGenerated M z t from le_sup_left.trans le_sup_left) (mem_zpowers z)
  have hzu : Commute z u := pair_centralizes_linear hunitary huD hu z hzL
  exact cover_of_equiv (conjugateClosureEquiv h
    (hshear u huD hu z (subset_closure ⟨hz, hzM⟩) hzu)) (hunitary u huD hu).2

private theorem center_of_unitary_sylow
    {H : Type*} [Group H] [Finite H] (hn : 2 ≤ n)
    (hc : IsUnitaryCentralizerCoverAt n H) (P : Sylow 2 H) :
    omegaOneAmbient (P : Subgroup H) = (center P).map (P : Subgroup H).subtype ∧
      Nat.card (omegaOneAmbient (P : Subgroup H)) = 2 ^ n := by
  obtain ⟨E, _, _, J, hJ, hcard, hfixed, hp | hs⟩ := hc
  · have hh := HermitianForm.SylowOmega.omega_of_projective_equiv
      J hn hcard hfixed hJ hp.some P
    exact ⟨hh.1, hh.2.2⟩
  · have hh := HermitianForm.SylowOmega.omega_of_special_equiv
      J hn hcard hfixed hJ hs.some P
    exact ⟨hh.1, hh.2.2⟩

/-- In a genuine binary unitary cover, an elementary subgroup of order q is
exactly a Sylow center. The statement retains the actual ambient inclusion. -/
public theorem elementary_eq_unitary_sylow_center
    {H : Type*} [Group H] [Finite H] (hn : 2 ≤ n)
    (hc : IsUnitaryCentralizerCoverAt n H) (A : Subgroup H)
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 2 ^ n) :
    ∃ P : Sylow 2 H, (center P).map (P : Subgroup H).subtype = A := by
  obtain ⟨P, hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨hcenter, hcard⟩ := center_of_unitary_sylow hn hc P
  have hAO : A ≤ omegaOneAmbient (P : Subgroup H) := by
    rw [← omegaOneAmbient_eq_self A]
    exact omegaOneAmbient_mono hAP
  have heq := eq_of_le_of_card_ge hAO (hcard.trans hA.symm).le
  exact ⟨P, hcenter.symm.trans heq.symm⟩

omit [Finite G] in
private theorem centralizer_normalizes_closure
    (h : IsProductDisconnected Z M) (v : G) :
    centralizer ({v} : Set G) ≤ normalizer (centralizerClosure Z v : Set G) := by
  apply le_normalizer_closure_iff.mpr
  intro g hg x hx
  exact subset_closure ⟨h.invariant g x hx.1,
    (centralizer ({v} : Set G)).mul_mem
      ((centralizer ({v} : Set G)).mul_mem hg hx.2)
      ((centralizer ({v} : Set G)).inv_mem hg)⟩

/-- The source root is a Sylow center of L_(zu), and the literal ambient
fixed torus acts on L_(zu) by conjugation, fixing that center pointwise. -/
public theorem coset_root_action
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) (hn : 2 ≤ n)
    (eL : residualGenerated M z t ≃* PSL2BinaryMatrixGroup n)
    (hshear : ResidualCentralizerShearing Z M t)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hBL : ambientFixedTorus Z M t u ≤ centralizer (residualGenerated M z t : Set G)) :
    ∃ (P : Sylow 2 (centralizerClosure Z (z * u)))
      (ρ : ambientFixedTorus Z M t u →* MulAut (centralizerClosure Z (z * u))),
      ((center P).map (P : Subgroup (centralizerClosure Z (z * u))).subtype).map
        (centralizerClosure Z (z * u)).subtype = closure (Z ∩ (M : Set G)) ∧
      (∀ b x, (ρ b x : G) = (b : G) * (x : G) * (b : G)⁻¹) ∧
      (∀ b x, x ∈ (center P).map (P : Subgroup (centralizerClosure Z (z * u))).subtype →
        ρ b x = x) := by
  let A := closure (Z ∩ (M : Set G))
  let F := centralizerClosure Z (z * u)
  let B := ambientFixedTorus Z M t u
  have hAL : A ≤ residualGenerated M z t :=
    residualGenerated_contains_distinguishedClosure h hz hzM ht htM
  obtain ⟨hAe, hAc⟩ := psl2_distinguishedClosure_elementary_card
    h r hz hzM ht htM hL ⟨eL⟩ hn hAL
  let : IsElementaryAbelian 2 A := hAe
  have hzA : z ∈ A := subset_closure ⟨hz, hzM⟩
  have huL := pair_centralizes_linear hunitary huD hu
  have hAF : A ≤ F := by
    apply (closure_le _).mpr
    intro a ha
    have haA : a ∈ A := subset_closure ha
    have haz : Commute a z := by
      exact congrArg Subtype.val (mul_comm' (⟨a, haA⟩ : A) ⟨z, hzA⟩)
    exact mem_centralizerClosure ha.1 (haz.mul_right (huL a (hAL haA)))
  let A' := A.subgroupOf F
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.subgroupOf hAF
  have hA' : Nat.card A' = 2 ^ n :=
    (Nat.card_congr (subgroupOfEquivOfLe hAF).toEquiv).trans hAc
  obtain ⟨P, hP⟩ := elementary_eq_unitary_sylow_center hn
    (coset_unitary_cover h hz hzM hshear hunitary huD hu) A' hA'
  have hBN : B ≤ normalizer (F : Set G) := by
    apply le_trans _ (centralizer_normalizes_closure h (z * u))
    intro b hb
    have hbz : Commute b z := (hBL hb z (hAL hzA)).symm
    have hbu : Commute b u := mem_centralizer_singleton_iff.mp
      (ambientFixedTorus_placement.2.2.2 hb)
    exact mem_centralizer_singleton_iff.mpr (hbz.mul_right hbu).eq
  let ρ := F.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  refine ⟨P, ρ, ?_, ?_, ?_⟩
  · rw [hP]
    exact map_subgroupOf_eq_of_le hAF
  · intro b x
    rfl
  · intro b x hx
    apply Subtype.ext
    change (b : G) * (x : G) * (b : G)⁻¹ = x
    have hxA : (x : G) ∈ A := (show x ∈ A' from hP ▸ hx)
    rw [← hBL b.property x (hAL hxA), mul_inv_cancel_right]

/-- Conditional transport of the intrinsic odd-order root-fixer theorem.
The model premise is universal over genuine covers and Sylow subgroups;
it contains no ambient subgroup witness or second-centralizer assumption. -/
public theorem coset_linear_witness_of_odd_root_fixers
    (hmodel : ∀ (K : Type w) [Group K] [Finite K],
      IsUnitaryCentralizerCoverAt n K → ∀ (P : Sylow 2 K) (α : MulAut K),
      Odd (orderOf α) →
      (∀ x ∈ (center P).map (P : Subgroup K).subtype, α x = x) →
      ∃ J : Subgroup K, Nonempty (J ≃* PSL2BinaryMatrixGroup n) ∧
        (center P).map (P : Subgroup K).subtype ≤ J ∧ ∀ x ∈ J, α x = x)
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) (hn : 2 ≤ n)
    (eL : residualGenerated M z t ≃* PSL2BinaryMatrixGroup n)
    (hshear : ResidualCentralizerShearing Z M t)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hBL : ambientFixedTorus Z M t u ≤ centralizer (residualGenerated M z t : Set G)) :
    ∃ I : Subgroup G, Nonempty (I ≃* PSL2BinaryMatrixGroup n) ∧ z ∈ I ∧
      I ≤ centralizer (ambientFixedTorus Z M t u : Set G) ∧
      I ≤ centralizer ({z * u} : Set G) := by
  let F := centralizerClosure Z (z * u)
  let B := ambientFixedTorus Z M t u
  obtain ⟨P, ρ, hP, hρ, hfix⟩ :=
    coset_root_action h r hz hzM ht htM hL hn eL hshear hunitary huD hu hBL
  obtain ⟨hcyc, _, hodd, _⟩ := ambientFixedTorus_properties h r ht htM hn hunitary huD hu
  obtain ⟨b, hb⟩ := B.isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  have hbB : b ∈ B := hb ▸ mem_zpowers b
  have hbodd : Odd (orderOf (ρ ⟨b, hbB⟩)) :=
    hodd.of_dvd_nat ((orderOf_map_dvd ρ ⟨b, hbB⟩).trans (orderOf_dvd_natCard _))
  obtain ⟨J, ⟨eJ⟩, hPJ, hJfix⟩ := hmodel F
    (coset_unitary_cover h hz hzM hshear hunitary huD hu)
    P (ρ ⟨b, hbB⟩) hbodd (hfix ⟨b, hbB⟩)
  let I := J.map F.subtype
  let eI : I ≃* PSL2BinaryMatrixGroup n :=
    (J.equivMapOfInjective F.subtype Subtype.val_injective).symm.trans eJ
  have hAI : closure (Z ∩ (M : Set G)) ≤ I := by
    rw [← hP]
    exact map_mono hPJ
  refine ⟨I, ⟨eI⟩, hAI (subset_closure ⟨hz, hzM⟩), ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩ c hc
    have hby : b * (y : G) * b⁻¹ = y :=
      (hρ ⟨b, hbB⟩ y).symm.trans (congrArg Subtype.val (hJfix y hy))
    have hBC : B ≤ centralizer ({(y : G)} : Set G) := by
      rw [← hb]
      exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp hby))
    exact mem_centralizer_singleton_iff.mp (hBC hc)
  · exact (map_subtype_le J).trans (centralizerClosure_le Z (z * u))

/-- The actual consumer of the coset construction. Only the intrinsic
odd-order unitary root-fixer theorem and the independently produced
centralization by the ambient torus remain explicit. -/
public theorem second_cover_of_odd_root_fixers
    (hmodel : ∀ (K : Type w) [Group K] [Finite K],
      IsUnitaryCentralizerCoverAt n K → ∀ (P : Sylow 2 K) (α : MulAut K),
      Odd (orderOf α) →
      (∀ x ∈ (center P).map (P : Subgroup K).subtype, α x = x) →
      ∃ J : Subgroup K, Nonempty (J ≃* PSL2BinaryMatrixGroup n) ∧
        (center P).map (P : Subgroup K).subtype ≤ J ∧ ∀ x ∈ J, α x = x)
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) (hn : 2 ≤ n)
    (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (eL : residualGenerated M z t ≃* PSL2BinaryMatrixGroup n)
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hshear : ResidualCentralizerShearing Z M t)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hBL : ambientFixedTorus Z M t u ≤ centralizer (residualGenerated M z t : Set G)) :
    residualGenerated M z t < distinguishedCentralizer Z (ambientFixedTorus Z M t u) ∧
      IsUnitaryCentralizerCoverAt n (distinguishedCentralizer Z (ambientFixedTorus Z M t u)) := by
  obtain ⟨I, ⟨eI⟩, hzI, hIB, hIv⟩ := coset_linear_witness_of_odd_root_fixers hmodel
    h r hz hzM ht htM hL hn eL hshear hunitary huD hu hBL
  obtain ⟨hc, _, _, hB⟩ := ambientFixedTorus_properties h r ht htM hn hunitary huD hu
  exact second_cover_of_distinguished_linear_witness h hz hlocal hn hcard eL
    (ambientFixedTorus Z M t u) hc hB hBL (pair_centralizes_linear hunitary huD hu)
    I eI hzI hIB hIv

/-- The additional linear subgroup in the coset centralizer, with the intrinsic
odd-order root-fixer premise discharged for both actual unitary covers.
Centralization of L by the ambient fixed torus is the independent geometric input. -/
public theorem coset_linear_witness
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) (hn : 2 ≤ n)
    (eL : residualGenerated M z t ≃* PSL2BinaryMatrixGroup n)
    (hshear : ResidualCentralizerShearing Z M t)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hBL : ambientFixedTorus Z M t u ≤ centralizer (residualGenerated M z t : Set G)) :
    ∃ I : Subgroup G, Nonempty (I ≃* PSL2BinaryMatrixGroup n) ∧ z ∈ I ∧
      I ≤ centralizer (ambientFixedTorus Z M t u : Set G) ∧
      I ≤ centralizer ({z * u} : Set G) := by
  apply coset_linear_witness_of_odd_root_fixers (n := n) ?_
    h r hz hzM ht htM hL hn eL hshear hunitary huD hu hBL
  intro K _ _ hcover P α hodd hfix
  exact unitary_cover_odd_root_fixed_linear hn hcover P α hodd hfix

/-- Applying the constructed subgroup to the distinguished-linear-witness
criterion gives the strict second centralizer and its genuine unitary cover.
No recognition or fixed-subgroup hypothesis for that centralizer is used. -/
public theorem second_cover_of_coset_linear_witness
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) (hn : 2 ≤ n)
    (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (eL : residualGenerated M z t ≃* PSL2BinaryMatrixGroup n)
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hshear : ResidualCentralizerShearing Z M t)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hBL : ambientFixedTorus Z M t u ≤ centralizer (residualGenerated M z t : Set G)) :
    residualGenerated M z t < distinguishedCentralizer Z (ambientFixedTorus Z M t u) ∧
      IsUnitaryCentralizerCoverAt n (distinguishedCentralizer Z (ambientFixedTorus Z M t u)) := by
  obtain ⟨I, ⟨eI⟩, hzI, hIB, hIv⟩ := coset_linear_witness
    h r hz hzM ht htM hL hn eL hshear hunitary huD hu hBL
  obtain ⟨hc, _, _, hB⟩ := ambientFixedTorus_properties h r ht htM hn hunitary huD hu
  exact second_cover_of_distinguished_linear_witness h hz hlocal hn hcard eL
    (ambientFixedTorus Z M t u) hc hB hBL (pair_centralizes_linear hunitary huD hu)
    I eI hzI hIB hIv

end BenderSuzuki.ZD.UnitaryExclusion.CosetLinearWitness
