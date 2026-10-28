module
public import Theory.GroupTheory.GeneralizedFitting.CentralizerQuotient
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.OddCentralInvolutionLifting
public import Mathlib.GroupTheory.Sylow

/-!
# Passing graph involutions through the component centralizer quotient

For a quasisimple generalized Fitting subgroup K, self-centralization
identifies C_G(K) with the embedded center of K. The quotient has simple
generalized Fitting subgroup canonically marked by K/Z(K), retains a Sylow
two-supplement, and is proper whenever K is proper. An outside quotient
involution lifts through the odd kernel to an original outside involution;
the original component and this lift generate G. The component restriction
and its conjugation identity use the literal quotient map throughout.

Source: the central-cover reduction in Aschbacher–Smith F.6.18(11), p.310,
and the centralizer quotient in 15.3.41, p.1138.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.QuasisimpleGraphQuotientLifting
variable {G : Type*} [Group G] [Finite G] (K : Subgroup G) [K.Normal]

omit [K.Normal] in
lemma centralizer_eq_embedded_center (hF : generalizedFitting G = K) :
    centralizer (K : Set G) = (center K).map K.subtype := by
  have hC : centralizer (K : Set G) ≤ K := hF ▸ centralizer_generalizedFitting_le G
  ext g
  constructor
  · intro hg
    refine ⟨⟨g, hC hg⟩, ?_, rfl⟩
    change (⟨g, hC hg⟩ : K) ∈ center K
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (hg k k.property)
  · rintro ⟨k, hk, rfl⟩ l hl
    exact congrArg Subtype.val (mem_center_iff.mp hk ⟨l, hl⟩)

lemma quotient_kernel_odd (hF : generalizedFitting G = K)
    (ho : Odd (Nat.card (center K))) : Odd (Nat.card (centralizerQuotientMap K).ker) := by
  change Odd (Nat.card (QuotientGroup.mk' (centralizer (K : Set G))).ker)
  rw [QuotientGroup.ker_mk', centralizer_eq_embedded_center K hF,
    card_map_of_injective K.subtype_injective]
  exact ho

variable [IsQuasisimple K] (hq : IsPGroup 2 (G ⧸ K))

@[expose] def fittingEquiv : K ⧸ center K ≃* generalizedFitting (CentralizerQuotient K) :=
  (centralizerQuotientComponentEquiv K).trans
    (MulEquiv.subgroupCongr (centralizerQuotient_generalizedFitting K hq).symm)

@[expose] def fittingMap : K →* generalizedFitting (CentralizerQuotient K) :=
  (fittingEquiv K hq).toMonoidHom.comp (QuotientGroup.mk' (center K))

@[simp] lemma fittingMap_coe (k : K) :
    (fittingMap K hq k : CentralizerQuotient K) = centralizerQuotientMap K k := by rfl

lemma fittingMap_surjective : Function.Surjective (fittingMap K hq) :=
  (fittingEquiv K hq).surjective.comp (QuotientGroup.mk'_surjective _)

lemma fittingMap_ker : (fittingMap K hq).ker = center K := by
  rw [fittingMap, MonoidHom.ker_comp_of_injective _ _ (fittingEquiv K hq).injective,
    QuotientGroup.ker_mk']

include hq in
lemma quotient_fitting_simple : IsSimpleGroup (generalizedFitting (CentralizerQuotient K)) := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  exact (fittingEquiv K hq).symm.isSimpleGroup

include hq in
lemma quotient_fitting_proper (hF : generalizedFitting G = K) (hproper : K ≠ ⊤) :
    generalizedFitting (CentralizerQuotient K) ≠ ⊤ := by
  intro h
  apply hproper
  have hker : (centralizerQuotientMap K).ker ≤ K := by
    rw [centralizerQuotientMap, QuotientGroup.ker_mk']
    exact hF ▸ centralizer_generalizedFitting_le G
  have hh := congrArg (Subgroup.comap (centralizerQuotientMap K)) h
  rw [centralizerQuotient_generalizedFitting K hq, centralizerQuotientComponent,
    comap_map_eq, comap_top, sup_eq_left.mpr hker] at hh
  exact hh

include hq in
lemma quotient_fitting_sup_sylow (T : Sylow 2 G)
    (hgen : K ⊔ (T : Subgroup G) = ⊤) :
    generalizedFitting (CentralizerQuotient K) ⊔
      (T.mapSurjective (QuotientGroup.mk'_surjective (centralizer (K : Set G))) :
        Subgroup (CentralizerQuotient K)) = ⊤ := by
  rw [centralizerQuotient_generalizedFitting K hq, centralizerQuotientComponent,
    Sylow.coe_mapSurjective, centralizerQuotientMap, ← Subgroup.map_sup, hgen,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

lemma fittingMap_conj (t : G) (x : K) :
    fittingMap K hq (MulAut.conjNormal t x) =
      MulAut.conjNormal (centralizerQuotientMap K t) (fittingMap K hq x) := by
  apply Subtype.ext
  simp only [fittingMap_coe, MulAut.conjNormal_apply, map_mul, map_inv]

include hq in
lemma exists_lift_involution (hF : generalizedFitting G = K)
    (ho : Odd (Nat.card (center K)))
    (b : CentralizerQuotient K) (hb : orderOf b = 2)
    (hout : b ∉ generalizedFitting (CentralizerQuotient K))
    (hgen : generalizedFitting (CentralizerQuotient K) ⊔ zpowers b = ⊤) :
    ∃ t : G, centralizerQuotientMap K t = b ∧ orderOf t = 2 ∧ t ∉ K ∧
      K ⊔ zpowers t = ⊤ := by
  let q := centralizerQuotientMap K
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  obtain ⟨t, ht, ht2⟩ := OddCentralLifting.exists_involution_lift q
    (quotient_kernel_odd K hF ho) hqs b (hb ▸ pow_orderOf_eq_one b)
  have htout : t ∉ K := by
    intro htk
    apply hout
    rw [centralizerQuotient_generalizedFitting K hq]
    exact ⟨t, htk, ht⟩
  have htgen : K ⊔ zpowers t = ⊤ := by
    have hmap : (K ⊔ zpowers t).map q = ⊤ := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, ht]
      rw [centralizerQuotient_generalizedFitting K hq] at hgen
      exact hgen
    have hh := congrArg (Subgroup.comap q) hmap
    rw [comap_map_eq, comap_top] at hh
    have hker : q.ker ≤ K ⊔ zpowers t := by
      apply le_sup_of_le_left
      change (QuotientGroup.mk' (centralizer (K : Set G))).ker ≤ K
      rw [QuotientGroup.ker_mk']
      exact hF ▸ centralizer_generalizedFitting_le G
    rwa [sup_eq_left.mpr hker] at hh
  exact ⟨t, ht, orderOf_eq_prime_iff.mpr
    ⟨ht2, fun h => htout (h ▸ one_mem _)⟩, htout, htgen⟩

end Theory.GroupTheory.QuasisimpleGraphQuotientLifting
