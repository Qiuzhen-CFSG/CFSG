module

public import Theory.AtlasPort.LinearGroups.G2.LieSylowCenter
public import Theory.AtlasPort.LinearGroups.G2.LongRootNormalGeneration
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance.Normalizers
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Core
public import Theory.GroupTheory.ConjugacyFamilySpan

public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Weak closure of the highest-root group in G₂

A highest-root displacement has zero product with every other such
displacement. Conjugation preserves this octonion identity. Applied to the
basis vectors indexed by 1 and 7 in the unipotent chart, it forces the sixth
root coordinate to vanish. Conversely, the three positive long-root groups
and their unipotent conjugates generate all five remaining coordinates when
the field has more than two elements. The radical center then identifies its
normalizer with the short parabolic.

This supplies the model weak-closure geometry for Aschbacher–Smith E.1.14(1),
printed p.214, citing Aschbacher [Asc82a], Lemma 4.7. Coordinate definitions and
root relations are from the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Subgroup
namespace Atlas.G2.HighestRootWeakClosure
open Atlas.SplitOctonion Explicit LieParabolicSetup
variable {F : Type*} [Field F]

private theorem rootA_displacements (a : F) (x y : Carrier F) :
    SplitOctonion.mul ((rootA a).val x - x) ((rootA a).val y - y) = 0 := by
  ext i
  fin_cases i <;> simp [SplitOctonion.mul, rootA, rootAEquiv, rootALinear, rootAApply]

private theorem conjugate_displacements (g : Model F) (a : F) (x y : Carrier F) :
    SplitOctonion.mul ((g * rootA a * g⁻¹).val x - x)
      ((g * rootA a * g⁻¹).val y - y) = 0 := by
  have hx : (g * rootA a * g⁻¹).val x - x =
      g.val ((rootA a).val (g.val.symm x) - g.val.symm x) := by
    rw [map_sub, LinearEquiv.apply_symm_apply]
    rfl
  have hy : (g * rootA a * g⁻¹).val y - y =
      g.val ((rootA a).val (g.val.symm y) - g.val.symm y) := by
    rw [map_sub, LinearEquiv.apply_symm_apply]
    rfl
  rw [hx, hy, ← automorphism_mul, rootA_displacements, map_zero]

/-- Every conjugate long-root element in U has zero sixth root coordinate. -/
theorem conjugate_rootA_mem_radical {g : Model F} {a : F}
    (hu : g * rootA a * g⁻¹ ∈ unipotent) :
    g * rootA a * g⁻¹ ∈ radical₁ := by
  rw [unipotent_eq_range] at hu
  obtain ⟨t, ht⟩ := hu
  have h := congrFun (conjugate_displacements g a (basisVector 1) (basisVector 7)) 2
  rw [← ht] at h
  have hc : SplitOctonion.mul
      ((unipotentProduct t).val (basisVector 1) - basisVector 1)
      ((unipotentProduct t).val (basisVector 7) - basisVector 7) 2 = (t 5)^2 := by
    simp [SplitOctonion.mul, unipotentProduct, basisVector,
      rootA,rootB,rootC,rootD,rootE,rootF,rootAEquiv,rootBEquiv,rootCEquiv,
      rootDEquiv,rootEEquiv,rootFEquiv,rootALinear,rootBLinear,rootCLinear,
      rootDLinear,rootELinear,rootFLinear,rootAApply,rootBApply,rootCApply,
      rootDApply,rootEApply,rootFApply, pow_two]
  rw [hc] at h
  exact ⟨t, (sq_eq_zero_iff.mp h), ht⟩

/-- The full inner conjugacy orbit of the additive highest-root subgroup. -/
def rootOrbit : Set (Subgroup (Model F)) :=
  Set.range fun g : Model F => highestRoot.map (MulAut.conj g).toMonoidHom

theorem rootOrbit_invariant : SubgroupFamily.ConjugationInvariant (rootOrbit (F := F)) := by
  rintro A ⟨g, rfl⟩ h
  refine ⟨h * g, ?_⟩
  rw [map_map]
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- The conjugate root groups lying in U are contained in its five-root radical. -/
theorem span_le_radical : SubgroupFamily.span (rootOrbit (F := F)) unipotent ≤ radical₁ := by
  apply sSup_le
  rintro A ⟨⟨g, rfl⟩, hA⟩ x ⟨z, ⟨a, rfl⟩, rfl⟩
  apply conjugate_rootA_mem_radical
  exact hA (mem_map_of_mem _ ⟨a, rfl⟩)

private theorem rootC_inverse (a : F) : (rootC a)⁻¹ = rootC (-a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [rootC_add, add_neg_cancel, rootC_zero]

/-- Three long-root groups and their U-conjugates generate the five-root radical. -/
theorem radical_le_of_long_roots (H : Subgroup (Model F))
    (hN : unipotent ≤ normalizer (H : Set (Model F)))
    (hA : ∀ a : F, rootA a ∈ H) (hB : ∀ a : F, rootB a ∈ H)
    (hE : ∀ a : F, rootE a ∈ H) (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    radical₁ ≤ H := by
  have hp (a s : F) : rootC (a*s^2) * rootD (-a*s) ∈ H := by
    have hc : rootF s * rootE a * rootF (-s) ∈ H := by
      rw [rootF_neg]
      exact (mem_normalizer_iff.mp (hN (subset_closure (by simp))) _).mp (hE a)
    rw [rootF_conjugate_rootE] at hc
    have hc' : rootA (-a^2*s^3) * rootB (-a*s^3) *
        (rootC (a*s^2) * rootD (-a*s)) ∈ H := by
      simpa only [mul_assoc] using (H.mul_mem_cancel_right (hE a)).mp hc
    exact (H.mul_mem_cancel_left (H.mul_mem (hA _) (hB _))).mp hc'
  have ht : t^2-t ≠ 0 := by
    rw [show t^2-t = t*(t-1) by ring]
    exact mul_ne_zero ht0 (sub_ne_zero.mpr ht1)
  have hC (a : F) : rootC a ∈ H := by
    let b := a / (t^2-t)
    have hm := H.mul_mem (hp b t) (H.inv_mem (hp (b*t) 1))
    have he : (rootC (b*t^2) * rootD (-b*t)) *
        (rootC (b*t*1^2) * rootD (-(b*t)*1))⁻¹ = rootC a := by
      simp only [one_pow, mul_one, neg_mul, mul_inv_rev]
      rw [mul_assoc, ← mul_assoc (rootD (-(b*t))), mul_inv_cancel, one_mul,
        rootC_inverse, rootC_add]
      congr 1
      dsimp [b]
      field_simp
      ring
    rwa [he] at hm
  have hD (a : F) : rootD a ∈ H := by
    have h := hp (-a) 1
    simp only [one_pow, mul_one, neg_neg] at h
    exact (H.mul_mem_cancel_left (hC (-a))).mp h
  rintro g ⟨v, hv, rfl⟩
  simp only [unipotentProduct, hv, rootF_zero, mul_one]
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (hA _) (hB _)) (hC _)) (hD _)) (hE _)

theorem span_eq_radical [Finite F] (hq : 2 < Nat.card F) :
    SubgroupFamily.span (rootOrbit (F := F)) unipotent = radical₁ := by
  apply le_antisymm span_le_radical
  let W := SubgroupFamily.span (rootOrbit (F := F)) unipotent
  have hN : unipotent ≤ normalizer (W : Set (Model F)) :=
    unipotent.le_normalizer.trans
      (SubgroupFamily.normalizer_le_span_normalizer rootOrbit_invariant unipotent)
  have hin (g : Model F) (h : highestRoot.map (MulAut.conj g).toMonoidHom ≤ unipotent)
      (a : F) : g * rootA a * g⁻¹ ∈ W :=
    SubgroupFamily.le_span (family := rootOrbit) ⟨g,rfl⟩ h (mem_map_of_mem _ ⟨Multiplicative.ofAdd a,rfl⟩)
  have hA (a : F) : rootA a ∈ W := by
    have h := hin 1 (by
      rintro _ ⟨x, ⟨b,rfl⟩, rfl⟩
      simpa [highestRootHom] using (show rootA b.toAdd ∈ unipotent from subset_closure (by simp))) a
    simpa using h
  have hB (a : F) : rootB a ∈ W := by
    rw [← weylR_rootA]
    apply hin
    rintro _ ⟨x, ⟨b,rfl⟩, rfl⟩
    change weylR * rootA b.toAdd * weylR⁻¹ ∈ unipotent
    rw [weylR_rootA]
    exact subset_closure (by simp)
  have hE (a : F) : rootE a ∈ W := by
    have he (b : F) : (weylS * weylR) * rootA b * (weylS * weylR)⁻¹ = rootE b := by
      calc
        _ = weylS * (weylR * rootA b * weylR⁻¹) * weylS⁻¹ := by group
        _ = rootE b := by rw [weylR_rootA, weylS_rootB]
    rw [← he]
    apply hin
    rintro _ ⟨x, ⟨b,rfl⟩, rfl⟩
    change (weylS * weylR) * rootA b.toAdd * (weylS * weylR)⁻¹ ∈ unipotent
    rw [he]
    exact subset_closure (by simp)
  classical
  let := Fintype.ofFinite F
  have hc : ({0,1} : Finset F).card < (Finset.univ : Finset F).card := by
    simpa [Nat.card_eq_fintype_card] using hq
  obtain ⟨t,_,ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have ht' : t ≠ 0 ∧ t ≠ 1 := by simpa using ht
  exact radical_le_of_long_roots W hN hA hB hE t ht'.1 ht'.2

/-- The center of the five-root radical recovers its parabolic normalizer. -/
theorem normalizer_radical [CharP F 2] :
    normalizer (radical₁ (F := F) : Set (Model F)) = parabolic₁ := by
  apply le_antisymm _ parabolic₁_normalizes_radical₁
  have h := normalizer_le_normalizer_characteristic_image (radical₁ (F := F)) (center radical₁)
  rwa [center_map_eq_highestRoot radical₁ le_rfl (fiveRootSubgroup_le_unipotent _ _),
    SylowParabolicInvariance.normalizer_highestRoot] at h

end Atlas.G2.HighestRootWeakClosure
