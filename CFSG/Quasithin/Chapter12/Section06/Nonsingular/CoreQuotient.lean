module

public import CFSG.Quasithin.Chapter12.Section06.Setup
public import Theory.GroupTheory.PCoreImageRestriction

/-!
# The literal quotient centralizer in Section 12.6

The quotient-automorphism kernel defining C_G(A/O₂(A)) is equivalent to
normalizing A and having every commutator with A in O₂(A). Under a quotient
with two-group kernel, this condition agrees with the corresponding condition
on the image, provided normalization of the original A has been established.

This supplies the quotient comparison in Lemma 12.6.5 of Aschbacher--Smith,
combined manuscript (1 March 2004), printed p.824. It does not replace R by
its later centralizer description before that normalization is proved.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
variable {G D : Type*} [Group G] [Group D]

/-- The quotient action is trivial precisely when all commutators lie in the core. -/
theorem mem_coreQuotientCentralizer_iff (A : Subgroup G) (r : G) :
    r ∈ coreQuotientCentralizer A ↔
      r ∈ normalizer (A : Set G) ∧ ∀ a ∈ A, ⁅r, a⁆ ∈ A.pCoreIn 2 := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨n.property, ?_⟩
    intro a ha
    have he := congrArg (fun b : MulAut (A ⧸ pCore 2 A) =>
      b (QuotientGroup.mk' (pCore 2 A) ⟨a, ha⟩)) hn
    simp only [MonoidHom.comp_apply, quotientAut_apply_mk] at he
    change QuotientGroup.mk' (pCore 2 A) (A.normalizerMonoidHom n ⟨a, ha⟩) =
      QuotientGroup.mk' (pCore 2 A) ⟨a, ha⟩ at he
    refine ⟨_, QuotientGroup.eq_iff_div_mem.mp he, ?_⟩
    change (n : G) * a * (n : G)⁻¹ / a = ⁅(n : G), a⁆
    rw [div_eq_mul_inv, commutatorElement_def]
  · rintro ⟨hn, hc⟩
    refine ⟨⟨r, hn⟩, ?_, rfl⟩
    apply MulEquiv.ext
    intro w
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) w
    simp only [MonoidHom.comp_apply, quotientAut_apply_mk]
    change QuotientGroup.mk' (pCore 2 A) (A.normalizerMonoidHom ⟨r, hn⟩ a) =
      QuotientGroup.mk' (pCore 2 A) a
    apply QuotientGroup.eq_iff_div_mem.mpr
    obtain ⟨c, hc', he⟩ := hc a a.property
    have he' : c = A.normalizerMonoidHom ⟨r, hn⟩ a / a := by
      apply Subtype.ext
      change (c : G) = r * (a : G) * r⁻¹ / a
      simpa only [div_eq_mul_inv, commutatorElement_def, subtype_apply] using he
    exact he' ▸ hc'

variable [Finite G] [Finite D]


/-- Compare the two core quotients after normalization has been established. -/
theorem mem_coreQuotientCentralizer_iff_map (f : G →* D) (A : Subgroup G)
    (hk : IsPGroup 2 f.ker) {r : G} (hn : r ∈ normalizer (A : Set G)) :
    r ∈ coreQuotientCentralizer A ↔ f r ∈ coreQuotientCentralizer (A.map f) := by
  rw [mem_coreQuotientCentralizer_iff, mem_coreQuotientCentralizer_iff]
  have hn' : f r ∈ normalizer (A.map f : Set D) :=
    A.le_normalizer_map f (mem_map_of_mem f hn)
  simp only [hn, hn', true_and]
  constructor
  · intro h b hb
    obtain ⟨a, ha, rfl⟩ := hb
    have hc := (inf_comap_pCoreIn_eq_of_ker_isPGroup 2 f A hk).ge (h a ha)
    have hm : f ⁅r, a⁆ ∈ (A.map f).pCoreIn 2 := hc.2
    simpa only [map_commutatorElement] using hm
  · intro h a ha
    apply (inf_comap_pCoreIn_eq_of_ker_isPGroup 2 f A hk).le
    refine ⟨?_, ?_⟩
    · exact (le_normalizer_iff_commutator_le_right.mp
        (zpowers_le.mpr hn)) (commutator_mem_commutator (mem_zpowers r) ha)
    · change f ⁅r, a⁆ ∈ (A.map f).pCoreIn 2
      rw [map_commutatorElement]
      exact h (f a) (mem_map_of_mem f ha)
end CFSG.Quasithin.Chapter12.Section06
