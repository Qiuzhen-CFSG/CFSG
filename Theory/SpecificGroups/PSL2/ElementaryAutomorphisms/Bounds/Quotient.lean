module

public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.OuterInvolutions
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms
public import Theory.ElementaryAbelian.CyclicKernel

/-!
# The split cyclic outer quotient from inner-field coverage

The field action injects into the actual quotient by the range of conjugation:
trace invariance detects its intersection with the inner subgroup. Coverage
makes this map surjective. Its inverse, composed with the quotient map, is a
surjective homomorphism to field automorphisms, split by `fieldAutHom` and with
kernel exactly `inner K`. Finite-field cyclicity gives the outer quotient and
the bound two for elementary subgroups disjoint from the inner subgroup.

The only automorphism-classification input is the stated coverage hypothesis.
Source: GLS, Volume 2, Theorem 26.24, Step 5 and the final contradiction,
`refs/KGroup/GLS2/ChapterG.tex`.
-/

namespace Theory.PSL2
variable {K : Type*} [Field K] [CharP K 2]

private noncomputable def fieldOuterHom :
    (K ≃+* K) →* MulAut (Group K) ⧸ inner K :=
  (QuotientGroup.mk' (inner K)).comp fieldAutHom

private theorem fieldOuterHom_injective :
    Function.Injective (fieldOuterHom (K := K)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply bot_unique
  intro σ hσ
  have hm : fieldAut σ ∈ inner K := (QuotientGroup.eq_one_iff _).mp hσ
  obtain ⟨g, hg⟩ := (mem_inner_iff K _).mp hm
  exact fieldAut_eq_conj_implies_refl σ g hg

variable (hcoverage : ∀ a : MulAut (Group K), ∃ (g : Group K) (σ : K ≃+* K),
  a = MulAut.conj g * fieldAut σ)

include hcoverage

private theorem fieldOuterHom_surjective :
    Function.Surjective (fieldOuterHom (K := K)) := by
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (inner K) x
  obtain ⟨g, σ, rfl⟩ := hcoverage a
  refine ⟨σ, ?_⟩
  change QuotientGroup.mk' (inner K) (fieldAut σ) = _
  have hg : QuotientGroup.mk' (inner K) (MulAut.conj g) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
  rw [map_mul, hg, one_mul]

/-- The field factor identifies the actual quotient by inner automorphisms. -/
public noncomputable def fieldOuterEquivOfCoverage
    (hcoverage : ∀ a : MulAut (Group K), ∃ (g : Group K) (σ : K ≃+* K),
      a = MulAut.conj g * fieldAut σ) :
    (K ≃+* K) ≃* MulAut (Group K) ⧸ inner K :=
  MulEquiv.ofBijective fieldOuterHom
    ⟨fieldOuterHom_injective, fieldOuterHom_surjective hcoverage⟩

/-- The field component of an automorphism, obtained from the actual outer quotient. -/
public noncomputable def fieldProjectionOfCoverage :
    MulAut (Group K) →* (K ≃+* K) :=
  (fieldOuterEquivOfCoverage hcoverage).symm.toMonoidHom.comp
    (QuotientGroup.mk' (inner K))

public theorem fieldProjectionOfCoverage_fieldAut (σ : K ≃+* K) :
    fieldProjectionOfCoverage hcoverage (fieldAut σ) = σ :=
  (fieldOuterEquivOfCoverage hcoverage).symm_apply_apply σ

public theorem fieldProjectionOfCoverage_split :
    (fieldProjectionOfCoverage hcoverage).comp fieldAutHom = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro σ
  exact fieldProjectionOfCoverage_fieldAut hcoverage σ

public theorem fieldProjectionOfCoverage_surjective :
    Function.Surjective (fieldProjectionOfCoverage hcoverage) :=
  fun σ => ⟨fieldAut σ, fieldProjectionOfCoverage_fieldAut hcoverage σ⟩

public theorem fieldProjectionOfCoverage_ker :
    (fieldProjectionOfCoverage hcoverage).ker = inner K := by
  ext a
  change (fieldOuterEquivOfCoverage hcoverage).symm
    (QuotientGroup.mk' (inner K) a) = 1 ↔ a ∈ inner K
  rw [← map_one (fieldOuterEquivOfCoverage hcoverage).symm,
    (fieldOuterEquivOfCoverage hcoverage).symm.injective.eq_iff]
  exact QuotientGroup.eq_one_iff a

public theorem outer_isCyclic_of_coverage [Finite K] :
    IsCyclic (MulAut (Group K) ⧸ inner K) := by
  let : IsCyclic (K ≃+* K) := OuterSolvable.finiteFieldAut_isCyclic
  exact isCyclic_of_surjective (fieldOuterEquivOfCoverage hcoverage).toMonoidHom
    (fieldOuterEquivOfCoverage hcoverage).surjective

/-- The elementary subgroup embeds in the cyclic field factor when its inner
intersection is trivial. -/
public theorem elementary_card_le_two_of_disjoint_inner [Finite K]
    (D : Subgroup (MulAut (Group K))) [IsElementaryAbelian 2 D]
    (hD : Disjoint D (inner K)) : Nat.card D ≤ 2 := by
  let : IsCyclic (K ≃+* K) := OuterSolvable.finiteFieldAut_isCyclic
  apply IsElementaryAbelian.card_le_of_disjoint_cyclic_kernel D
    (fieldProjectionOfCoverage hcoverage)
  rwa [fieldProjectionOfCoverage_ker]

end Theory.PSL2
