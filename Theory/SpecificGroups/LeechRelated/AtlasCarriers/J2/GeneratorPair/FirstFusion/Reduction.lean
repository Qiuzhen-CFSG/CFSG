module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.LocalData
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Reducing first-generator fusion to two finite J₂ calculations

The kernel-checked odd index of `C(t)` puts a Sylow two-subgroup inside it.
Sylow conjugacy therefore moves every nonidentity involution into this
centralizer. Once its involutions fuse to `a` or `t`, a pair passing the
published word tests must have first entry conjugate to `a`: conjugating a
putative `t`-pair contradicts the checked fourth-power identity.

`first_generator_conjugate_of_finite_checks` assembles the precise remaining
contracts. The local task supplies coverage by the 1920 centralizer words
and their involution fusion. Independently, the pair task checks the cube,
seventh-power, and fourth-power implication on the 1920 × 315 products.
The assembly discharges finite-representative coverage and all conjugation
transport; these extra finite-check premises are not yet proved here.

Source: the standard Sylow conjugacy theorem, ATLAS `J2G1-p100B0`, and the
J₂ involution/outer-group application in GLS3, Table 5.3g. The published
`PairProfile`, the actual degree-100 carrier, and the requested conclusion
are preserved, including that the final conjugator belongs to the carrier.
-/

public section
namespace Sporadic.LeechRelated.J2.GeneratorPair

namespace FirstFusion

theorem conjugate_into_centralizer {x : Carrier} (hx : x ^ 2 = 1) (hne : x ≠ 1) :
    ∃ z : centralizer, IsConj x (z : Carrier) := by
  let P : Sylow 2 centralizer := Sylow.nonempty.some
  have hQ : ¬2 ∣ ((P : Subgroup centralizer).map centralizer.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Fact.out P.not_dvd_index centralizer_odd_index
  let S : Sylow 2 Carrier := (P.2.map centralizer.subtype).toSylow hQ
  obtain ⟨z, hz⟩ := S.exists_isConj_of_orderOf_eq_prime_pow
    ((orderOf_eq_prime hx hne).trans (pow_one 2).symm)
  exact ⟨⟨z, Subgroup.map_subtype_le (P : Subgroup centralizer) z.property⟩, hz⟩

theorem involution_fusion_of_local
    (hlocal : ∀ z : centralizer, (z : Carrier) ^ 2 = 1 → (z : Carrier) ≠ 1 →
      IsConj a (z : Carrier) ∨ IsConj t (z : Carrier))
    {x : Carrier} (hx : x ^ 2 = 1) (hne : x ≠ 1) : IsConj a x ∨ IsConj t x := by
  obtain ⟨z, hz⟩ := conjugate_into_centralizer hx hne
  obtain ⟨g, hg⟩ := isConj_iff.mp hz
  have hg' : (MulAut.conj g) x = (z : Carrier) := hg
  have hz2 : (z : Carrier) ^ 2 = 1 := by
    rw [← hg', ← map_pow, hx, map_one]
  have hzn : (z : Carrier) ≠ 1 := by
    intro hh
    exact hne ((MulAut.conj g).injective (hg'.trans (hh.trans (map_one _).symm)))
  rcases hlocal z hz2 hzn with ha | ht
  · exact Or.inl (ha.trans hz.symm)
  · exact Or.inr (ht.trans hz.symm)

end FirstFusion

theorem PairProfile.first_ne_one {x y : Carrier} (h : PairProfile x y) : x ≠ 1 := by
  intro hx
  apply h.2.2.2.2
  simp [hx]

theorem first_generator_conjugate_of_local_fusion
    (hlocal : ∀ z : FirstFusion.centralizer,
      (z : Carrier) ^ 2 = 1 → (z : Carrier) ≠ 1 →
      IsConj a (z : Carrier) ∨ IsConj FirstFusion.t (z : Carrier))
    (hexclude : ∀ v : Carrier, v ^ 3 = 1 → (FirstFusion.t * v) ^ 7 = 1 →
      (FirstFusion.t * v * FirstFusion.t * v⁻¹) ^ 4 = 1)
    (x y : Carrier) (h : PairProfile x y) : ∃ g : Carrier, x = MulAut.conj g a := by
  rcases FirstFusion.involution_fusion_of_local hlocal h.1 h.first_ne_one with ha | ht
  · obtain ⟨g, hg⟩ := isConj_iff.mp ha
    exact ⟨g, hg.symm⟩
  · obtain ⟨g, hg⟩ := isConj_iff.mp ht.symm
    have h' := h.map (MulAut.conj g)
    have hx : (MulAut.conj g) x = FirstFusion.t := hg
    rw [hx] at h'
    exact False.elim (h'.2.2.2.2 (hexclude _ h'.2.1 h'.2.2.1))

/-- Assembly from the independent local enumeration and finite pair checks.
The coverage premise is required only here, not by the finite pair check. -/
theorem first_generator_conjugate_of_finite_checks
    (hcover : ∀ z ∈ FirstFusion.centralizer,
      ∃ i : Fin 1920, z = FirstFusion.centralizerElement i)
    (hlocal : ∀ i : Fin 1920,
      FirstFusion.centralizerElement i ^ 2 = 1 → FirstFusion.centralizerElement i ≠ 1 →
      IsConj a (FirstFusion.centralizerElement i) ∨
        IsConj FirstFusion.t (FirstFusion.centralizerElement i))
    (hcheck : ∀ (i : Fin 1920) (j : Fin 315),
      FirstFusion.pairRepresentative i j ^ 3 = 1 →
      (FirstFusion.t * FirstFusion.pairRepresentative i j) ^ 7 = 1 →
      (FirstFusion.t * FirstFusion.pairRepresentative i j * FirstFusion.t *
        (FirstFusion.pairRepresentative i j)⁻¹) ^ 4 = 1)
    (x y : Carrier) (h : PairProfile x y) : ∃ g : Carrier, x = MulAut.conj g a := by
  apply first_generator_conjugate_of_local_fusion ?_ ?_ x y h
  · intro z hz2 hzne
    obtain ⟨i, hi⟩ := hcover z z.property
    rw [hi] at hz2 hzne ⊢
    exact hlocal i hz2 hzne
  · intro v hv3 htv7
    obtain ⟨i, j, rfl⟩ := FirstFusion.pairRepresentative_cover hcover v
    exact hcheck i j hv3 htv7

end Sporadic.LeechRelated.J2.GeneratorPair
