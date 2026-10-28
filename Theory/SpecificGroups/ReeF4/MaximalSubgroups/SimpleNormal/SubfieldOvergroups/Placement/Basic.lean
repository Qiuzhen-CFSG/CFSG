module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.Contracts

/-!
# From split F4 conjugacy to Ree conjugacy

The representation-theoretic obligation compares the supplied socle with the
actual coefficient image of the smaller Ree derived group inside split F4.
It does not require its conjugator to be fixed by the Ree twist. Field descent
identifies that coefficient image with the standard derived subfield group.

If an endomorphism fixes two subgroups pointwise, the displacement of any
conjugator between them centralizes the target subgroup. A trivial target
centralizer therefore fixes the conjugator itself. Applied to the Ree twist,
this turns split F4 conjugacy into conjugacy in the Ree group. The centralizer
of the binary derived subgroup suffices for every subfield parameter.

These are conditional reductions for the subfield case of Malle,
*The maximal subgroups of ²F₄(q²)*, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E. The list in arXiv:0910.4758,
proof of Theorem 5, case 10, retains the full smaller Ree group.
The split conjugacy assertion below is still a proof obligation.
-/

public section

namespace ReeF4.MaximalSubgroups.SimpleNormal.Placement

open Subgroup ReeF4.Subfield

/-- The remaining representation geometry, with the original local hypotheses.
The target is an actual coefficient image and the conjugator is only required
to lie in split F4. Neither field descent nor a normalizer calculation is
assumed. The equivalence identifies the supplied socle, including at `k = 0`. -/
@[expose] def SplitConjugacy : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S →
      centralizer (S : Set M) = ⊥ →
      ∀ k, k < m → (2 * k + 1) ∣ (2 * m + 1) →
        (S ≃* _root_.commutator (Model k)) →
        ∃ (f : CoefficientField k →+* CoefficientField m) (a : SplitGroup m),
          ((S.map M.subtype).map (toSplitGroup m)).map (MulAut.conj a).toMonoidHom =
            (_root_.commutator (Model k)).map ((splitMap f).comp (toSplitGroup k))

/-- Descent identifies the image of the smaller derived group, without
identifying that derived group with the full smaller Ree group. -/
theorem map_commutator_reeMap_of_descent (hdesc : SubfieldDescent) {m k : ℕ}
    (hdiv : (2 * k + 1) ∣ (2 * m + 1))
    (f : CoefficientField k →+* CoefficientField m) :
    (_root_.commutator (Model k)).map (reeMap hdiv f) = derivedSubfield m k := by
  rw [map_commutator_eq, hdesc m k hdiv f]
  rfl

/-- The same identification in the split representation used by the
conjugacy calculation. -/
theorem map_commutator_splitMap_of_descent (hdesc : SubfieldDescent) {m k : ℕ}
    (hdiv : (2 * k + 1) ∣ (2 * m + 1))
    (f : CoefficientField k →+* CoefficientField m) :
    (_root_.commutator (Model k)).map ((splitMap f).comp (toSplitGroup k)) =
      (derivedSubfield m k).map (toSplitGroup m) := by
  have hf : (splitMap f).comp (toSplitGroup k) =
      (toSplitGroup m).comp (reeMap hdiv f) := by
    apply MonoidHom.ext
    intro x
    exact (toSplitGroup_reeMap hdiv f x).symm
  rw [hf, ← Subgroup.map_map, map_commutator_reeMap_of_descent hdesc hdiv f]

/-- Every derived subfield contains the binary one, so the binary split
centralizer calculation also supplies the centralizer for this parameter. -/
theorem derived_splitCentralizer_eq_bot (hC : BinaryDerivedSplitCentralizer)
    {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    centralizer ((derivedSubfield m k).map (toSplitGroup m) : Set (SplitGroup m)) = ⊥ := by
  have hle : derivedSubfield m 0 ≤ derivedSubfield m k := by
    apply commutator_mono <;> exact fixedSubfield_mono m (by simp)
  exact le_bot_iff.mp ((centralizer_le (Subgroup.map_mono hle)).trans_eq (hC m hm))

private theorem fixed_of_conjugates_of_centralizer_eq_bot {G : Type*} [Group G]
    (f : G →* G) (H K : Subgroup G)
    (hH : ∀ x ∈ H, f x = x) (hK : ∀ x ∈ K, f x = x)
    (hC : centralizer (K : Set G) = ⊥) {a : G}
    (ha : H.map (MulAut.conj a).toMonoidHom = K) : f a = a := by
  have hc : f a * a⁻¹ ∈ centralizer (K : Set G) := by
    apply mem_centralizer_iff.mpr
    intro y hy
    rw [← ha] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hfix := hK ((MulAut.conj a) x) (ha ▸ (mem_map.mpr ⟨x, hx, rfl⟩))
    simp only [MulAut.conj_apply, map_mul, map_inv, hH x hx] at hfix
    have he := congrArg (fun z => z * f a * a⁻¹) hfix
    simpa [MulAut.conj_apply, mul_assoc] using he.symm
  have he : f a * a⁻¹ = 1 := by simpa only [hC, mem_bot] using hc
  exact mul_inv_eq_one.mp he

/-- A split F4 conjugator between Ree subgroups is a Ree element when the
target has trivial centralizer in split F4. Both subgroups are fixed pointwise
by the Ree twist, so the conjugator's displacement is trivial. -/
theorem exists_ree_conjugator_of_split {m : ℕ} (H K : Subgroup (Model m))
    (hC : centralizer (K.map (toSplitGroup m) : Set (SplitGroup m)) = ⊥)
    (a : SplitGroup m)
    (ha : (H.map (toSplitGroup m)).map (MulAut.conj a).toMonoidHom =
      K.map (toSplitGroup m)) :
    ∃ g : Model m, H.map (MulAut.conj g).toMonoidHom = K := by
  have hfix (L : Subgroup (Model m)) : ∀ x ∈ L.map (toSplitGroup m), reeTwist m x = x := by
    rintro _ ⟨x, _, rfl⟩
    exact reeTwist_toSplitGroup m x
  have ha' : reeTwist m a = a :=
    fixed_of_conjugates_of_centralizer_eq_bot (reeTwist m) _ _ (hfix H) (hfix K) hC ha
  let g : Model m := ⟨a, (mem_fixedSubgroup m a).mpr ha'⟩
  refine ⟨g, (Subgroup.map_injective (toSplitGroup_injective m)) ?_⟩
  rw [Subgroup.map_map]
  have hmaps : (toSplitGroup m).comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp (toSplitGroup m) := by
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, MulAut.conj_apply, map_mul, map_inv]
    rw [toSplitGroup_apply m g]
  rw [hmaps, ← Subgroup.map_map]
  exact ha

end ReeF4.MaximalSubgroups.SimpleNormal.Placement
