module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.Placement.Basic

/-!
# Binary anchors for Ree subfield conjugacy

The coefficient embedding sends the binary derived Ree group into every larger
derived Ree group. Pulling it back along the supplied socle equivalence produces
an injective homomorphism into the actual ambient Ree group. No normality of
this binary subgroup in the maximal overgroup is claimed or needed.

The two remaining geometric assertions are independent. Binary conjugacy places
this small subgroup. Anchored rigidity must then recover the full binary group
and the relevant torus inside the positive-parameter socle, and show that these
generate the prescribed coefficient image. The full binary group and its derived
subgroup are distinct throughout. Neither geometric assertion is proved here.

Source: Malle, *The maximal subgroups of ²F₄(q²)*, J. Algebra 139 (1991),
52–69, DOI 10.1016/0021-8693(91)90283-E. Proposition 2.13 uses an A₆ and
its marked elementary abelian group of order nine for binary conjugacy;
§2.12 uses the full binary group and the torus T₈ for larger subfields.
The author manuscript is https://agag-malle.math.rptu.de/~malle/download/sub2f4.dvi.
Malle's q² is our coefficient-field cardinal 2^(2*m+1).
-/

public section

namespace ReeF4.MaximalSubgroups.SimpleNormal.Placement.SplitGeometry

open Subgroup ReeF4.Subfield

noncomputable section

/-- The coefficient map from the two-element field, with existence supplied by
field-degree divisibility. Its choice is unique by `binaryCoefficientHom_unique`. -/
def binaryCoefficientHom (m : ℕ) : CoefficientField 0 →+* CoefficientField m :=
  Classical.choice (nonempty_coefficientHom (k := 0) (m := m) (by simp))

/-- There is no choice of coefficient embedding at the binary endpoint. -/
theorem binaryCoefficientHom_unique {m : ℕ}
    (f : CoefficientField 0 →+* CoefficientField m) : f = binaryCoefficientHom m := by
  ext x
  have hx : x ^ 2 = x := by simpa using field_pow 0 x
  rcases eq_zero_or_one_of_sq_eq_self hx with rfl | rfl <;> simp

/-- The actual coefficient image of the binary derived subgroup in the full
ambient Ree group. This definition makes no field-descent assertion. -/
@[expose] def binaryDerivedImage (m : ℕ) : Subgroup (Model m) :=
  (_root_.commutator (Model 0)).map (reeMap (by simp) (binaryCoefficientHom m))

/-- A coefficient embedding restricts to the derived subgroups. -/
def derivedReeMap {k m : ℕ} (hdiv : (2 * k + 1) ∣ (2 * m + 1))
    (f : CoefficientField k →+* CoefficientField m) :
    _root_.commutator (Model k) →* _root_.commutator (Model m) :=
  ((reeMap hdiv f).comp (_root_.commutator (Model k)).subtype).codRestrict
    (_root_.commutator (Model m)) (by
      intro x
      have hle : (_root_.commutator (Model k)).map (reeMap hdiv f) ≤
          _root_.commutator (Model m) := by
        rw [map_commutator_eq]
        exact commutator_mono le_top le_top
      exact hle (mem_map.mpr ⟨x, x.property, rfl⟩))

/-- Restriction to the derived groups preserves the underlying coefficient map. -/
@[simp] theorem derivedReeMap_coe {k m : ℕ}
    (hdiv : (2 * k + 1) ∣ (2 * m + 1))
    (f : CoefficientField k →+* CoefficientField m)
    (x : _root_.commutator (Model k)) :
    (derivedReeMap hdiv f x : Model m) = reeMap hdiv f x := by rfl

/-- The induced homomorphism on derived subgroups is faithful. -/
theorem derivedReeMap_injective {k m : ℕ}
    (hdiv : (2 * k + 1) ∣ (2 * m + 1))
    (f : CoefficientField k →+* CoefficientField m) :
    Function.Injective (derivedReeMap hdiv f) := by
  intro x y h
  apply Subtype.ext
  exact reeMap_injective hdiv f (congrArg Subtype.val h)

/-- The supplied equivalence realizes the smaller derived group as the given
socle's actual ambient image, without any assertion about conjugacy. -/
def socleEmbedding {m k : ℕ} {M : Subgroup (Model m)} {S : Subgroup M}
    (e : S ≃* _root_.commutator (Model k)) :
    _root_.commutator (Model k) →* Model m :=
  (M.subtype.comp S.subtype).comp e.symm.toMonoidHom

/-- Faithfulness of the supplied socle embedding. -/
theorem socleEmbedding_injective {m k : ℕ} {M : Subgroup (Model m)}
    {S : Subgroup M} (e : S ≃* _root_.commutator (Model k)) :
    Function.Injective (socleEmbedding e) :=
  Subtype.val_injective.comp (Subtype.val_injective.comp e.symm.injective)

/-- Its range is exactly the image of the supplied subgroup. -/
@[simp] theorem socleEmbedding_range {m k : ℕ} {M : Subgroup (Model m)}
    {S : Subgroup M} (e : S ≃* _root_.commutator (Model k)) :
    (socleEmbedding e).range = S.map M.subtype := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact mem_map.mpr ⟨e.symm y, (e.symm y).property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨e ⟨y, hy⟩, ?_⟩
    change ((e.symm (e ⟨y, hy⟩) : S) : Model m) = (y : Model m)
    rw [e.symm_apply_apply]

/-- The binary derived subgroup inside the supplied socle, obtained by pulling
back the actual smaller coefficient embedding through its equivalence. -/
def binarySocleEmbedding {m k : ℕ} {M : Subgroup (Model m)} {S : Subgroup M}
    (e : S ≃* _root_.commutator (Model k)) :
    _root_.commutator (Model 0) →* Model m :=
  (socleEmbedding e).comp (derivedReeMap (by simp) (binaryCoefficientHom k))

/-- The binary anchor remains faithful after pullback and ambient inclusion. -/
theorem binarySocleEmbedding_injective {m k : ℕ} {M : Subgroup (Model m)}
    {S : Subgroup M} (e : S ≃* _root_.commutator (Model k)) :
    Function.Injective (binarySocleEmbedding e) :=
  (socleEmbedding_injective e).comp
    (derivedReeMap_injective (by simp) (binaryCoefficientHom k))

/-- The constructed binary anchor lies in the supplied ambient socle. -/
theorem binarySocleEmbedding_range_le {m k : ℕ} {M : Subgroup (Model m)}
    {S : Subgroup M} (e : S ≃* _root_.commutator (Model k)) :
    (binarySocleEmbedding e).range ≤ S.map M.subtype := by
  rw [← socleEmbedding_range e]
  rintro x ⟨y, rfl⟩
  exact ⟨derivedReeMap (by simp) (binaryCoefficientHom k) y, rfl⟩

/-- The binary conjugacy obligation from Malle's Proposition 2.13. The image
need not be normal in the ambient maximal subgroup: positive-parameter socles
supply it via `binarySocleEmbedding`. Only this one binary group is classified.
The source root argument gives a Ree conjugator; no split-centralizer theorem
or ambient simplicity is assumed. -/
@[expose] def BinaryConjugacy : Prop :=
  ∀ m, 1 ≤ m → ∀ ι : _root_.commutator (Model 0) →* Model m,
    Function.Injective ι → ∃ g : Model m,
      ι.range.map (MulAut.conj g).toMonoidHom = binaryDerivedImage m

/-- The remaining positive-parameter geometry after the binary derived subgroup
has been placed. All original local hypotheses are retained, and the conclusion
concerns an actual coefficient image. This is a reduction contract for §2.12,
not its literal statement: a proof must recover the full binary subgroup from
this derived anchor and justify the torus-generation step. Binary conjugacy,
field descent, and the desired normalizer calculation are not premises. -/
@[expose] def AnchoredRigidity : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S →
      centralizer (S : Set M) = ⊥ →
      ∀ k, 1 ≤ k → k < m → ∀ hdiv : (2 * k + 1) ∣ (2 * m + 1),
        (S ≃* _root_.commutator (Model k)) → ∀ g : Model m,
        binaryDerivedImage m ≤ (S.map M.subtype).map (MulAut.conj g).toMonoidHom →
        ∃ f : CoefficientField k →+* CoefficientField m,
          (S.map M.subtype).map (MulAut.conj g).toMonoidHom =
            (_root_.commutator (Model k)).map (reeMap hdiv f)

end

end ReeF4.MaximalSubgroups.SimpleNormal.Placement.SplitGeometry

