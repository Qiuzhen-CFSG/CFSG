module

public import Theory.Representation.BinaryConjugationSection.tensorChief
public import Theory.GroupTheory.NoncentralChiefRefinement.BinaryFlagSections

/-!
# Chief factors of a scalar field section

Suppose the actual conjugation action on S/E is multiplication by the image
of a surjection to the units of a field of characteristic two. On the field
itself this action is irreducible over the prime field, since it is transitive
on nonzero vectors. A field basis of S/E gives equivariant homogeneous
coordinates. Pulling back its coordinate flag constructs actual noncentral
binary chief factors, one for each field dimension.

Source application: the scalar cubic on the maximal quotient U_L/W in
Aschbacher–Smith 13.8.30, printed p.964. The source must supply that quotient
and the scalar action of its actual subgroup L₀.
-/

@[expose] public section
open Subgroup Representation
namespace NoncentralChiefRefinement

variable {K F : Type*} [Group K] [Field F] [Algebra (ZMod 2) F]

/-- Scalar multiplication, regarded as a binary representation. -/
def scalarRepresentation (χ : K →* Fˣ) : Representation (ZMod 2) K F where
  toFun k :=
    { toFun := fun x => (χ k : F) * x
      map_add' := mul_add _
      map_smul' := by intro c x; simp only [Algebra.smul_def, RingHom.id_apply]; ring }
  map_one' := by ext x; simp
  map_mul' k l := by ext x; simp [mul_assoc]

/-- The full scalar group is transitive on nonzero field elements. -/
theorem scalarRepresentation_irreducible (χ : K →* Fˣ)
    (hχ : Function.Surjective χ) : IsIrreducible (scalarRepresentation χ) := by
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · exact fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro P
  by_cases hp : P.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hp)
  right
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro w _
  by_cases hw : w = 0
  · subst w; exact P.toSubmodule.zero_mem
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  obtain ⟨g, hg⟩ := hχ (Units.mk0 (w / v) (div_ne_zero hw hv0))
  have he : scalarRepresentation χ g v = w := by
    change (χ g : F) * v = w
    rw [hg]
    exact div_mul_cancel₀ w hv0
  exact he ▸ P.apply_mem_toSubmodule g hv

/-- A nontrivial scalar moves the field element one. -/
theorem scalarRepresentation_noncentral (χ : K →* Fˣ) (hn : ∃ k, χ k ≠ 1) :
    ∃ k v, scalarRepresentation χ k v ≠ v := by
  obtain ⟨k, hk⟩ := hn
  refine ⟨k, 1, ?_⟩
  intro he
  apply hk
  apply Units.ext
  change (χ k : F) * 1 = 1 at he
  simpa only [mul_one, Units.val_one] using he

variable {G W : Type*} [Group G] [AddCommGroup W]
  [Module (ZMod 2) W] [Module F W]
  [FiniteDimensional F W]
  {H S E : Subgroup G} {ρ : Representation (ZMod 2) H W}

/-- A field basis gives coordinates on the literal relative quotient S/E,
intertwining its actual conjugation action with the scalar action. -/
noncomputable def scalarChiefCoordinates
    (d : BinaryConjugationSection H S E ρ) (χ : H →* Fˣ)
    (hscalar : ∀ h w, ρ h w = (χ h : F) • w) :
    SectionCoordinates d.lowerChiefNode d.upperChiefNode
      (scalarRepresentation χ) (Module.finrank F W) := by
  let e : W ≃ₗ[F] (Fin (Module.finrank F W) → F) := (Module.finBasis F W).equivFun
  let f : d.upperChiefNode.val →* Multiplicative (Fin (Module.finrank F W) → F) :=
    e.toAddEquiv.toMultiplicative.toMonoidHom.comp
      (d.coordinates.comp (subgroupOfEquivOfLe d.section_le).toMonoidHom)
  have hf : Function.Surjective f := e.surjective.comp
    (d.onto.comp (subgroupOfEquivOfLe d.section_le).surjective)
  have hk : f.ker = d.lowerChiefNode.val.subgroupOf d.upperChiefNode.val := by
    ext x
    change e (d.coordinates _).toAdd = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff]
    exact d.coordinates_eq_one_iff _
  refine
    { equiv := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hf)
      equivariant := ?_ }
  intro h x i
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ x
  exact (congrArg (fun w => e w i)
    (d.equivariant h ((subgroupOfEquivOfLe d.section_le) b))).trans (by
      rw [hscalar, map_smul]
      rfl)

/-- The constructed factors are chief for H and all noncentral; the count
is the field dimension, not a supplied numerical bound. -/
theorem exists_scalar_chief_refinement
    (d : BinaryConjugationSection H S E ρ) (χ : H →* Fˣ)
    (hχ : Function.Surjective χ) (hn : ∃ h, χ h ≠ 1)
    (hscalar : ∀ h w, ρ h w = (χ h : F) • w) :
    ∃ s : ChiefSeries H, s.head = d.lowerChiefNode ∧ s.last = d.upperChiefNode ∧
      s.length = Module.finrank F W ∧ s.noncentralTwoCount = Module.finrank F W := by
  let := scalarRepresentation_irreducible χ hχ
  obtain ⟨s, hs, ht, hl, hc, _⟩ :=
    (scalarChiefCoordinates d χ hscalar).exists_chief_refinement d.lower_le_upperChiefNode
      (scalarRepresentation_noncentral χ hn)
  exact ⟨s, hs, ht, hl, hc⟩

/-- Extending the literal section to any complete chief series preserves its
lower bound, by equivariant Jordan–Hölder. -/
theorem scalar_dimension_le_complete_count [Finite G]
    (d : BinaryConjugationSection H S E ρ) (χ : H →* Fˣ)
    (hχ : Function.Surjective χ) (hn : ∃ h, χ h ≠ 1)
    (hscalar : ∀ h w, ρ h w = (χ h : F) • w)
    (t : ChiefSeries H) (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    Module.finrank F W ≤ t.noncentralTwoCount := by
  obtain ⟨s, hs0, hs1, _, hc⟩ := exists_scalar_chief_refinement d χ hχ hn hscalar
  obtain ⟨u, hu0, hu1, hu⟩ := BinaryFlag.extend_count bot_le le_top s hs0 hs1
  have he := u.noncentralTwoCount_eq t (hu0.trans ht0.symm) (hu1.trans ht1.symm)
  omega

end NoncentralChiefRefinement
