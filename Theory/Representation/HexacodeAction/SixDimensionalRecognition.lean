module

public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.CentralField
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.Coordinates
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.Normalizer

/-!
# Recognition of the faithful six-dimensional binary hexacode representation

The central cubic recovers F₄ scalars from the original binary representation.
A classification of faithful embeddings of the even cover on the concrete
three-dimensional field space then supplies even intertwining coordinates.
Normality puts the whole transported group, including its odd coset, in the
binary normalizer of that image. As this normalizer is the concrete full
hexacode image, faithfulness and finiteness give an automorphism of the full
group and intertwining coordinates for every group element.

The conditional reduction keeps the two finite inputs explicit. The final
`exists_equivariant` theorem discharges them using the checked even-image
classification and exact binary normalizer calculation. In particular, an
even-group automorphism is never assumed to extend to the full group; the
full twist is constructed from the original action and the normalizer.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, K.1.3,
printed p.453 (PDF p.464), citing GM02, Table 6.3, and the terminal application
on printed p.1155 (PDF p.1172). The finite calculations use the actual
ATLAS hexacode action and kernel-checked matrix certificates.
-/

@[expose] public section

open Atlas.Codes Subgroup
namespace Representation.Hexacode.SixDimensional

variable {W : Type*} [AddCommGroup W] [Module Bit W]
    (ρ : Representation Bit HexAutomorphisms W)

/-- Even intertwining identifies the literal image of the even subgroup. -/
theorem even_image_of_intertwining (e : W ≃ₗ[Bit] hexacode)
    (b : MulAut HexEvenAutomorphisms)
    (he : ∀ (g : HexEvenAutomorphisms) w, e (ρ g.val w) = action (b g).val (e w)) :
    hexSign.ker.map (coordinateAction ρ e) = evenBinaryImage := by
  have hg (g : HexEvenAutomorphisms) : coordinateAction ρ e g.val = hexAction (b g).val := by
    apply LinearEquiv.ext
    intro w
    change e (ρ g.val (e.symm w)) = action (b g).val w
    rw [he, e.apply_symm_apply]
  ext t
  constructor
  · rintro ⟨g, hgmem, rfl⟩
    exact ⟨b ⟨g, hgmem⟩, (hg ⟨g, hgmem⟩).symm⟩
  · rintro ⟨g, rfl⟩
    refine ⟨(b.symm g).val, (b.symm g).property, ?_⟩
    rw [hg, b.apply_symm_apply]
    rfl

/-- The exact model normalizer promotes even intertwining to a full-group twist. -/
theorem exists_full_twist_of_even_intertwining
    (hn : Subgroup.normalizer (evenBinaryImage : Set BinaryGL) = hexAction.range)
    (hf : Function.Injective ρ) (e : W ≃ₗ[Bit] hexacode)
    (b : MulAut HexEvenAutomorphisms)
    (he : ∀ (g : HexEvenAutomorphisms) w, e (ρ g.val w) = action (b g).val (e w)) :
    ∃ a : MulAut HexAutomorphisms,
      ∀ g w, e (ρ g w) = action (a g) (e w) := by
  let f := coordinateAction ρ e
  have hmem (g : HexAutomorphisms) : f g ∈ hexAction.range := by
    rw [← hn, ← even_image_of_intertwining ρ e b he]
    apply Subgroup.le_normalizer_map f
    apply Subgroup.mem_map_of_mem
    rw [hexSign.ker.normalizer_eq_top]
    trivial
  let j : HexAutomorphisms →* hexAction.range := f.codRestrict hexAction.range hmem
  let q := MonoidHom.ofInjective hexAction_injective
  let a : HexAutomorphisms →* HexAutomorphisms := q.symm.toMonoidHom.comp j
  have ha (g : HexAutomorphisms) : hexAction (a g) = f g :=
    MonoidHom.apply_ofInjective_symm hexAction_injective (j g)
  have hai : Function.Injective a := by
    intro g h hh
    apply coordinateAction_injective ρ e hf
    rw [← ha, ← ha, hh]
  let A : MulAut HexAutomorphisms :=
    MulEquiv.ofBijective a ⟨hai, Finite.surjective_of_injective hai⟩
  refine ⟨A, ?_⟩
  intro g w
  have hh := LinearEquiv.congr_fun (ha g) (e w)
  change action (A g) (e w) = e (ρ g (e.symm (e w))) at hh
  simpa only [e.symm_apply_apply] using hh.symm

/-- The two finite matrix inputs suffice for intrinsic binary six-dimensional recognition. -/
theorem exists_equivariant_of_finite_inputs [Module.Finite Bit W]
    (hc : ∀ f : HexEvenAutomorphisms →* FieldGL, Function.Injective f →
      ∃ (b : MulAut HexEvenAutomorphisms) (c : FieldGL),
        ∀ g w, c (f g w) = evenFieldAction (b g) (c w))
    (hn : Subgroup.normalizer (evenBinaryImage : Set BinaryGL) = hexAction.range)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp hexSign.ker.subtype))
    (hd : Module.finrank Bit W = 6) :
    ∃ (a : MulAut HexAutomorphisms) (e : W ≃ₗ[Bit] hexacode),
      ∀ g w, e (ρ g w) = action (a g) (e w) := by
  have hq := scalar_quadratic ρ hf hi
  let := fieldModule ρ hq
  let := fieldTower ρ hq
  let E := fieldCoordinates ρ hq hd
  let f := coordinateAction (evenRepresentation ρ hq) E
  obtain ⟨b, c, hbc⟩ := hc f
    (coordinateAction_injective _ E (evenRepresentation_injective ρ hq hf))
  let e : W ≃ₗ[Bit] hexacode := (E.trans c).restrictScalars Bit
  have he (g : HexEvenAutomorphisms) (w : W) :
      e (ρ g.val w) = action (b g).val (e w) := by
    change c (E (ρ g.val w)) = action (b g).val (c (E w))
    have h := hbc g (E w)
    change c (E (ρ g.val (E.symm (E w)))) = action (b g).val (c (E w)) at h
    simpa only [E.symm_apply_apply] using h
  obtain ⟨a, ha⟩ := exists_full_twist_of_even_intertwining ρ hn hf e b he
  exact ⟨a, e, ha⟩

/-- Every faithful binary six-dimensional representation of the full hexacode group
whose even restriction is irreducible is quasiequivalent to the actual hexacode
action. The same coordinates intertwine every element, including the odd coset. -/
theorem exists_equivariant [Module.Finite Bit W]
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp hexSign.ker.subtype))
    (hd : Module.finrank Bit W = 6) :
    ∃ (a : MulAut HexAutomorphisms) (e : W ≃ₗ[Bit] hexacode),
      ∀ g w, e (ρ g w) = action (a g) (e w) :=
  exists_equivariant_of_finite_inputs ρ EvenImage.exists_twist
    normalizer_evenBinaryImage hf hi hd

end Representation.Hexacode.SixDimensional
