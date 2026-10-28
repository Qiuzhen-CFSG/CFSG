module

public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.Coordinates
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage.Operators
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage.OrderFourConjugacy
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage.PairCertificate

/-!
# Recognition of faithful even hexacode images

A faithful embedding sends the actual generating pair to operators satisfying
its power relations. Normalize the first operator, then conjugate the pair
into the actual model image. Membership for the generators gives membership
for the whole image. Faithfulness and finiteness construct an automorphism of
the even cover and the required intertwiner on the literal hexacode carrier.

Order-four conjugacy in dimension three is proved by matching nilpotent-chain
bases. The normalized-pair certificate covers all second matrices over F₄ by
kernel reduction and identifies their conjugates with words in the actual
generators. Together these discharge both premises of the reduction and give
`exists_twist` for every faithful embedding, without an irreducibility or
determinant hypothesis. The separate binary normalizer calculation is needed
only for extending recognition to the full group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, K.1.3,
printed p.453 (PDF p.464), and the `hc` input of
`SixDimensional.exists_equivariant_of_finite_inputs`.
-/

@[expose] public section
open Atlas.Codes Subgroup
namespace Representation.Hexacode.SixDimensional.EvenImage

/-- Faithful even images have determinant one, independently of the binary recovery. -/
theorem determinant_one (f : HexEvenAutomorphisms →* FieldGL)
    (g : HexEvenAutomorphisms) : LinearEquiv.det (f g) = 1 := by
  let d : HexEvenAutomorphisms →* Fˣ := LinearEquiv.det.comp f
  let _ : Group.IsPerfect HexEvenAutomorphisms := even_isPerfect
  let _ : Group.IsPerfect d.range := Group.IsPerfect.range d
  exact congrArg Subtype.val (Subsingleton.elim (⟨d g, ⟨g, rfl⟩⟩ : d.range) 1)

/-- Placing both generators in the model image constructs the group twist;
no choice of a preexisting representation equivalence is assumed. -/
theorem exists_twist_of_generator_conjugates
    (f : HexEvenAutomorphisms →* FieldGL) (hf : Function.Injective f)
    (c : FieldGL)
    (ha : MulAut.conj c (f generatorA) ∈ evenFieldAction.range)
    (hb : MulAut.conj c (f generatorB) ∈ evenFieldAction.range) :
    ∃ b : MulAut HexEvenAutomorphisms,
      ∀ g w, c (f g w) = evenFieldAction (b g) (c w) := by
  let j : HexEvenAutomorphisms →* FieldGL := (MulAut.conj c).toMonoidHom.comp f
  have hj : j.range ≤ evenFieldAction.range := by
    rw [MonoidHom.range_eq_map, ← generators_closure, MonoidHom.map_closure, closure_le]
    rintro _ ⟨g, hg, rfl⟩
    rcases hg with rfl | rfl
    · exact ha
    · exact hb
  let j' := j.codRestrict evenFieldAction.range (fun g => hj ⟨g, rfl⟩)
  let q := MonoidHom.ofInjective evenFieldAction_injective
  let b : HexEvenAutomorphisms →* HexEvenAutomorphisms := q.symm.toMonoidHom.comp j'
  have he (g : HexEvenAutomorphisms) : evenFieldAction (b g) = j g :=
    MonoidHom.apply_ofInjective_symm evenFieldAction_injective (j' g)
  have hbi : Function.Injective b := by
    intro g h hh
    apply hf
    apply (MulAut.conj c).injective
    change j g = j h
    rw [← he, ← he, hh]
  let e : MulAut HexEvenAutomorphisms :=
    MulEquiv.ofBijective b ⟨hbi, Finite.surjective_of_injective hbi⟩
  refine ⟨e, ?_⟩
  intro g w
  have h := LinearEquiv.congr_fun (he g) (c w)
  change evenFieldAction (e g) (c w) = c (f g (c.symm (c w))) at h
  simpa only [c.symm_apply_apply] using h.symm

/-- Normalizing order-four operators and certifying the remaining matrix pairs
suffices for the precise even intertwining input of six-dimensional recognition.
Both finite linear-algebra premises are still explicit. -/
theorem exists_twist_of_pair_inputs
    (hn : ∀ u : FieldGL, u ^ 4 = 1 → u ^ 2 ≠ 1 →
      ∃ d : FieldGL, MulAut.conj d u = fieldGenerator)
    (hp : ∀ v : FieldGL, v ^ 3 = 1 → (fieldGenerator * v) ^ 5 = 1 →
      (fieldGenerator * v ^ 2) ^ 3 = 1 →
      ∃ c : FieldGL, MulAut.conj c fieldGenerator ∈ evenFieldAction.range ∧
        MulAut.conj c v ∈ evenFieldAction.range)
    (f : HexEvenAutomorphisms →* FieldGL) (hf : Function.Injective f) :
    ∃ (b : MulAut HexEvenAutomorphisms) (c : FieldGL),
      ∀ g w, c (f g w) = evenFieldAction (b g) (c w) := by
  have h4 : f generatorA ^ 4 = 1 := by rw [← map_pow, generatorA_four, map_one]
  have h2 : f generatorA ^ 2 ≠ 1 := by
    intro h
    apply generatorA_sq_ne_one
    apply hf
    simpa only [map_pow, map_one] using h
  obtain ⟨d, hd⟩ := hn (f generatorA) h4 h2
  let j : HexEvenAutomorphisms →* FieldGL := (MulAut.conj d).toMonoidHom.comp f
  have hja : j generatorA = fieldGenerator := hd
  have hv3 : j generatorB ^ 3 = 1 := by rw [← map_pow, generatorB_three, map_one]
  have hav5 : (fieldGenerator * j generatorB) ^ 5 = 1 := by
    rw [← hja, ← map_mul, ← map_pow, generatorAB_five, map_one]
  have hav23 : (fieldGenerator * j generatorB ^ 2) ^ 3 = 1 := by
    rw [← hja, ← map_pow, ← map_mul, ← map_pow, generatorAB2_three, map_one]
  obtain ⟨c, hca, hcb⟩ := hp (j generatorB) hv3 hav5 hav23
  have hconj (g : HexEvenAutomorphisms) :
      MulAut.conj (c * d) (f g) = MulAut.conj c (j g) := by
    change (MulAut.conj (c * d)) (f g) = MulAut.conj c (MulAut.conj d (f g))
    rw [map_mul]
    rfl
  obtain ⟨b, hb⟩ := exists_twist_of_generator_conjugates f hf (c * d)
    (by rw [hconj, hja]; exact hca) (by rw [hconj]; exact hcb)
  exact ⟨b, c * d, hb⟩

/-- Every faithful field-linear action of the even cover on the actual hexacode
is equivalent to its model action after an automorphism of the even cover.
This discharges the `hc` input of `exists_equivariant_of_finite_inputs`. -/
theorem exists_twist
    (f : HexEvenAutomorphisms →* FieldGL) (hf : Function.Injective f) :
    ∃ (b : MulAut HexEvenAutomorphisms) (c : FieldGL),
      ∀ g w, c (f g w) = evenFieldAction (b g) (c w) :=
  exists_twist_of_pair_inputs exists_conjugator_of_order_four exists_pair_conjugates f hf

end Representation.Hexacode.SixDimensional.EvenImage
