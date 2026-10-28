module

public import Theory.SpecificGroups.G2.ConwayRootFour.Pullback
public import Theory.SpecificGroups.G2.FiniteUniversalCover
public import Theory.AtlasPort.LinearGroups.G2.ShortRootFieldWitness

/-!
# The marked G₂(4) pullback of the Leech cover

The coordinate module constructs an actual Leech isometry with square equal
to the nonidentity central sign. Given an injective homomorphism from the
split-octonion G₂(4) model carrying C(1) to its quotient image, the literal
pullback has a central kernel of order two, embeds in the Leech cover, and
every lift of C(1) squares to its nonidentity central sign. It has no section.
The root C(1) is a non-two-central involution of the actual octonion model.

The field-transport construction reduces the geometric input for an arbitrary
field of order four to the canonical `FiniteCover.FourField` used by the
universal-cover owner. All homomorphisms and the root marking are preserved.

Source: Aschbacher–Smith I.2.2(5), printed p.411/PDF422; Aschbacher,
Sporadic Groups (1994), Lemmas 46.9 and 49.5, printed pp.254 and 283–284.
The existence of the marked embedding and its identification with the source
root-four geometry remain unproved inputs here. These conditional pullback
results do not establish that source theorem.
-/

@[expose] public section

namespace Atlas.G2.ConwayRootFour
open Atlas.Lattices Atlas.Conway Atlas.SplitOctonion Explicit

variable {F K : Type*} [Field F] [Field K]

/-- Coefficient transport retains the particular short root, including its parameter. -/
theorem fieldEquiv_rootC (e : F ≃+* K) (a : F) :
    fieldEquiv e (rootC a) = rootC (e a) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;> simp [fieldEquiv, transportAutomorphism, transportLinear,
    mapCoefficients, rootC, rootCEquiv, rootCLinear, rootCApply]

/-- A field identification with the carrier already used by the universal cover. -/
noncomputable def fieldFourEquiv [Finite F] (hF : Nat.card F = 4) :
    F ≃+* FiniteCover.FourField := by
  letI := Fintype.ofFinite F
  letI := Fintype.ofFinite FiniteCover.FourField
  apply FiniteField.ringEquivOfCardEq
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
    GaloisField.card 2 2 (by decide)]
  decide

/-- Transport an actual marked Conway embedding; this constructs no embedding
without the input homomorphism. -/
noncomputable def transportEmbedding [Finite F] (hF : Nat.card F = 4)
    (f : FiniteCover.FourBase →* LeechCentralQuotient) : Model F →* LeechCentralQuotient :=
  f.comp (fieldEquiv (fieldFourEquiv hF)).toMonoidHom

theorem transportEmbedding_injective [Finite F] (hF : Nat.card F = 4)
    {f : FiniteCover.FourBase →* LeechCentralQuotient} (hf : Function.Injective f) :
    Function.Injective (transportEmbedding hF f) :=
  hf.comp (fieldEquiv (fieldFourEquiv hF)).injective

theorem transportEmbedding_marked [Finite F] (hF : Nat.card F = 4)
    {f : FiniteCover.FourBase →* LeechCentralQuotient}
    (hm : f (rootC 1) = markedInvolution) :
    transportEmbedding hF f (rootC (1 : F)) = markedInvolution := by
  change f (fieldEquiv (fieldFourEquiv hF) (rootC 1)) = _
  rw [fieldEquiv_rootC, map_one, hm]

theorem rootC_one_sq [Finite F] (hF : Nat.card F = 4) : (rootC (1 : F)) ^ 2 = 1 := by
  let : CharP F 2 := charP_of_injective_ringHom
    (f := (fieldFourEquiv hF).symm.toRingHom) (fieldFourEquiv hF).symm.injective 2
  rw [pow_two, rootC_add, CharTwo.add_self_eq_zero, rootC_zero]

theorem rootC_one_order [Finite F] (hF : Nat.card F = 4) : orderOf (rootC (1 : F)) = 2 := by
  apply orderOf_eq_prime (rootC_one_sq hF)
  intro h
  exact one_ne_zero (rootC_injective (h.trans rootC_zero.symm))

theorem rootC_one_not_twoCentral [Finite F] (hF : Nat.card F = 4) :
    ¬ Theory.GroupTheory.IsSylowCentralInvolution (rootC (1 : F)) := by
  let : CharP F 2 := charP_of_injective_ringHom
    (f := (fieldFourEquiv hF).symm.toRingHom) (fieldFourEquiv hF).symm.injective 2
  exact ShortRootFieldWitness.rootC_one_not_twoCentral

/-- The square assertion for every lift, with the literal pullback projection. -/
theorem rootC_lift_square [Finite F] (hF : Nat.card F = 4)
    (f : Model F →* LeechCentralQuotient) (hm : f (rootC 1) = markedInvolution)
    {x : pullback f} (hx : projection f x = rootC 1) : x ^ 2 = centralSign f :=
  lift_sq_of_marked f (rootC_one_sq hF) hm hx

/-- A marked lift in the genuine restricted cover, together with its order and square. -/
theorem exists_rootC_lift [Finite F] (hF : Nat.card F = 4)
    (f : Model F →* LeechCentralQuotient) (hf : Function.Injective f)
    (hm : f (rootC 1) = markedInvolution) :
    ∃ x : pullback f, projection f x = rootC 1 ∧
      x ^ 2 = centralSign f ∧ orderOf x = 4 := by
  obtain ⟨x, hx⟩ := projection_surjective f (rootC 1)
  exact ⟨x, hx, rootC_lift_square hF f hm hx, lift_order_of_marked hf hm hx⟩

/-- The marked short root obstructs splitting of this actual double extension. -/
theorem rootC_no_section [Finite F] (hF : Nat.card F = 4)
    (f : Model F →* LeechCentralQuotient) (hm : f (rootC 1) = markedInvolution) :
    ¬∃ s : Model F →* pullback f, (projection f).comp s = MonoidHom.id (Model F) :=
  no_section_of_marked f (rootC_one_sq hF) hm

end Atlas.G2.ConwayRootFour
