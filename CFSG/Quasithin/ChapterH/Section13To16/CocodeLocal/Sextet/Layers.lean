module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Sextet.Geometry
public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Sextet.Layers.Middle
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers
public import Theory.Representation.BinaryPermutationNaturalStructure

/-!
# Composition factors of the native sextet cocode flag

Tetrad parity identifies the literal cocode quotient by `sextetPairSpace` with
the natural permutation module on the six parts. Its kernel calculation gives
the dimensions seven, six, and four of the pair space and the two sections.
The intertwining equation identifies the top action kernel with the kernel of
the actual part permutation, proved surjective by compatible affine coordinates.
The natural top factor is irreducible. The middle factor is equivariantly the
dual of conjugation on the transported hexacode translations, with the exact
translation kernel; the tetrad line is simple. Thus all three factors of the
literal geometric flag are irreducible.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.15.3(1),
printed p.400. Identification of the tetrad line with the intrinsic-kernel
fixed space, intrinsic prime-core identifications, and the full transvection
and fixed-space-span assertions remain with the H.15.3 assembly owner.
-/

@[expose] public section

noncomputable section
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode Representation.BinaryOffender

lemma sextetPairSpace_finrank (S : Sextet) :
    Module.finrank (ZMod 2) (sextetPairSpace S) = 7 := sextetPairSpan_finrank S

lemma sextetLineInPair_finrank (S : Sextet) :
    Module.finrank (ZMod 2) (sextetLineInPair S).toSubmodule = 1 := by
  change Module.finrank (ZMod 2) ((sextetTetradLine S).comap (sextetPairSpace S).subtype) = 1
  rw [(Submodule.comapSubtypeEquivOfLe (sextetTetradLine_le_pairSpace S)).finrank_eq,
    sextetTetradLine_finrank]

lemma sextetMiddle_finrank (S : Sextet) :
    Module.finrank (ZMod 2) ((sextetPairSpace S) ⧸ (sextetLineInPair S).toSubmodule) = 6 := by
  have h := (sextetLineInPair S).toSubmodule.finrank_quotient_add_finrank
  have hp : Module.finrank (ZMod 2) (sextetPairSubrepresentation S).toSubmodule = 7 :=
    sextetPairSpace_finrank S
  rw [sextetLineInPair_finrank, hp] at h
  exact Nat.add_right_cancel h

lemma sextetTop_finrank (S : Sextet) :
    Module.finrank (ZMod 2) (Cocode ⧸ sextetPairSpace S) = 4 := by
  have h := (sextetPairSpace S).finrank_quotient_add_finrank
  rw [sextetPairSpace_finrank, finrank_cocode] at h
  omega

lemma sextetPairSpace_lt_top (S : Sextet) : sextetPairSpace S < ⊤ := by
  apply lt_of_le_of_ne le_top
  intro he
  have h := sextetPairSpace_finrank S
  rw [he, finrank_top, finrank_cocode] at h
  omega

/-- The top parity equivalence with the chapter's literal quotient carrier. -/
def sextetTopModelEquiv (S : Sextet) :
    (Cocode ⧸ (sextetPairSubrepresentation S).toSubmodule) ≃ₗ[ZMod 2]
      BinaryPermutation.natural (SextetPart S) := sextetTopEquiv S

/-- The parity identification intertwines the actual quotient representation. -/
lemma sextetTopModelEquiv_equivariant (S : Sextet) (g : sextetStabilizer S)
    (v : Cocode ⧸ (sextetPairSubrepresentation S).toSubmodule) :
    sextetTopModelEquiv S ((sextetPairSubrepresentation S).quotientRepresentation g v) =
      BinaryPermutation.naturalRepresentation (SextetPart S) (sextetPartPerm S g)
        (sextetTopModelEquiv S v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ v => exact sextetCocodeParity_equivariant S g v

/-- The action kernel on the top factor is precisely the kernel of the action on parts. -/
lemma sextetTop_action_kernel (S : Sextet) :
    (sextetPairSubrepresentation S).quotientRepresentation.ker = (sextetPartPerm S).ker := by
  ext g
  change (sextetPairSubrepresentation S).quotientRepresentation g = 1 ↔ sextetPartPerm S g = 1
  constructor
  · intro hg
    apply sextetNatural_faithful S
    rw [map_one]
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := (sextetTopModelEquiv S).surjective v
    rw [← sextetTopModelEquiv_equivariant, LinearMap.congr_fun hg]
    rfl
  · intro hg
    apply LinearMap.ext
    intro v
    apply (sextetTopModelEquiv S).injective
    rw [sextetTopModelEquiv_equivariant, hg, map_one]
    rfl

/-- Surjectivity of the actual part action suffices for the top factor's irreducibility.
The marking/transport construction is responsible for that surjectivity. -/
lemma sextetTop_isIrreducible_of_surjective (S : Sextet)
    (hsurj : Function.Surjective (sextetPartPerm S)) :
    Representation.IsIrreducible (sextetPairSubrepresentation S).quotientRepresentation := by
  let := BinaryPermutation.alternatingNatural_isIrreducible
    (Ω := SextetPart S) (by rw [card_sextetPart]; decide)
  let e := sextetTopModelEquiv S
  let : Nontrivial (BinaryPermutation.natural (SextetPart S)) :=
    Subrepresentation.irreducible_module_nontrivial
      (BinaryPermutation.alternatingNaturalRepresentation (Ω := SextetPart S))
  let : Nontrivial (Cocode ⧸ (sextetPairSubrepresentation S).toSubmodule) :=
    (Equiv.nontrivial_congr e.toEquiv).mpr inferInstance
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro P
  let W : Subrepresentation (BinaryPermutation.alternatingNaturalRepresentation
      (Ω := SextetPart S)) :=
    { toSubmodule := P.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule := by
        intro g v hv
        obtain ⟨w,hw,rfl⟩ := hv
        obtain ⟨s,hs⟩ := hsurj g.val
        refine ⟨(sextetPairSubrepresentation S).quotientRepresentation s w,
          P.apply_mem_toSubmodule s hw, ?_⟩
        exact (sextetTopModelEquiv_equivariant S s w).trans (by rw [hs]; rfl) }
  rcases eq_bot_or_eq_top W with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    have hm : e v ∈ W := ⟨v,hv,rfl⟩
    rw [h] at hm
    change e v = 0 at hm
    exact e.injective (hm.trans e.map_zero.symm)
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro v _
    have hm : e v ∈ W := by rw [h]; trivial
    obtain ⟨w,hw,he⟩ := hm
    exact e.injective he ▸ hw

/-- The natural top factor is irreducible for the actual native stabilizer. -/
lemma sextetTop_isIrreducible (S : Sextet) :
    Representation.IsIrreducible (sextetPairSubrepresentation S).quotientRepresentation :=
  sextetTop_isIrreducible_of_surjective S
    (SextetLayers.CoordinateTransport.nativePartPerm_surjective S)

/-- The top parity identification as an equivalence of representations. -/
def sextetTopRepresentationEquiv (S : Sextet) :
    (sextetPairSubrepresentation S).quotientRepresentation.Equiv
      ((BinaryPermutation.naturalRepresentation (SextetPart S)).comp (sextetPartPerm S)) :=
  .mk (sextetTopModelEquiv S)
    (fun g => LinearMap.ext (sextetTopModelEquiv_equivariant S g))

/-- The kernel on the natural top factor is the transported column kernel. -/
lemma sextetTop_action_kernel_eq_columnKernel (S : Sextet) :
    (sextetPairSubrepresentation S).quotientRepresentation.ker =
      Atlas.Codes.sextetCoordinateHom.ker.map
        (SextetLayers.CoordinateTransport.nativeStabilizerEquiv S).toMonoidHom := by
  rw [sextetTop_action_kernel, SextetLayers.CoordinateTransport.nativePartPerm_kernel]

lemma sextetTop_action_kernel_card (S : Sextet) :
    Nat.card (sextetPairSubrepresentation S).quotientRepresentation.ker = 192 := by
  rw [sextetTop_action_kernel, SextetLayers.CoordinateTransport.nativePartPerm_kernel_card]

/-- The faithful top actor is the full symmetric group on the actual six tetrads. -/
def sextetTopActorEquiv (S : Sextet) :
    (sextetStabilizer S ⧸ (sextetPartPerm S).ker) ≃* Equiv.Perm (SextetPart S) :=
  QuotientGroup.quotientKerEquivOfSurjective (sextetPartPerm S)
    (SextetLayers.CoordinateTransport.nativePartPerm_surjective S)

/-- The geometric flag has three nonzero irreducible factors. The source's
identification of its first term with the intrinsic-kernel fixed space is separate. -/
theorem sextet_composition_factors (S : Sextet) :
    ⊥ < sextetTetradLine S ∧
    sextetTetradLine S < sextetPairSpace S ∧
    sextetPairSpace S < ⊤ ∧
    Representation.IsIrreducible (sextetLineSubrepresentation S).toRepresentation ∧
    Representation.IsIrreducible (sextetLineInPair S).quotientRepresentation ∧
    Representation.IsIrreducible (sextetPairSubrepresentation S).quotientRepresentation :=
  ⟨bot_lt_iff_ne_bot.mpr (sextetTetradLine_ne_bot S),
    sextetTetradLine_lt_pairSpace S, sextetPairSpace_lt_top S,
    sextetLine_isIrreducible S, sextetMiddle_isIrreducible S, sextetTop_isIrreducible S⟩

end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
