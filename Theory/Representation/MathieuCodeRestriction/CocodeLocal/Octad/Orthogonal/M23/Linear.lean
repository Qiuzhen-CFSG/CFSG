module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Orthogonal.M23.Coordinates

/-!
# The even seven-coordinate model of the M23 octad space

Extension by zero sends the even words on the seven unfixed points to the
supported cocode space. Minimum distance makes this map injective: a codeword
supported on the octad is constant there, and here vanishes at the fixed point.
Both spaces have dimension six. The map intertwines the literal coordinate
actions; the alternating image then proves irreducibility.

Source: Aschbacher--Smith, H.15.2(2), printed pp.398--399.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Pointwise
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace MathieuCode.CocodeOctad

/-- The actual M23 restriction of the supported cocode action. -/
def m23PairRepresentation (O : Octad) :
    Representation Bit (m23OctadStabilizer O) (supportedPairSpace O.val) :=
  (pairRepresentation O).comp (m23ToOctad O)

lemma m23PairRepresentation_apply (O : Octad) (g : m23OctadStabilizer O)
    (v : supportedPairSpace O.val) :
    (m23PairRepresentation O g v).val = m23CocodeRepresentation g.val v.val := rfl

lemma seven_finrank (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    Module.finrank Bit (BinaryPermutation.core (octadSeven O)) = 6 := by
  let : Nonempty (octadSeven O) := Fintype.card_pos_iff.mp (by
    rw [Fintype.card_coe, octadSeven_card O hO]; decide)
  rw [BinaryPermutation.finrank_core, Fintype.card_coe, octadSeven_card O hO]

/-- Extension by zero, followed by the native cocode quotient. -/
def sevenToSupported (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    BinaryPermutation.core (octadSeven O) →ₗ[Bit] supportedPairSpace O.val :=
  (toCocode (octadSeven O)).codRestrict _ (by
    let : Nonempty (octadSeven O) := Fintype.card_pos_iff.mp (by
      rw [Fintype.card_coe, octadSeven_card O hO]; decide)
    intro v
    have hv : toCocode (octadSeven O) v ∈ supportedPairSpace (octadSeven O) := by
      rw [← range_toCocode]
      exact LinearMap.mem_range_self _ _
    exact supportedPairSpace_mono (Finset.erase_subset 0 O.val) hv)

lemma sevenToSupported_apply (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (v : BinaryPermutation.core (octadSeven O)) :
    (sevenToSupported O hO v).val = toCocode (octadSeven O) v := rfl

lemma sevenToSupported_injective (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    Function.Injective (sevenToSupported O hO) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro w hw
  have hc : extend (octadSeven O) w.val ∈ golay :=
    (Submodule.Quotient.mk_eq_zero codeInCore).mp (congrArg Subtype.val hw)
  have hz : extend (octadSeven O) w.val = 0 := by
    rcases supported_golay_word O hc (fun i hi =>
      extend_apply_not_mem _ _ i (fun h => hi (Finset.erase_subset _ _ h))) with hz | hcst
    · exact hz
    · have h := congrFun hcst 0
      rw [extend_apply_not_mem _ _ 0 (by simp [octadSeven])] at h
      simp [wordOfSet, hO] at h
  apply Subtype.ext
  apply extend_injective (octadSeven O)
  change extend (octadSeven O) w.val = extend (octadSeven O) 0
  rwa [map_zero]

/-- The six-dimensional even binary permutation module on the seven unfixed points. -/
def sevenCoreEquiv (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    BinaryPermutation.core (octadSeven O) ≃ₗ[Bit] supportedPairSpace O.val :=
  (sevenToSupported O hO).linearEquivOfInjective (sevenToSupported_injective O hO)
    ((seven_finrank O hO).trans (finrank_supportedPairSpace O).symm)

lemma sevenCoreEquiv_apply (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (v : BinaryPermutation.core (octadSeven O)) :
    (sevenCoreEquiv O hO v).val = toCocode (octadSeven O) v := rfl

private lemma extend_seven_permute (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (g : m23OctadStabilizer O) (v : octadSeven O → Bit) :
    extend (octadSeven O)
        (BinaryPermutation.representation (octadSeven O) (sevenCoordinateAction O hO g) v) =
      fullRepresentation (pointEmbedding g.val) (extend (octadSeven O) v) := by
  ext i
  let u := toSevenStabilizer O hO g
  have hg := MulAction.mem_stabilizer_finset.mp u.property
  have hi : u.val.val.symm i ∈ octadSeven O ↔ i ∈ octadSeven O := by
    have hh : u.val.val (u.val.val.symm i) ∈ octadSeven O ↔
        u.val.val.symm i ∈ octadSeven O := hg (u.val.val.symm i)
    simpa only [Equiv.apply_symm_apply] using hh.symm
  by_cases h : i ∈ octadSeven O
  · have h' := hi.mpr h
    change (if hi : i ∈ octadSeven O then
      v ((sevenCoordinateAction O hO g).symm ⟨i, hi⟩) else 0) =
      (if hj : u.val.val.symm i ∈ octadSeven O then v ⟨u.val.val.symm i, hj⟩ else 0)
    simp only [dif_pos h, dif_pos h']
    rfl
  · have h' : u.val.val.symm i ∉ octadSeven O := fun hh => h (hi.mp hh)
    change (if hi : i ∈ octadSeven O then _ else 0) =
      (if hj : u.val.val.symm i ∈ octadSeven O then _ else 0)
    simp only [dif_neg h, dif_neg h']

/-- The linear identification retains the actual M23 action. -/
lemma sevenCoreEquiv_equivariant (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (g : m23OctadStabilizer O) (v : BinaryPermutation.core (octadSeven O)) :
    sevenCoreEquiv O hO
        (BinaryPermutation.coreRepresentation (octadSeven O) (sevenCoordinateAction O hO g) v) =
      m23PairRepresentation O g (sevenCoreEquiv O hO v) := by
  apply Subtype.ext
  change toCocode (octadSeven O) _ = cocodeRepresentation (pointEmbedding g.val)
    (toCocode (octadSeven O) v)
  apply congrArg codeInCore.mkQ
  apply Subtype.ext
  exact extend_seven_permute O hO g v.val

lemma seven_card_odd (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    Odd (Fintype.card (octadSeven O)) := by
  rw [Fintype.card_coe, octadSeven_card O hO]; decide

/-- The equivalent natural-section model, used to import alternating irreducibility. -/
def sevenNaturalEquiv (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    BinaryPermutation.natural (octadSeven O) ≃ₗ[Bit] supportedPairSpace O.val :=
  (BinaryPermutation.coreEquivNatural (octadSeven O) (seven_card_odd O hO)).symm.trans
    (sevenCoreEquiv O hO)

lemma sevenNaturalEquiv_equivariant (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (g : m23OctadStabilizer O) (v : BinaryPermutation.natural (octadSeven O)) :
    sevenNaturalEquiv O hO
        (BinaryPermutation.naturalRepresentation (octadSeven O) (sevenCoordinateAction O hO g) v) =
      m23PairRepresentation O g (sevenNaturalEquiv O hO v) := by
  obtain ⟨w, rfl⟩ := (BinaryPermutation.coreEquivNatural (octadSeven O)
    (seven_card_odd O hO)).surjective v
  rw [← BinaryPermutation.coreEquivNatural_equivariant]
  simpa only [sevenNaturalEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    using sevenCoreEquiv_equivariant O hO g w

lemma m23PairRepresentation_isIrreducible (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    Representation.IsIrreducible (m23PairRepresentation O) := by
  have hn : 5 ≤ Fintype.card (octadSeven O) := by
    rw [Fintype.card_coe, octadSeven_card O hO]; decide
  let := BinaryPermutation.alternatingNatural_isIrreducible (Ω := octadSeven O) hn
  let E := sevenNaturalEquiv O hO
  have : Nontrivial (supportedPairSpace O.val) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_supportedPairSpace]; decide)
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro S
  let T : Subrepresentation (BinaryPermutation.alternatingNaturalRepresentation
      (Ω := octadSeven O)) :=
    ⟨S.toSubmodule.comap E.toLinearMap, by
      intro d w hw
      obtain ⟨g, hg⟩ := sevenAlternatingAction_surjective O hO d
      change E (BinaryPermutation.naturalRepresentation (octadSeven O) d.val w) ∈ S
      rw [← hg]
      change sevenNaturalEquiv O hO
        (BinaryPermutation.naturalRepresentation _ (sevenCoordinateAction O hO g) w) ∈ S
      rw [sevenNaturalEquiv_equivariant]
      exact S.apply_mem_toSubmodule g hw⟩
  rcases eq_bot_or_eq_top T with hb | ht
  · left
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.comap_injective_of_surjective E.surjective
    change T.toSubmodule = Submodule.comap E.toLinearMap ⊥
    rw [hb]
    ext w
    change w = 0 ↔ E w = 0
    exact E.map_eq_zero_iff.symm
  · right
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.comap_injective_of_surjective E.surjective
    change T.toSubmodule = Submodule.comap E.toLinearMap ⊤
    rw [ht]
    rfl

lemma m23_quadratic_invariant (O : Octad) (g : m23OctadStabilizer O)
    (v : supportedPairSpace O.val) :
    quadratic O (m23PairRepresentation O g v) = quadratic O v :=
  quadratic_invariant O (m23ToOctad O g) v

end MathieuCode.CocodeOctad
