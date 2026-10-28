module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.CoordinateTransport.Coordinates
public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Comparison

/-!
# Constructing compatible coordinates for every native sextet

Native four-transitivity sends a tetrad of the standard sextet to a tetrad of
any given sextet. The native cocode recovers the whole partition from this
common tetrad class, so the same group element sends all six parts correctly.
Composing that element with the concrete standard ATLAS coordinates constructs
a code-preserving marking. Conjugating the checked standard stabilizer
comparison gives a group equivalence through exactly the same point map.

This reuses the native/ATLAS automorphism comparison proved in
`SextetCore.Comparison`, and the native tetrad recovery in `Sextet.Geometry`.
The former constructs a faithful coordinate homomorphism before proving its
surjectivity; no recognition from an abstract group order is used.

Source: Aschbacher–Smith H.15.3(1), printed p.400, and H.14.1(2), pp.396–397.
The concrete ATLAS code and affine model are by Gerald Höhn and ATLAS
contributors, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917, under the ATLAS
Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
-/

public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise
namespace MathieuCode.SextetLayers.CoordinateTransport
noncomputable section

private lemma tetrad_transitive (A B : Finset (Fin 24)) (hA : A.card = 4) (hB : B.card = 4) :
    ∃ g : M24, g • A = B := by
  let eA : Fin 4 ≃ A := (Finset.equivFinOfCardEq hA).symm
  let eB : Fin 4 ≃ B := (Finset.equivFinOfCardEq hB).symm
  let a : Fin 4 ↪ Fin 24 := eA.toEmbedding.trans (Function.Embedding.subtype _)
  let b : Fin 4 ↪ Fin 24 := eB.toEmbedding.trans (Function.Embedding.subtype _)
  let := m24_isFivePretransitive
  have ht : MulAction.IsMultiplyPretransitive M24 (Fin 24) 4 :=
    MulAction.isMultiplyPretransitive_of_le (n := 5) (by decide) (by simp)
  obtain ⟨g,hg⟩ := ht.exists_smul_eq a b
  have happ (i : Fin 4) : g • (eA i).val = (eB i).val :=
    congrArg (fun f : Fin 4 ↪ Fin 24 => f i) hg
  refine ⟨g, Finset.eq_of_subset_of_card_le ?_ (by simp [hA,hB])⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_smul_finset.mp hx
  obtain ⟨i,hi⟩ := eA.surjective ⟨y,hy⟩
  have hh : (eA i).val = y := congrArg Subtype.val hi
  rw [← hh, happ]
  exact (eB i).property

/-- Native four-transitivity and tetrad-class recovery transport the entire sextet. -/
lemma exists_sextet_conjugator (S : Sextet) : ∃ g : M24,
    g • standardSextet.parts = S.parts := by
  obtain ⟨A,hA⟩ := sextet_parts_nonempty standardSextet
  obtain ⟨B,hB⟩ := sextet_parts_nonempty S
  obtain ⟨g,hg⟩ := tetrad_transitive A B (standardSextet.tetrad A hA) (S.tetrad B hB)
  have hv : cocodeRepresentation g (sextetVector standardSextet) = sextetVector S := by
    rw [sextetVector_eq standardSextet hA, evenSetVector_equivariant]
    simpa only [hg] using (sextetVector_eq S hB).symm
  refine ⟨g, Finset.eq_of_subset_of_card_le ?_ (by simp [S.card,standardSextet.card])⟩
  intro C hC
  obtain ⟨D,hD,rfl⟩ := Finset.mem_smul_finset.mp hC
  apply (evenSetVector_eq_sextetVector_iff S (by simpa using standardSextet.tetrad D hD)).mp
  rw [← evenSetVector_equivariant g D (sextet_tetrad_even standardSextet hD),
    ← sextetVector_eq standardSextet hD, hv]

def sextetConjugator (S : Sextet) : M24 := (exists_sextet_conjugator S).choose

lemma sextetConjugator_parts (S : Sextet) :
    sextetConjugator S • standardSextet.parts = S.parts :=
  (exists_sextet_conjugator S).choose_spec

private def standardPart (i : Atlas.Codes.HexIndex) : SextetPart standardSextet :=
  ⟨(Atlas.Codes.tetrad i).image atlasPointEquiv, by
    rw [← SextetCore.nativeParts_distinguished]
    exact Finset.mem_image.mpr ⟨Atlas.Codes.tetrad i,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩,rfl⟩⟩

private lemma standardPart_bijective : Function.Bijective standardPart := by
  constructor
  · intro i j h
    apply Atlas.Codes.distinguished_sextet.injective
    exact Finset.image_injective atlasPointEquiv.injective (congrArg Subtype.val h)
  · intro B
    have hB : B.val ∈ SextetCore.nativeParts Atlas.Codes.distinguishedUnorderedSextet.val := by
      simpa only [SextetCore.nativeParts_distinguished] using B.property
    obtain ⟨A,hA,he⟩ := Finset.mem_image.mp hB
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    exact ⟨i,Subtype.ext he⟩

def standardMarking : Marking standardSextet where
  pointEquiv := atlasPointEquiv
  partEquiv := Equiv.ofBijective standardPart standardPart_bijective
  mem_part p i := by
    change atlasPointEquiv p ∈ (Atlas.Codes.tetrad i).image atlasPointEquiv ↔ p.1 = i
    constructor
    · intro h
      obtain ⟨q,hq,he⟩ := Finset.mem_image.mp h
      have hp := atlasPointEquiv.injective he
      exact (Atlas.Codes.mem_tetrad p i).mp (hp ▸ hq)
    · intro h
      exact Finset.mem_image.mpr ⟨p,(Atlas.Codes.mem_tetrad p i).mpr h,rfl⟩
  golay_iff := mem_atlas_golay_iff

private def partTransport (S : Sextet) : SextetPart standardSextet ≃ SextetPart S where
  toFun B := ⟨sextetConjugator S • B.val, by
    rw [← sextetConjugator_parts S]
    exact Finset.smul_mem_smul_finset B.property⟩
  invFun B := ⟨(sextetConjugator S)⁻¹ • B.val, by
    have h : (sextetConjugator S)⁻¹ • S.parts = standardSextet.parts := by
      rw [← sextetConjugator_parts S, inv_smul_smul]
    rw [← h]
    exact Finset.smul_mem_smul_finset B.property⟩
  left_inv B := by apply Subtype.ext; exact inv_smul_smul _ _
  right_inv B := by apply Subtype.ext; exact smul_inv_smul _ _

private lemma golay_smul_iff (g : M24) (v : Full) :
    v ∈ golay ↔ fullRepresentation g v ∈ golay := by
  constructor
  · exact golay_invariant g
  · intro h
    have hi := golay_invariant g⁻¹ h
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using hi

/-- Code-preserving coordinates for every native sextet, with the literal six-part bijection. -/
def nativeMarking (S : Sextet) : Marking S where
  pointEquiv := atlasPointEquiv.trans (sextetConjugator S).val
  partEquiv := standardMarking.partEquiv.trans (partTransport S)
  mem_part p i := by
    change sextetConjugator S • atlasPointEquiv p ∈
      sextetConjugator S • (standardMarking.partEquiv i).val ↔ p.1 = i
    rw [Finset.smul_mem_smul_finset_iff]
    exact standardMarking.mem_part p i
  golay_iff w := (mem_atlas_golay_iff w).trans (golay_smul_iff (sextetConjugator S) _)

/-- Conjugation transports the genuine standard stabilizer comparison. -/
def nativeStabilizerEquiv (S : Sextet) :
    Atlas.Codes.SextetStabilizer ≃* sextetStabilizer S :=
  SextetCore.sextetEquiv.symm.trans
    (MulAction.stabilizerEquivStabilizer (sextetConjugator_parts S).symm)

lemma standardStabilizer_coordinates (s : Atlas.Codes.SextetStabilizer) (p : Atlas.Codes.Omega) :
    (SextetCore.sextetEquiv.symm s).val.val (atlasPointEquiv p) = atlasPointEquiv (s.val.val p) := by
  have h := congrArg (fun x : Atlas.Codes.SextetStabilizer => x.val.val p)
    (SextetCore.sextetEquiv.apply_symm_apply s)
  rw [SextetCore.sextetEquiv_apply] at h
  exact (atlasPointEquiv.symm_apply_eq).mp h

lemma nativeStabilizer_coordinates (S : Sextet) (s : Atlas.Codes.SextetStabilizer)
    (p : Atlas.Codes.Omega) :
    (nativeStabilizerEquiv S s).val.val ((nativeMarking S).pointEquiv p) =
      (nativeMarking S).pointEquiv (s.val.val p) := by
  change (sextetConjugator S).val
    ((SextetCore.sextetEquiv.symm s).val.val
      ((sextetConjugator S).val.symm ((sextetConjugator S).val (atlasPointEquiv p)))) = _
  rw [Equiv.symm_apply_apply, standardStabilizer_coordinates]
  rfl

end
end MathieuCode.SextetLayers.CoordinateTransport
