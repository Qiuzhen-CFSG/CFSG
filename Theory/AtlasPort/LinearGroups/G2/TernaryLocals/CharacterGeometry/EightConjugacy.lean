module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.EightConjugacy.Frames
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.EightConjugacy.NormCharacter
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.EightConjugacy.CayleyTable
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.EightConjugacy.NormalizedGenerators

/-!
# The two representatives for elementary eights in G₂(3)

An independent frame with one of the two reference multiplication tables
produces an actual multiplicative linear automorphism of the split octonions.
If its eight lines are homogeneous for an elementary eight `E`, conjugation
puts `E` in the self-centralizing reference eight. Equality follows from the
orders. Every conjugating map below is constructed from the two actual bases,
and its multiplicativity is verified on all basis pairs.

The norm character selects homogeneous generators of norms `1,1,±1`. Their
geometric orthogonality gives the full Cayley table and independence. Combining
these results proves that every elementary abelian subgroup of order eight is
conjugate to the old torus/Weyl eight or the all-norm-one Cayley eight, with no
additional geometric or conjugacy hypotheses.

Application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(4), printed pp.3–4 and 481–482. This discharges the eight branch
of the maximal-local cover; the line and four-group branches are separate. Source
§I.4 on p.417 does not itself supply that cover. The concrete algebra and
reference embeddings use the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

public section
namespace Atlas.G2.TernaryLocals.CharacterGeometry.EightConjugacy
open Atlas.SplitOctonion

/-- An independent eight-element frame is a basis of the actual octonions. -/
noncomputable def basisOfFrame (a b c : V)
    (hli : LinearIndependent (ZMod 3) (frame a b c)) : Module.Basis (Fin 8) (ZMod 3) V :=
  .mk hli (by rw [hli.span_eq_top_of_card_eq_finrank (by simp)])

@[simp] theorem basisOfFrame_apply (a b c : V)
    (hli : LinearIndependent (ZMod 3) (frame a b c)) (i : Fin 8) :
    basisOfFrame a b c hli i = frame a b c i := Module.Basis.mk_apply hli _ i

/-- The actual basis map from a reference frame to an independent Cayley frame. -/
noncomputable def frameMap (k : Bool) (a b c : V)
    (hli : LinearIndependent (ZMod 3) (frame a b c)) : V ≃ₗ[ZMod 3] V :=
  (referenceBasis k).equiv (basisOfFrame a b c hli) (Equiv.refl (Fin 8))

@[simp] theorem frameMap_apply (k : Bool) (a b c : V)
    (hli : LinearIndependent (ZMod 3) (frame a b c)) (i : Fin 8) :
    frameMap k a b c hli (referenceFrame k i) = frame a b c i := by
  rw [← referenceBasis_apply]
  exact (Module.Basis.equiv_apply _ i _ _).trans (basisOfFrame_apply a b c hli i)

/-- All 64 table equations certify that the basis map preserves multiplication. -/
theorem frameMap_mul (k : Bool) (a b c : V)
    (hli : LinearIndependent (ZMod 3) (frame a b c))
    (htable : ∀ i j, mul (frame a b c i) (frame a b c j) =
      coefficient (referenceNorm k) i j • frame a b c (CayleyEight.gradeSum i j))
    (x y : V) :
    frameMap k a b c hli (mul x y) = mul (frameMap k a b c hli x) (frameMap k a b c hli y) := by
  let f := frameMap k a b c hli
  have he : multiplication.compr₂ f.toLinearMap =
      multiplication.compl₁₂ f.toLinearMap f.toLinearMap := by
    apply (referenceBasis k).ext
    intro i
    apply (referenceBasis k).ext
    intro j
    change f (mul (referenceBasis k i) (referenceBasis k j)) =
      mul (f (referenceBasis k i)) (f (referenceBasis k j))
    simp only [referenceBasis_apply, reference_mul, map_smul, f, frameMap_apply, htable]
  exact congrArg (fun f : V →ₗ[ZMod 3] V →ₗ[ZMod 3] V => f x y) he

/-- An actual element of `G₂(3)`, certified by the full multiplication table. -/
noncomputable def automorphismOfTable (k : Bool) (a b c : V)
    (hli : LinearIndependent (ZMod 3) (frame a b c))
    (htable : ∀ i j, mul (frame a b c i) (frame a b c j) =
      coefficient (referenceNorm k) i j • frame a b c (CayleyEight.gradeSum i j)) : G :=
  ⟨frameMap k a b c hli, frameMap_mul k a b c hli htable⟩

@[simp] theorem automorphismOfTable_apply (k : Bool) (a b c : V)
    (hli : LinearIndependent (ZMod 3) (frame a b c))
    (htable : ∀ i j, mul (frame a b c i) (frame a b c j) =
      coefficient (referenceNorm k) i j • frame a b c (CayleyEight.gradeSum i j)) (i : Fin 8) :
    (automorphismOfTable k a b c hli htable).val (referenceFrame k i) = frame a b c i :=
  frameMap_apply k a b c hli i

/-- A homogeneous Cayley basis conjugates the whole elementary eight. -/
theorem conjugacy_of_homogeneous_frame (E : Subgroup G) (hE : Nat.card E = 8)
    (k : Bool) (a b c : V) (hli : LinearIndependent (ZMod 3) (frame a b c))
    (htable : ∀ i j, mul (frame a b c i) (frame a b c j) =
      coefficient (referenceNorm k) i j • frame a b c (CayleyEight.gradeSum i j))
    (hhom : ∀ i, ∃ χ : Character E, frame a b c i ∈ characterSpace E χ) :
    ∃ g : G, E = (representative k).map (MulAut.conj g).toMonoidHom := by
  let g := automorphismOfTable k a b c hli htable
  have hg (i : Fin 8) : g.val (referenceFrame k i) = frame a b c i :=
    automorphismOfTable_apply k a b c hli htable i
  refine ⟨g, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · intro e he
    let q : G := g⁻¹ * e * g
    have hs (i : Fin 8) : ∃ r : ZMod 3, q.val (referenceFrame k i) = r • referenceFrame k i := by
      obtain ⟨χ, hχ⟩ := hhom i
      refine ⟨(χ ⟨e, he⟩ : ZMod 3), ?_⟩
      have hh : e.val (g.val (referenceFrame k i)) =
          (χ ⟨e, he⟩ : ZMod 3) • g.val (referenceFrame k i) := by
        rw [hg]
        exact hχ ⟨e, he⟩
      change g.val.symm (e.val (g.val (referenceFrame k i))) = _
      rw [hh, map_smul, LinearEquiv.symm_apply_apply]
    have hq : q ∈ representative k := by
      rw [← centralizer_representative]
      intro t ht
      rw [representative_eq_range] at ht
      obtain ⟨p, rfl⟩ := ht
      apply Subtype.ext
      apply LinearEquiv.toLinearMap_injective
      apply (referenceBasis k).ext
      intro i
      rw [referenceBasis_apply]
      change (referenceEmbedding k p).val (q.val (referenceFrame k i)) =
        q.val ((referenceEmbedding k p).val (referenceFrame k i))
      obtain ⟨r, hr⟩ := hs i
      simp only [hr, map_smul, referenceEmbedding_frame, smul_smul]
      rw [mul_comm]
    refine Subgroup.mem_map.mpr ⟨q, hq, ?_⟩
    change g * (g⁻¹ * e * g) * g⁻¹ = e
    group
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_representative, hE]

/-- Exact two-representative conclusion, conditional on a homogeneous geometric
triple and the independent arbitrary-triple Cayley theorem. -/
theorem conjugacy_of_triple_and_cayley_theorem (E : Subgroup G) (hE : Nat.card E = 8)
    (htriple : ∃ (k : Bool) (a b c : V),
      IsCayleyTriple (referenceNorm k) a b c ∧
      ∀ i, ∃ χ : Character E, frame a b c i ∈ characterSpace E χ)
    (hcayley : ∀ (r : ZMod 3) (a b c : V), IsCayleyTriple r a b c →
      LinearIndependent (ZMod 3) (frame a b c) ∧
      ∀ i j, mul (frame a b c i) (frame a b c j) =
        coefficient r i j • frame a b c (CayleyEight.gradeSum i j)) :
    ∃ g : G, E = TernaryLocals.elementary.map (MulAut.conj g).toMonoidHom ∨
      E = CayleyEight.elementary.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨k, a, b, c, ht, hh⟩ := htriple
  obtain ⟨hli, htable⟩ := hcayley _ a b c ht
  obtain ⟨g, hg⟩ := conjugacy_of_homogeneous_frame E hE k a b c hli htable hh
  refine ⟨g, ?_⟩
  cases k
  · exact Or.inl hg
  · exact Or.inr hg

/-- Every elementary abelian subgroup of order eight in the actual ternary
octonion automorphism group is conjugate to one of the two embedded reference
eights. The conjugating automorphism comes from their full Cayley tables. -/
theorem elementary_eight_conjugacy (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) :
    ∃ g : G, E = TernaryLocals.elementary.map (MulAut.conj g).toMonoidHom ∨
      E = CayleyEight.elementary.map (MulAut.conj g).toMonoidHom :=
  conjugacy_of_triple_and_cayley_theorem E hE
    (exists_normalized_homogeneous_triple E hE) cayley_basis_and_table

end Atlas.G2.TernaryLocals.CharacterGeometry.EightConjugacy
