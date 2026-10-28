module

public import Theory.GroupAction.TypedCosetAutomorphisms
public import Theory.GroupAction.InvariantFixedTree
public import Theory.SpecificGroups.Triality.TwoLocalCover
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage
public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.Actions

/-!
# Simultaneously invariant triality parabolics

For every nonidentity two-subgroup of the genuine binary triality carrier,
there is one conjugate full root parabolic containing its normalizer and
preserved by every automorphism stabilizing that same two-subgroup.

The actual inner--coefficient decomposition supplies a type-preserving
semilinear automorphism of the parabolic coset graph. Its fixed subtree has a
canonical colored center. Selecting that center simultaneously for all these
automorphisms proves invariance of the resulting vertex stabilizer. The
existing hexagon, odd apartment fixer and fixed-edge theorems discharge every
geometric premise. Simplicity and perfectness are inherited hypotheses of the
proved automorphism decomposition.

Source: the finite-building proof of Borel--Tits, GLS3 Theorem 3.1.3;
Aschbacher--Smith 2.4.25, printed p.543. The parabolics and automorphisms here
are those of the original triality carrier and its cubic coefficient field.
-/

@[expose] public section
noncomputable section

namespace Triality.Standard.TwoLocalGeometry
open Subgroup Parabolics OuterOdd GroupAction.EvenPolygon

/-- Every automorphism of the binary triality carrier acts semilinearly on its
actual parabolic incidence graph and preserves each vertex type. -/
theorem exists_semilinear_graphIso (f : ℕ) (hf : 0 < f)
    [IsSimpleGroup (BinaryCarrier f hf)] [Group.IsPerfect (BinaryCarrier f hf)]
    (a : MulAut (BinaryCarrier f hf)) :
    ∃ e : incidenceGraph f hf ≃g incidenceGraph f hf,
      (∀ g v, e (g • v) = a g • e v) ∧
      (∀ v, (e v).type = v.type) ∧
      ∀ v, vertexColor (e v) = vertexColor v := by
  obtain ⟨k, c, hform⟩ := Coverage.binary_inner_coefficient f hf a
  let e : incidenceGraph f hf ≃g incidenceGraph f hf :=
    CosetGeometry.innerAutomorphismGraphIso (parabolic (binaryParameters f hf))
      k (coefficientAction (binaryParameters f hf) c)
      (coefficient_parabolic (binaryParameters f hf) c)
  refine ⟨e, ?_, fun _ => rfl, fun _ => rfl⟩
  intro g v
  rw [hform]
  exact CosetGeometry.innerAutomorphismGraphIso_smul
    (parabolic (binaryParameters f hf)) k
    (coefficientAction (binaryParameters f hf) c)
    (coefficient_parabolic (binaryParameters f hf) c) g v

end Triality.Standard.TwoLocalGeometry

namespace Triality.Standard.TwoLocalCover
open Subgroup Parabolics TwoLocalGeometry GroupAction.EvenPolygon

/-- A single vertex contains the normalizer of the two-subgroup in its
stabilizer, and that stabilizer is invariant under every automorphism
preserving the original two-subgroup. -/
theorem invariant_normalizer_vertex (f : ℕ) (hf : 0 < f)
    [IsSimpleGroup (BinaryCarrier f hf)] [Group.IsPerfect (BinaryCarrier f hf)]
    (R : Subgroup (BinaryCarrier f hf)) (hR : R ≠ ⊥) (hRtwo : IsPGroup 2 R) :
    ∃ v : Vertex f hf,
      normalizer (R : Set (BinaryCarrier f hf)) ≤
        MulAction.stabilizer (BinaryCarrier f hf) v ∧
      ∀ a : MulAut (BinaryCarrier f hf), R.map a.toMonoidHom = R →
        (MulAction.stabilizer (BinaryCarrier f hf) v).map a.toMonoidHom =
          MulAction.stabilizer (BinaryCarrier f hf) v := by
  have hΓ := (hexagonGeometry f hf).toEvenPolygonAction
    (apartmentTranslates f hf) (standardApartment_fixer_odd f hf)
  have hT := fixed_graph_isTree hΓ R hR hRtwo (exists_fixed_edge f hf R hRtwo)
  obtain ⟨v, hv, hi⟩ := fixed_tree_invariant_stabilizer R hT
    hΓ.adjacent_color hΓ.smul_adj hΓ.smul_color
  refine ⟨v, hv, ?_⟩
  intro a ha
  apply hi a ha
  obtain ⟨e, he, _, hc⟩ := exists_semilinear_graphIso f hf a
  exact ⟨e, he, hc⟩

/-- The canonical fixed-tree vertex yields one actual conjugate parabolic
containing the normalizer and invariant under all automorphisms of the pair. -/
theorem invariant_normalizer_parabolic (f : ℕ) (hf : 0 < f)
    [IsSimpleGroup (BinaryCarrier f hf)] [Group.IsPerfect (BinaryCarrier f hf)]
    (R : Subgroup (BinaryCarrier f hf)) (hR : R ≠ ⊥) (hRtwo : IsPGroup 2 R) :
    ∃ (g : BinaryCarrier f hf) (i : Node),
      normalizer (R : Set (BinaryCarrier f hf)) ≤
        (parabolic (binaryParameters f hf) i).map (MulAut.conj g).toMonoidHom ∧
      ∀ a : MulAut (BinaryCarrier f hf), R.map a.toMonoidHom = R →
        ((parabolic (binaryParameters f hf) i).map (MulAut.conj g).toMonoidHom).map
          a.toMonoidHom =
            (parabolic (binaryParameters f hf) i).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨v, hv, hi⟩ := invariant_normalizer_vertex f hf R hR hRtwo
  obtain ⟨g, hg⟩ := CosetGeometry.exists_smul_base
    (parabolic (binaryParameters f hf)) v
  have hs : MulAction.stabilizer (BinaryCarrier f hf) v =
      (parabolic (binaryParameters f hf) v.type).map (MulAut.conj g).toMonoidHom := by
    calc
      _ = MulAction.stabilizer (BinaryCarrier f hf)
          (g • CosetGeometry.base (parabolic (binaryParameters f hf)) v.type) :=
        congrArg (MulAction.stabilizer (BinaryCarrier f hf)) hg.symm
      _ = _ := by rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
        CosetGeometry.stabilizer_base]
  refine ⟨g, v.type, hs ▸ hv, ?_⟩
  intro a ha
  simpa only [hs] using hi a ha

end Triality.Standard.TwoLocalCover
