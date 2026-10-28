module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.Model
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Coverage
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals
/-!
# Arbitrary markings of the incident parabolics

Compose the given automorphism with the common flag conjugation. The
inner-or-graph theorem expresses its two marked parabolics as a common
conjugate of the standard incident pair, allowing the graph automorphism
to exchange the point and line members. No innerness assumption is added.

Source: Meierfrankenfeld--Stellmacher (1993), proof of (1.7)(i), p.847;
the matrix automorphism coverage is provided by the PSL₃(2) theory.
-/

@[expose] public section
open Matrix Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms

private theorem marked_eq (σ : MulAut SL) (g : SL) (j : Bool) :
    markedParabolic σ g j =
      (if j then lineParabolicSL else pointParabolicSL).map (σ * MulAut.conj g).toMonoidHom := by
  rw [markedParabolic, modelParabolic, Subgroup.map_map]
  rfl

private theorem lineParabolic_map_diagram : lineParabolicSL.map diagram.toMonoidHom = pointParabolicSL := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply (diagram_point_line (diagram x)).mp
    rwa [diagram_involutive]
  · intro ha
    exact ⟨diagram a, (diagram_point_line a).mpr ha, diagram_involutive a⟩

private theorem map_aut_mul (P : Subgroup SL) (α β : MulAut SL) :
    P.map (α * β).toMonoidHom = (P.map β.toMonoidHom).map α.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem marked_pair (σ : MulAut SL) (g : SL) (i : Bool) :
    ∃ k : SL,
      (markedParabolic σ g i = pointParabolicSL.map (MulAut.conj k).toMonoidHom ∧
       markedParabolic σ g (!i) = lineParabolicSL.map (MulAut.conj k).toMonoidHom) ∨
      (markedParabolic σ g i = lineParabolicSL.map (MulAut.conj k).toMonoidHom ∧
       markedParabolic σ g (!i) = pointParabolicSL.map (MulAut.conj k).toMonoidHom) := by
  obtain ⟨k, hk|hk⟩ := inner_or_graph (σ * MulAut.conj g)
  · refine ⟨k, ?_⟩
    cases i
    · exact Or.inl ⟨by rw [marked_eq, hk]; rfl, by rw [marked_eq, hk]; rfl⟩
    · exact Or.inr ⟨by rw [marked_eq, hk]; rfl, by rw [marked_eq, hk]; rfl⟩
  · refine ⟨k, ?_⟩
    have hp : markedParabolic σ g false = lineParabolicSL.map (MulAut.conj k).toMonoidHom := by
      rw [marked_eq, hk, map_aut_mul]
      exact congrArg (fun P : Subgroup SL => P.map (MulAut.conj k).toMonoidHom) pointParabolic_map_diagram
    have hl : markedParabolic σ g true = pointParabolicSL.map (MulAut.conj k).toMonoidHom := by
      rw [marked_eq, hk, map_aut_mul]
      exact congrArg (fun P : Subgroup SL => P.map (MulAut.conj k).toMonoidHom) lineParabolic_map_diagram
    cases i
    · exact Or.inr ⟨hp, hl⟩
    · exact Or.inl ⟨hl, hp⟩
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof
