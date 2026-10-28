module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagRepresentation.Linear
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagRepresentation.Stabilizer
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagRepresentation.ChevalleyLine
public import Theory.AlgebraicGroup.Borel.Defs

/-!
# A Borel subgroup as an exact faithful flag stabilizer

For Borel, *Linear Algebraic Groups*, §11.1, take the Chevalley representation
with the prescribed line stabilizer and add the faithful coordinate-translation
representation. Restrict to the Borel and triangularize the quotient by that
line. Pulling back its flag retains the line, hence the exact stabilizer.

The representation is rational in the algebraic sense, with its regular morphism
witness explicitly exported. No connectedness of the ambient group is required.
Every flag stabilizer in a faithful representation is solvable by the companion
adapted-basis theorem `flagStabilizer_isSolvable`.
-/

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private theorem carrier_connected {G : Variety k} [AlgebraicGroup G]
    (B : ClosedSubgroup G) (hB : _root_.IsConnected (B : Set (Variety.Point G))) :
    Variety.IsConnected B.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph B.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point G // x ∈ (B : Set (Variety.Point G))} :=
    Subtype.connectedSpace hB
  let : ConnectedSpace (Variety.Point B.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

/-- Every prescribed Borel subgroup is the exact point stabilizer of a full
flag in a faithful finite-dimensional rational representation. Rationality is
proved explicitly, so this representation supplies a regular flag action. -/
public theorem exists_faithful_rationalRepresentation_exact_flagStabilizer
    {G : Variety k} [AlgebraicGroup G] (B : ClosedSubgroup G) (hB : IsBorelSubgroup B) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
      (ρ : RationalRepresentation G V),
      IsRationalRepresentation ρ ∧ Function.Injective ρ.action ∧
      ∃ F : FullFlag k V, ∀ g : Variety.Point G,
        (flagAction ρ).smul g F = F ↔ g ∈ B.toSubgroup := by
  obtain ⟨V, hVadd, hVmodule, hVfinite, ρ, hρrat, hρfaith, L, hLdim, hLstab⟩ :=
    exists_faithful_rationalRepresentation_exact_lineStabilizer B
  obtain ⟨σ, hσ, hσrat⟩ := rationalRepresentation_pullback_exists B.inclusion ρ hρrat
  have hLstable : IsInvariantSubmodule σ L := by
    intro b x hx
    rw [hσ b]
    exact (hLstab (B.inclusion.onPoints b)).mpr
      (B.pointEquiv b).property x hx
  obtain ⟨F, hFline, hFfixed⟩ := exists_invariant_fullFlag_extending_line
    σ hσrat hB.solvable (carrier_connected B hB.connected) L hLdim hLstable
  refine ⟨V, hVadd, hVmodule, hVfinite, ρ, hρrat, hρfaith, F, ?_⟩
  intro g
  constructor
  · intro hg
    apply (hLstab g).mp
    change F.map (ρ.action g).toLinearEquiv = F at hg
    have hinv := (FullFlag.map_eq_iff F _).mp hg 1
    simpa only [hFline, LinearMap.GeneralLinearGroup.coe_toLinearEquiv] using hinv
  · intro hg
    have hrange : g ∈ Set.range B.inclusion.onPoints := by
      rw [B.range_inclusion]
      exact hg
    obtain ⟨b, rfl⟩ := hrange
    have hfix := hFfixed b
    change F.map (σ.action b).toLinearEquiv = F at hfix
    change F.map (ρ.action (B.inclusion.onPoints b)).toLinearEquiv = F
    rwa [hσ b] at hfix

end Theory.AlgebraicGroup.BorelGeometricConjugacy
