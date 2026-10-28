module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.Projection
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.Transport

/-! # Extracting sections from the five genuine SL₃ alternatives
Cases (1) and (2) use Q; case (3) uses Z(Q); case (4) constructs the
natural projection with kernel C_Q(L). Case (5) gives the central omega
clause directly. All unused dual and radical clauses remain in the input.
Source: C.1.34, pp.136–137, as used in the proof of 15.4.20, p.1164.
-/

@[expose] public section
open Subgroup Representation Stellmacher CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases

variable {D : Type*} [Group D]

/-- Normalizing a subgroup also normalizes its intrinsic center. -/
theorem normalizes_center (L Q : Subgroup D) (hn : L ≤ normalizer (Q : Set D)) :
    L ≤ normalizer ((center Q).map Q.subtype : Set D) := by
  have hc (l : L) (z : D) (hz : z ∈ (center Q).map Q.subtype) :
      (l : D) * z * (l : D)⁻¹ ∈ (center Q).map Q.subtype := by
    obtain ⟨z, hz, rfl⟩ := hz
    let e : MulAut Q := normalizerMonoidHom Q ⟨l, hn l.property⟩
    exact ⟨e z, (centerCongr e ⟨z, hz⟩).property, rfl⟩
  intro l hl
  apply mem_normalizer_iff.mpr
  intro z
  constructor
  · exact hc ⟨l, hl⟩ z
  · intro hz
    have hh := hc ⟨l⁻¹, L.inv_mem hl⟩ (l * z * l⁻¹) hz
    simpa only [inv_inv, ← mul_assoc, inv_mul_cancel, one_mul, mul_inv_cancel_right, inv_mul_cancel_right] using hh

/-- The source commutator and its center have the expected component action. -/
theorem sourceCenter_normalized (L : Subgroup D) : L ≤ normalizer (sourceCenter L : Set D) :=
  normalizes_center L (sourceQ L) (normalizer_commutator_ge_right _ _)

variable [Finite D]

/-- The five full source cases yield precisely the sections consumed by
the natural obstruction, or the central-omega clause consumed locally. -/
theorem Alternatives.sections_or_central {L R : Subgroup D} (hL : L.IsCComponent)
    (S : Sylow 2 D) {e : (L ⧸ pCore 2 L) ≃* Natural.Actor}
    (h : Alternatives (ZMod 2) 1 L R S e) :
    Nonempty (CoreCenterSection L 1) ∨ Nonempty (CoreCenterSection L 2) ∨
      omegaOneCenterAmbient (S : Subgroup D) ≤ center D := by
  have hCQ : sourceCenter L ≤ sourceQ L := map_subtype_le _
  cases h with
  | one _ m =>
    obtain ⟨m⟩ := m
    rw [naturalCopies_binary] at m
    exact Or.inl ⟨m.coreCenterSection hL hCQ bot_le⟩
  | two m _ =>
    obtain ⟨m⟩ := m
    rw [naturalCopies_binary] at m
    exact Or.inr (Or.inl ⟨m.coreCenterSection hL hCQ bot_le⟩)
  | three m _ _ =>
    obtain ⟨m⟩ := m
    rw [naturalCopies_binary] at m
    exact Or.inl ⟨m.coreCenterSection hL le_rfl bot_le⟩
  | four _ _ _ hCZ hUZ hs m _ _ _ _ =>
    obtain ⟨m⟩ := m
    let : IsMulCommutative (sourceCenter L) :=
      inferInstanceAs (IsMulCommutative ((center (sourceQ L)).map (sourceQ L).subtype))
    have hc : sourceFixed L ≤ centralizer (L : Set D) := inf_le_right
    let projection := m.projectDirectSum hUZ hCZ (sourceCenter_normalized L) hc hs
    rw [naturalCopies_binary] at projection
    exact Or.inl ⟨projection.coreCenterSection hL le_rfl hc⟩
  | five _ _ _ hc _ => exact Or.inr (Or.inr hc)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
