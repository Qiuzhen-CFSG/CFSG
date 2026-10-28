module

public import ABG.ChapterII.Section1.FusionFrame
public import ABG.ChapterII.Section2.QuasiQDCharacterization
public import ABG.ChapterII.Section2.QuasiInvolutionCentralizer

/-!
# Q-group structure of the semidihedral involution centralizers

A finite group with a semidihedral Sylow two-subgroup and no normal
subgroup of index two has the full QD fusion pattern of ABG II.1.
ABG II.2 then makes the centralizer of every actual involution a Q-group,
retaining the original full Sylow fusion witness.

The frame-existence theorem chooses the four and quaternion subgroups
inside the specified Sylow subgroup. The proved QD characterization
excludes the index-two and normal-complement alternatives without losing
the automizer clauses. Applying the involution-centralizer theorem to
that same frame supplies the input to the characteristic-three GL₂(3)
recognition in the semidihedral branch of Aschbacher–Smith I.4.3.

Source: Alperin–Brauer–Gorenstein, Chapter II, §1 Proposition 1 and §2
Proposition 1, article pp.10–15; Aschbacher–Smith, *The Classification of
Quasithin Groups*, I.4.3, printed pp.416–417.
-/

namespace CFSG.Quasithin.ChapterI.SmallSylow
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The specified semidihedral Sylow subgroup admits a complete QD frame
under the original no-index-two hypothesis. -/
public theorem semidihedral_qd_pattern
    (T : Sylow 2 G) (hT : Stellmacher.IsSemidihedralGroup T)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) :
    ∃ E Q : Subgroup G,
      ABG.QuasiDihedralFusionFrame T E Q ∧ ABG.QuasiDihedralQDPattern E Q := by
  obtain ⟨E, Q, hf⟩ := ABG.exists_quasiDihedralFusionFrame T hT
  exact ⟨E, Q, hf,
    (ABG.quasiDihedral_qdPattern_iff_no_normal_index_two T E Q hf).mpr hno⟩

/-- The full QD-group hypothesis needed by the local ABG recognition route. -/
public theorem semidihedral_isQDGroup
    (T : Sylow 2 G) (hT : Stellmacher.IsSemidihedralGroup T)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) : ABG.IsQDGroup G := by
  obtain ⟨E, Q, hf, hQD⟩ := semidihedral_qd_pattern T hT hno
  exact Or.inl ⟨T, E, Q, hf, hQD⟩

/-- Every actual involution centralizer has the original full-Sylow
Q-group structure, with no simplicity or even-characteristic premise. -/
public theorem semidihedral_involutionCentralizer_isFullSylowQGroup
    (T : Sylow 2 G) (hT : Stellmacher.IsSemidihedralGroup T)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (x : G) (hx : orderOf x = 2) :
    ABG.IsFullSylowQGroup (centralizer ({x} : Set G)) := by
  obtain ⟨E, Q, hf, hQD⟩ := semidihedral_qd_pattern T hT hno
  exact ABG.quasiQD_involutionCentralizer_isFullSylowQGroup T E Q hf hQD x hx

/-- The literal involution-centralizer input to the characteristic-three
Q-group model theorem used in I.4.3. -/
public theorem semidihedral_involutionCentralizer_isQGroup
    (T : Sylow 2 G) (hT : Stellmacher.IsSemidihedralGroup T)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (x : G) (hx : orderOf x = 2) :
    ABG.IsQGroup (centralizer ({x} : Set G)) :=
  Or.inl (semidihedral_involutionCentralizer_isFullSylowQGroup T hT hno x hx)

end CFSG.Quasithin.ChapterI.SmallSylow
