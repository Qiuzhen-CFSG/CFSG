module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import Theory.SpecificGroups.SymplecticFour.NaturalScalarCubic
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Moving cubics on the natural module of a symplectic local section

For a local C-component B at a full Sylow S, subnormality in B joined with S
puts the actual two-core of B inside S. A vector fixed by S is therefore
fixed by that core. Conjugate B to its literal point or plane residual;
the natural-coordinate scalar theorem gives a cubic normalizer element,
trivial on the two-core quotient and moving the transported nonzero vector.
Conjugating back preserves B, its actual two-core and the original vector.

This proves the natural-module movement step in Aschbacher–Smith 10.2.9,
printed pp.751–752. No identification of the natural module with the
parabolic radical, or faithfulness on an original unquotiented radical,
is made. The A₅ marking consumer derives field size four from the actual
local section before applying movement.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem local_core_le_sylow {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S) :
    B.pCoreIn 2 ≤ (S : Subgroup G) := by
  let J := B ⊔ (S : Subgroup G)
  have hsub : (B.subgroupOf J).IsSubnormal := hB.subnormal
  have hle : (B.subgroupOf J).pCoreIn 2 ≤ (S.subtype (show (S : Subgroup G) ≤ J from le_sup_right) : Subgroup J) :=
    (pCoreIn_le_of_subnormal 2 hsub).trans
      (pCore_isPGroup.le_sylow_of_normal (S.subtype (show (S : Subgroup G) ≤ J from le_sup_right)))
  rw [pCoreIn_subgroupOf 2 B J le_sup_left] at hle
  have hm := map_mono (f := J.subtype) hle
  rw [map_subgroupOf_eq_of_le ((B.pCoreIn_le 2).trans le_sup_left),
    Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] at hm
  exact hm

omit [Finite F] [CharP F 2] in
private theorem conjugate_moving_cubic (B : Subgroup (Sp F)) (g : Sp F)
    (v : Vector F)
    (h : ∃ y : Sp F, orderOf y = 3 ∧
      y ∈ normalizer (B.map (MulAut.conj g).toMonoidHom : Set (Sp F)) ∧
      (∀ b ∈ B.map (MulAut.conj g).toMonoidHom,
        ⁅y,b⁆ ∈ (B.map (MulAut.conj g).toMonoidHom).pCoreIn 2) ∧
      y • (g • v) ≠ g • v) :
    ∃ x : Sp F, orderOf x = 3 ∧ x ∈ normalizer (B : Set (Sp F)) ∧
      (∀ b ∈ B, ⁅x,b⁆ ∈ B.pCoreIn 2) ∧ x • v ≠ v := by
  obtain ⟨y, ho, hn, hc, hv⟩ := h
  let a := MulAut.conj g
  refine ⟨a.symm y, (orderOf_injective a.symm.toMonoidHom a.symm.injective y).trans ho,
    ?_, ?_, ?_⟩
  · apply (mem_map_iff_mem (f := a.toMonoidHom) a.injective).mp
    rw [map_normalizer_eq_of_bijective B a.bijective]
    change a (a.symm y) ∈ normalizer (B.map a.toMonoidHom : Set (Sp F))
    rw [a.apply_symm_apply]
    exact hn
  · intro b hb
    apply (mem_map_iff_mem (f := a.toMonoidHom) a.injective).mp
    rw [map_pCoreIn_of_injective 2 _ _ a.injective]
    change a ⁅a.symm y, b⁆ ∈ (B.map a.toMonoidHom).pCoreIn 2
    rw [map_commutatorElement, a.apply_symm_apply]
    exact hc (a b) (mem_map_of_mem a.toMonoidHom hb)
  · intro he
    apply hv
    have ht : a (a.symm y) • (g • v) = g • ((a.symm y) • v) := by
      simp [a, MulAut.conj_apply, mul_smul]
    simpa only [MulEquiv.apply_symm_apply, he] using ht

/-- Every nonzero natural vector fixed by the original full Sylow is moved
by a cubic element centralizing the local section modulo its actual two-core. -/
theorem symplectic_local_moving_cubic (hF : Nat.card F = 4)
    (S : Sylow 2 (Sp F)) (B : Subgroup (Sp F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (v : Vector F) (hv : v ≠ 0)
    (hfix : ∀ s ∈ (S : Subgroup (Sp F)), s • v = v) :
    ∃ x : Sp F, orderOf x = 3 ∧ x ∈ normalizer (B : Set (Sp F)) ∧
      (∀ b ∈ B, ⁅x,b⁆ ∈ B.pCoreIn 2) ∧ x • v ≠ v := by
  have hcore := local_core_le_sylow S B hB
  obtain ⟨g,hg⟩ := symplectic_local_placement (n := 2) hF (by decide) S B hB hproper
  let a := MulAut.conj g
  have hzero : g • v ≠ 0 := by
    intro he
    exact hv (by simpa using congrArg (g⁻¹ • ·) he)
  have hf : ∀ q ∈ (B.map a.toMonoidHom).pCoreIn 2, q • (g • v) = g • v := by
    rw [← map_pCoreIn_of_injective 2 _ _ a.injective]
    rintro q ⟨r, hr, rfl⟩
    have he := hfix r (hcore hr)
    simpa [a, MulAut.conj_apply, mul_smul] using congrArg (g • ·) he
  apply conjugate_moving_cubic B g v
  rcases hg with hp | hp
  · rw [hp] at hf ⊢
    exact NaturalScalarCubic.point_cubic_moves_fixed hF (g • v) hzero hf
  · rw [hp] at hf ⊢
    exact NaturalScalarCubic.plane_cubic_moves_fixed hF (g • v) hzero hf

/-- An actual A₅ two-core marking supplies the field-four parameter for the
natural-module cubic movement theorem. -/
theorem symplectic_five_section_moving_cubic {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Sp F)) (B : Subgroup (Sp F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (v : Vector F) (hv : v ≠ 0)
    (hfix : ∀ s ∈ (S : Subgroup (Sp F)), s • v = v) :
    ∃ x : Sp F, orderOf x = 3 ∧ x ∈ normalizer (B : Set (Sp F)) ∧
      (∀ b ∈ B, ⁅x,b⁆ ∈ B.pCoreIn 2) ∧ x • v ≠ v :=
  symplectic_local_moving_cubic
    (symplectic_five_section_placement hF hn S B hB hproper e).1 S B hB hproper v hv hfix

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
