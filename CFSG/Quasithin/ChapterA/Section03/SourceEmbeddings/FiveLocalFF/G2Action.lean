module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import Theory.Representation.G2.NaturalScalarCubic
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Moving cubics on the natural G₂ module

Subnormality puts a local component's two-core inside the full Sylow.
After conjugating the local component to a literal short or long parabolic
residual, its nonzero fixed vector is moved by the corresponding cubic scalar.
Conjugating back retains the specified subgroup, actual two-core, and vector.
This is the G₂ natural-action step in Aschbacher–Smith 10.2.9, pp.751–752.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory Atlas.G2
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

omit [Finite F] in
private theorem conjugate_moving_cubic (B : Subgroup (Model F)) (g : Model F)
    (v : Natural.Space F)
    (h : ∃ y : Model F, orderOf y = 3 ∧
      y ∈ normalizer (B.map (MulAut.conj g).toMonoidHom : Set (Model F)) ∧
      (∀ b ∈ B.map (MulAut.conj g).toMonoidHom,
        ⁅y,b⁆ ∈ (B.map (MulAut.conj g).toMonoidHom).pCoreIn 2) ∧
      Natural.action F y (Natural.action F g v) ≠ Natural.action F g v) :
    ∃ x : Model F, orderOf x = 3 ∧ x ∈ normalizer (B : Set (Model F)) ∧
      (∀ b ∈ B, ⁅x,b⁆ ∈ B.pCoreIn 2) ∧ Natural.action F x v ≠ v := by
  obtain ⟨y, ho, hn, hc, hv⟩ := h
  let a := MulAut.conj g
  refine ⟨a.symm y, (orderOf_injective a.symm.toMonoidHom a.symm.injective y).trans ho,
    ?_, ?_, ?_⟩
  · apply (mem_map_iff_mem (f := a.toMonoidHom) a.injective).mp
    rw [map_normalizer_eq_of_bijective B a.bijective]
    change a (a.symm y) ∈ normalizer (B.map a.toMonoidHom : Set (Model F))
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
    have ht : Natural.action F (a (a.symm y)) (Natural.action F g v) = Natural.action F g (Natural.action F (a.symm y) v) := by
      simp [a, MulAut.conj_apply, map_mul, Module.End.mul_apply]
    simpa only [MulEquiv.apply_symm_apply, he] using ht

/-- Every nonzero natural vector fixed by the original full Sylow is moved
by a cubic element centralizing the local section modulo its actual two-core. -/
theorem g2_local_moving_cubic (hF : Nat.card F = 4)
    (S : Sylow 2 (Model F)) (B : Subgroup (Model F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (v : Natural.Space F) (hv : v ≠ 0)
    (hfix : ∀ s ∈ (S : Subgroup (Model F)), Natural.action F s v = v) :
    ∃ x : Model F, orderOf x = 3 ∧ x ∈ normalizer (B : Set (Model F)) ∧
      (∀ b ∈ B, ⁅x,b⁆ ∈ B.pCoreIn 2) ∧ Natural.action F x v ≠ v := by
  have hcore := local_core_le_sylow S B hB
  obtain ⟨g,hg⟩ := G2.local_placement (by rw [hF]; decide) S B hB hproper
  let a := MulAut.conj g
  have hzero : Natural.action F g v ≠ 0 := by
    intro he
    exact hv (by simpa using congrArg (Natural.action F g⁻¹) he)
  have hf : ∀ q ∈ (B.map a.toMonoidHom).pCoreIn 2, Natural.action F q (Natural.action F g v) = Natural.action F g v := by
    rw [← map_pCoreIn_of_injective 2 _ _ a.injective]
    rintro q ⟨r, hr, rfl⟩
    have he := hfix r (hcore hr)
    simpa [a, MulAut.conj_apply, map_mul, Module.End.mul_apply] using congrArg (Natural.action F g) he
  apply conjugate_moving_cubic B g v
  rcases hg with hp | hp
  · rw [hp] at hf ⊢
    exact NaturalScalarCubic.short_cubic_moves_fixed hF (Natural.action F g v) hzero hf
  · rw [hp] at hf ⊢
    exact NaturalScalarCubic.long_cubic_moves_fixed hF (Natural.action F g v) hzero hf


end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
