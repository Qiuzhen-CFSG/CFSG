module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
public import Theory.Mathieu.M24.LocalGeometry.TrioNormalizerControl
public import Theory.Mathieu.M24.Properties.Order

/-!
# The cardinality of the native trio geometry

The literal Witt-design trios form a transitive M₂₄ action: the established
native transporter sends the standard partition to any trio, and the action
on its three octads preserves all the defining incidence data. The standard
stabilizer order and the order of M₂₄ therefore give exactly 3795 trios.
This is the finite-universe count used when checking the native far-orbit
certificate in the cycle-base argument.

Source: AS91 §§2–3; the transporter is the native Golay-code trio action, and
the standard stabilizer order is proved in `TrioNormalizerControl`.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native

open Sporadic.Mathieu
open Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open MathieuCode.TrioCalculation
open scoped Pointwise

/-- The literal point permutation action on the unordered octad partitions. -/
noncomputable def smulLine (g : M24) (l : Line) : Line where
  parts := g • l.parts
  card := by simpa only [Finset.card_smul_finset] using l.card
  octad := by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_smul_finset.mp hA
    have hg := (Sporadic.Mathieu.mem_M24_iff (g : Equiv.Perm (Fin 24))).mp g.property
    change g.val • B ∈ Sporadic.Mathieu.m24Blocks
    have hB' : B ∈ (Sporadic.Mathieu.m24Blocks : Set (Finset (Fin 24))) := l.octad B hB
    have hmem : g.val • B ∈ g.val • (Sporadic.Mathieu.m24Blocks : Set (Finset (Fin 24))) :=
      Set.mem_smul_set.mpr ⟨B, hB', rfl⟩
    rw [hg] at hmem
    exact hmem
  disjoint := by
    intro A hA B hB hne
    obtain ⟨A₀, hA₀, rfl⟩ := Finset.mem_smul_finset.mp hA
    obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_smul_finset.mp hB
    have hne₀ : A₀ ≠ B₀ := fun he => hne (congrArg (g • ·) he)
    have hdis := l.disjoint A₀ hA₀ B₀ hB₀ hne₀
    rw [Finset.disjoint_left] at hdis ⊢
    intro x hxA hxB
    obtain ⟨a, ha, hax⟩ := Finset.mem_smul_finset.mp hxA
    obtain ⟨b, hb, hbx⟩ := Finset.mem_smul_finset.mp hxB
    have hab : a = b := (MulAction.injective g) (hax.trans hbx.symm)
    exact hdis ha (hab ▸ hb)
  cover := by
    ext x
    constructor
    · intro _
      exact Finset.mem_univ x
    · intro _
      have hx₀ : g⁻¹ • x ∈ l.parts.biUnion id := by
        rw [l.cover]
        simp
      obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.mp hx₀
      apply Finset.mem_biUnion.mpr
      refine ⟨g • A, Finset.mem_smul_finset.mpr ⟨A, hA, rfl⟩, ?_⟩
      exact Finset.mem_smul_finset.mpr ⟨g⁻¹ • x, hxA, by simp⟩

noncomputable instance : MulAction M24 Line where
  smul := smulLine
  one_smul l := by
    apply line_parts_injective
    change (1 : M24) • l.parts = l.parts
    simp
  mul_smul g h l := by
    apply line_parts_injective
    change (g * h : M24) • l.parts = g • (h • l.parts)
    simp only [mul_smul]

noncomputable instance : Finite Line := Finite.of_injective Trio.parts line_parts_injective

/-- Every two native trios are related by an actual M₂₄ point permutation. -/
instance : MulAction.IsPretransitive M24 Line where
  exists_smul_eq := by
    intro l m
    obtain ⟨g, hg⟩ := exists_smul_standardTrio l
    obtain ⟨h, hh⟩ := exists_smul_standardTrio m
    refine ⟨h * g⁻¹, ?_⟩
    apply line_parts_injective
    change (h * g⁻¹) • l.parts = m.parts
    calc
      (h * g⁻¹) • l.parts = (h * g⁻¹) • (g • standardTrio.parts) := by rw [hg]
      _ = h • standardTrio.parts := by rw [mul_smul, inv_smul_smul]
      _ = m.parts := hh

/-- There are exactly 3795 unordered partitions of the 24 points into three
Witt octads. The exact order follows from the literal standard trio
stabilizer, not from a certificate table. -/
theorem line_card : Nat.card Line = 3795 := by
  have hstab : MulAction.stabilizer M24 standardTrio = trioStabilizer standardTrio := by
    ext g
    constructor
    · intro hg
      exact congrArg Trio.parts (show g • standardTrio = standardTrio from hg)
    · intro hg
      apply line_parts_injective
      change g • standardTrio.parts = standardTrio.parts
      exact hg
  have hidx := MulAction.index_stabilizer_of_transitive M24 standardTrio
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer M24 standardTrio)
  rw [hstab, Sporadic.Mathieu.M24LocalGeometry.TrioRecognition.standard_trio_card,
    Sporadic.Mathieu.m24_order] at hmul
  have hidx' : (trioStabilizer standardTrio).index = Nat.card Line := by
    rw [← hstab]
    exact hidx
  rw [hidx'] at hmul
  omega

end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native

end
