module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.SourceInputs
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Coverage.Intransitive
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.KernelGeometry

/-!
# Sylow centralizers in quartic M₂₂ covers

For a finite perfect group with cyclic center of order four and the supplied
central quotient M₂₂, the centralizer of every Sylow two-subgroup lies in the
actual center. The quotient Sylow fixes a native hexad and contains its
pointwise kernel. Pulling that kernel back gives a subgroup of the original
Sylow. Native self-centralization puts a Sylow-centralizing element in this
pullback, and quartic recognition identifies its center with the ambient center.
All quotient maps and subgroup embeddings are the original ones.

Source: Aschbacher–Smith I.2.2(6), printed pp.410 and 412. This consequence
feeds the marked inner-action exclusion in 2.3.9(7), printed pp.525–526.
-/

public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
universe u
variable {K : Type u} [Group K] [Finite K] [Group.IsPerfect K]

/-- The Sylow centralizer in a supplied quartic M₂₂ cover is central. -/
theorem centralizer_sylow_le_center [IsCyclic (center K)]
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4)
    (P : Sylow 2 K) : centralizer (P : Set K) ≤ center K := by
  have hp : IsPGroup 2 (projection e).ker := by
    rw [projection_ker]
    exact IsPGroup.of_card (n := 2) (by simpa using hZ)
  obtain ⟨Q, hQ⟩ := P.exists_comap_eq_of_ker_isPGroup hp
  obtain ⟨B, hB, hQB⟩ := M22SolvableSylow.sylow_preserves_hexad Q
  have hRP : hexadRadical e B ≤ (P : Subgroup K) := by
    change (m22HexadPointwiseKernel B).comap (projection e) ≤ _
    rw [← hQ]
    exact Subgroup.comap_mono (M22SolvableSylow.kernel_le_of_sylow hB Q hQB)
  obtain ⟨d⟩ := exists_hexadRecognition_of_perfect e hZ hB
  intro x hx
  have himage : projection e x ∈
      centralizer (m22HexadPointwiseKernel B : Set M22) := by
    intro y hy
    obtain ⟨r, hr⟩ := projection_surjective e y
    have hrR : r ∈ hexadRadical e B := by
      change projection e r ∈ m22HexadPointwiseKernel B
      rwa [hr]
    simpa only [map_mul, hr] using congrArg (projection e) (hx r (hRP hrR))
  have hxR : x ∈ hexadRadical e B :=
    m22HexadPointwiseKernel_selfCentralizing hB himage
  have hxZ : (⟨x, hxR⟩ : hexadRadical e B) ∈ center (hexadRadical e B) := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact hx y (hRP y.property)
  rw [d.center_eq_ambient] at hxZ
  exact hxZ

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic
