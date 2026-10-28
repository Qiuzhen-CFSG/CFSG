module

public import Theory.Mathieu.M12.ValueBoundParabolics.CentralCovers.LocalAction
public import Theory.Mathieu.M24.ValueBoundParabolics.CentralCover.ThreeTransfer
public import Theory.GroupTheory.CentralExtensionPartialInversion
import all Theory.Mathieu.M12.Properties.Sylow3
import all Theory.Mathieu.M11.Properties.Sylow3

/-!
# Three-primary kernels over M₁₁ and M₁₂

The actual M₁₁ Sylow nine-group has an ambient element fixing one generator
and inverting the other. The M₁₂ Heisenberg Sylow has a simultaneous inverter.
Apply the corresponding proved central-extension and transfer lemmas to these
marked configurations. No tabulated multiplier is used.

Source: Aschbacher–Smith I.1.1–I.1.3, printed p.407; the M₁₂ consequence is
also used in A.2.19 and E.4.3(1). Internal imports give access to the already
certified coordinates without changing the model modules' public boundaries.
-/

open Subgroup
open scoped commutatorElement
namespace Sporadic.Mathieu.SchurMultipliers
open M12SmallPair.ValueBoundParabolics.CentralCovers

private abbrev X : M12Heisenberg := ⟨1, 0, 0⟩
private abbrev Y : M12Heisenberg := ⟨0, 1, 0⟩
private theorem heisenberg_generate : closure ({X, Y} : Set M12Heisenberg) = ⊤ := by
  apply top_unique
  intro a _
  have hx : X ∈ closure ({X, Y} : Set M12Heisenberg) := subset_closure (by simp)
  have hy : Y ∈ closure ({X, Y} : Set M12Heisenberg) := subset_closure (by simp)
  have hc : ⁅X, Y⁆ ∈ closure ({X, Y} : Set M12Heisenberg) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hn : X ^ a.i.val * Y ^ a.j.val * ⁅X, Y⁆ ^ a.k.val = a := by
    rcases a with ⟨i,j,k⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel
  rw [← hn]
  exact mul_mem (mul_mem (pow_mem hx _) (pow_mem hy _)) (pow_mem hc _)

private noncomputable def m12InvertedSylow : PerfectCentralCovering.InvertedHeisenbergSylowThree M12 where
  sylow := m12Sylow3
  a := m12HeisenbergHom X
  b := m12HeisenbergHom Y
  inverter := sylowThreeInverter
  generate := by
    have h := congrArg (Subgroup.map m12HeisenbergHom) heisenberg_generate
    simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      ← MonoidHom.range_eq_map, m12Sylow3_coe, m12Sylow3Subgroup] using h
  a_cube := by rw [← map_pow, m12Heisenberg_cube_eq_one, map_one]
  b_cube := by rw [← map_pow, m12Heisenberg_cube_eq_one, map_one]
  commutator_a := by
    rw [← map_commutatorElement]
    exact (show Commute ⁅X, Y⁆ X by rfl).map m12HeisenbergHom
  commutator_b := by
    rw [← map_commutatorElement]
    exact (show Commute ⁅X, Y⁆ Y by rfl).map m12HeisenbergHom
  commutator_ne_one := by
    rw [← map_commutatorElement, ← map_one m12HeisenbergHom]
    exact fun h => (by decide +kernel : ⁅X, Y⁆ ≠ 1) (m12HeisenbergHom_injective h)
  inverter_sq := sylowThreeInverter_sq
  conjugate_a := by
    rw [sylowThreeInverter_conj, ← map_inv]
    rfl
  conjugate_b := by
    rw [sylowThreeInverter_conj, ← map_inv]
    rfl

/-- Three is excluded from every finite perfect central kernel over actual M₁₂. -/
public theorem m12_cover_kernel_not_three {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E M12) : ¬ 3 ∣ Nat.card f.toMonoidHom.ker :=
  PerfectCentralCovering.not_three_dvd_kernel_of_invertedHeisenbergSylow f m12InvertedSylow

private abbrev X11 : M11E9 := Multiplicative.ofAdd (0,1)
private abbrev Y11 : M11E9 := Multiplicative.ofAdd (1,0)
private theorem e9_generate : closure ({X11, Y11} : Set M11E9) = ⊤ := by
  apply top_unique
  intro a _
  have hx : X11 ∈ closure ({X11, Y11} : Set M11E9) := subset_closure (by simp)
  have hy : Y11 ∈ closure ({X11, Y11} : Set M11E9) := subset_closure (by simp)
  have hn : X11 ^ a.toAdd.2.val * Y11 ^ a.toAdd.1.val = a := by
    rcases a with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> rfl
  rw [← hn]
  exact mul_mem (pow_mem hx _) (pow_mem hy _)

/-- The marked partial inverter of E₉ excludes three from an M₁₁ cover kernel. -/
public theorem m11_cover_kernel_not_three {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : PerfectCentralCovering.Cover E M11) : ¬ 3 ∣ Nat.card f.toMonoidHom.ker := by
  apply CentralExtension.not_dvd_card_kernel_of_partial_inversion
    f.toMonoidHom f.surjective f.ker_le_center m11Sylow3
    (m11E9Hom X11) (m11E9Hom Y11) m11GeneratorAInM11
  · have h := congrArg (Subgroup.map m11E9Hom) e9_generate
    simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      ← MonoidHom.range_eq_map, m11Sylow3_coe, m11Sylow3Subgroup] using h
  · exact (by decide : Nat.Coprime 3 2)
  · rw [← map_pow]
    exact (congrArg m11E9Hom (by decide +kernel : X11 ^ 3 = 1)).trans (map_one _)
  · exact (Commute.all X11 Y11).map m11E9Hom
  · change m11GeneratorAInM11 * m11E9Eval X11 * m11GeneratorAInM11⁻¹ = _
    rw [m11Sylow3GeneratorA_conj]
    exact (congrArg m11E9Hom (by decide +kernel : m11Sylow3AAct X11 = X11⁻¹)).trans
      (map_inv _ _)
  · have h := m11Sylow3GeneratorA_conj Y11
    change m11GeneratorAInM11 * m11E9Hom Y11 * m11GeneratorAInM11⁻¹ = _ at h
    have hy : m11Sylow3AAct Y11 = Y11 := by decide +kernel
    rw [hy] at h
    exact mul_inv_eq_iff_eq_mul.mp h
end Sporadic.Mathieu.SchurMultipliers
