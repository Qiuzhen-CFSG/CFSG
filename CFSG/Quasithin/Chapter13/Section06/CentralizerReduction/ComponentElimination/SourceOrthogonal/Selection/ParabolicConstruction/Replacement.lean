module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.Actions

/-!
# Movement of the source seed through the original plus quotient

If the original plus image of Lᵥ is contained in that of a replacement D,
then movement of z passes from Lᵥ to D. A lift differs from an element of
D by the original action kernel, which centralizes W_K and hence z.
No containment of Lᵥ in D is required.

The final consumer applies 13.6.16(3) and the genuine L₃(2) exclusion to
such a replacement. Its model uses D's own plus quotient on W_D, while
the containment transporting movement uses the original quotient on W_K.
Construction, local-family membership and star-quasisimplicity of D remain
obligations of the inner-action residual argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.6.23, printed p.933/PDF p.950.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction
open ComponentSelection
variable {G : Type*} [Group G]

/-- Movement transfers through the original action quotient; the subgroup
D need not contain Lᵥ before taking that quotient. -/
theorem replacement_moves_z (K D L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (himage : plusImage K L T z v hL hz (Lv L v) ≤ plusImage K L T z v hL hz D)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G)) :
    ¬ D ≤ centralizer ({z} : Set G) := by
  intro hD
  apply hmove
  intro x hx
  have hLa : Lv L v ≤ plusActor K L T v := le_sup_right.trans le_sup_left
  let a : plusActor K L T v := ⟨x, hLa hx⟩
  have ha : plusMk K L T z v hL hz a ∈ plusImage K L T z v hL hz (Lv L v) :=
    mem_map.mpr ⟨a, hx, rfl⟩
  obtain ⟨d, hd, he⟩ := mem_map.mp (himage ha)
  have hk : d⁻¹ * a ∈ (plusMk K L T z v hL hz).ker := by
    change plusMk K L T z v hL hz (d⁻¹ * a) = 1
    rw [map_mul, map_inv, he, inv_mul_cancel]
  rw [plusMk_ker] at hk
  have hzk : (d : G)⁻¹ * x ∈ centralizer ({z} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr
      (le_conjugateSpanBy (zpowers z) (Kminus K T v ⊔ Lv L v) (mem_zpowers z))) hk
  have hh := (centralizer ({z} : Set G)).mul_mem (hD hd) hzk
  simpa only [subtype_apply, mul_inv_cancel_left] using hh

/-- The actual residual criterion, distinguishing the old and replacement
plus quotients and deriving movement from image containment alone. -/
theorem false_of_rankThree_plus_replacement [Finite G]
    (K D L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (h16 : ∀ A ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (A : Set G) → ¬ A ≤ centralizer ({z} : Set G) →
      ⁅A, Stellmacher.elementaryAbelianMaxJ (Tv T v)⁆ = A)
    (hsmall : ∀ A ∈ Yz L T z v,
      ¬ Nonempty (plusImage A L T z v hL hz A ≃* SL(3, ZMod 2)))
    (hlocal : D ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hn : Tv T v ≤ normalizer (D : Set G))
    (hLN : Lv L v ≤ normalizer (D : Set G))
    (hq : Theory.GroupTheory.IsQuasisimple (starImage z v D ⧸ pCore 2 (starImage z v D)))
    (himage : plusImage K L T z v hL hz (Lv L v) ≤ plusImage K L T z v hL hz D)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    (e : plusImage D L T z v hL hz D ≃* SL(3, ZMod 2)) : False :=
  false_of_rankThree_source_replacement D L T z v hL hz h16 hsmall hlocal hn hLN hq
    (replacement_moves_z K D L T z v hL hz himage hmove) e

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction
