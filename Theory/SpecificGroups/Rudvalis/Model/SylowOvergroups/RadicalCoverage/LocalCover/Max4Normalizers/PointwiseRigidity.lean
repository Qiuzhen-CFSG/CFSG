module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Refinement.Level1Step04
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Refinement.Level2Step10
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Rigidity.Level5

/-!
# Point-image and pointwise rigidity bounds for the marked-set stabilizer

Count neighbors in an invariant color cell in the certified Rudvalis orbital.
The finite rows, cells, and counts are checked by the kernel. These calculations
use the preserved ATLAS action (see `Model.PermutationData`), GLS3 Table 5.3r.
Witness generation: `Max4Normalizers/source/GenerateRefinement.py`.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.RefinementCertificate

open Rudvalis.OuterNormalizer Rudvalis.OuterNormalizer.RigidityCertificate
set_option maxRecDepth 30000
set_option Elab.async false

private theorem second_decode : ∀ x : Fin 4060,
    c1s4 x = c1s4 1 → x ∈ secondImages := by
  apply Rudvalis.Data.allFin
  decide +kernel

public theorem second_image (g : Model) (hg : g ∈ pointSetStabilizer)
    (hg0 : g • (0 : Fin 4060) = 0) : g • (1 : Fin 4060) ∈ secondImages := by
  apply second_decode
  apply c1s4_preserved g hg
  intro x hx
  have he : x = 0 := Fin.ext (by omega)
  subst x
  exact hg0

private theorem base_decode : ∀ x : Fin 4060,
    (c2s10 x = c2s10 2 → x = 2) ∧
    (c2s10 x = c2s10 3 → x = 3) ∧
    (c2s10 x = c2s10 4 → x = 4) := by
  apply Rudvalis.Data.allFin
  decide +kernel

public theorem fix_two_eq_one (g : Model) (hg : g ∈ pointSetStabilizer)
    (hg0 : g • (0 : Fin 4060) = 0) (hg1 : g • (1 : Fin 4060) = 1) : g = 1 := by
  have hf : ∀ x : Fin 4060, x.val < 2 → g • x = x := by
    intro x hx
    have he : x = 0 ∨ x = 1 := by
      have : x.val = 0 ∨ x.val = 1 := by omega
      simpa only [Fin.ext_iff,
        show (0 : Fin 4060).val = 0 from rfl,
        show (1 : Fin 4060).val = 1 from rfl,
        show (2 : Fin 4060).val = 2 from rfl,
        show (3 : Fin 4060).val = 3 from rfl,
        show (4 : Fin 4060).val = 4 from rfl] using this
    rcases he with rfl | rfl
    · exact hg0
    · exact hg1
  have hi := c2s10_preserved g hg hf
  have h2 := (base_decode (g • 2)).1 (hi 2)
  have h3 := (base_decode (g • 3)).2.1 (hi 3)
  have h4 := (base_decode (g • 4)).2.2 (hi 4)
  apply Subtype.ext
  apply fix_five_eq_one g.val (model_relation g)
  intro x hx
  have he : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
    have : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 ∨ x.val = 3 ∨ x.val = 4 := by omega
    simpa only [Fin.ext_iff,
        show (0 : Fin 4060).val = 0 from rfl,
        show (1 : Fin 4060).val = 1 from rfl,
        show (2 : Fin 4060).val = 2 from rfl,
        show (3 : Fin 4060).val = 3 from rfl,
        show (4 : Fin 4060).val = 4 from rfl] using this
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact hg0
  · exact hg1
  · exact h2
  · exact h3
  · exact h4

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.RefinementCertificate
