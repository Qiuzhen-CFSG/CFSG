module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.SporadicNumerical
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.JankoTwo
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.MathieuCubic

/-!
# The literal sporadic Theorem C branch in the source sieve

The supplied model isomorphism connects every allowed sporadic carrier to its
proved source exclusion. The degree inequalities exclude M11, M23, J1, J4, HS,
He and Ru; the marked automorphism fixed-cubic arguments exclude M12, M22, M24
and J2. The Theorem C hypothesis explicitly removes J3.

Source: Aschbacher--Smith, A.2.4 and 15.3.58, printed pp.33 and 1149.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.Sporadic
open ChapterA.Section02
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

theorem exclude (h : SourceData ρ X T v s) (hK : ComponentData ρ K)
    (hsimple : IsSimpleGroup K) (hnonab : ¬ IsMulCommutative K)
    (hm : IsTheoremCSporadicModel K) : False := by
  rcases hm with hmodel | hmodel
  · obtain ⟨name, hname, ⟨e⟩⟩ := hmodel
    cases name with
    | m11 => exact h.not_m11_component hK e
    | m12 => exact h.not_m12_component hK e
    | m22 => exact h.not_m22_component hK e
    | m23 => exact h.not_m23_component hK e
    | m24 => exact h.not_m24_component hK e
    | j2 => exact h.not_j2_component hK e
    | j3 => exact hname rfl
    | j4 => exact h.not_j4_component hK hsimple hnonab e
    | hs => exact h.not_hs_component hK e
    | he => exact h.not_he_component hK e
    | ru => exact h.not_ru_component hK hsimple e
  · obtain ⟨e⟩ := hmodel
    exact h.not_j1_component hK e


end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.Sporadic
