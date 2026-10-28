module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Centralizers
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Normalizer
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Assembly

/-!
# Constructing the orthogonal centralizer lift

The exported `lift_of_selected_configuration` constructs D=[U,i]⟨i,z⟩
of order 64, its order-32 base, the chief modules and full transvection
action, both core identities, the symmetric centralizers and the original
local Sylow witness. It applies the existing normalizer deductions, deriving
irreducibility, the normalizer-core intersection and global Sylow promotion.
Its input is the earlier selected configuration with the literal moved module
and centralizer-modulo-line comparison. The theorem below preserves the older
conditional application with separate symmetry and local Sylow premises.

The source selection and terminal component exclusion remain with the parent
Orthogonal assembly; this module completes their intervening lift calculation.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G] [Finite G]

/-- Assemble the checked lift with the normalizer deductions. The conjugate fixed line,
conjugate-core normalization and local Sylow witness remain explicit source-
symmetry inputs. The elementary lift and both centralizer calculations on
the original side are proved here from the moved section. -/
theorem lift_normalizer_consequences_of_moved_section
    (U : Subgroup G) [IsExtraspecial 2 U] (T : Sylow 2 G) (z x : G)
    (hz : orderOf z = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : conjugateElement z x ∈ normalizer (U : Set G))
    (hiz : conjugateElement z x ∈ centralizer ({z} : Set G))
    (hout : conjugateElement z x ∉ U)
    (hUcard : Nat.card U = 512)
    (hKU : diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x) ≤
      normalizer (U : Set G))
    (hmoved : Nat.card (((⁅U,zpowers (conjugateElement z x)⁆).subgroupOf U).map
      (QuotientGroup.mk' (center U))) = 16)
    (hirr : ∀ E : Subgroup G, zpowers z ≤ E → E ≤ liftBase U z (conjugateElement z x) →
      diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x) ≤
        normalizer (E : Set G) → E = zpowers z ∨ E = liftBase U z (conjugateElement z x))
    (hCUx : centralizerLift U z (conjugateElement z x) ⊓
      centralizer (conjugateCore U x : Set G) = zpowers (conjugateElement z x))
    (hUxD : conjugateCore U x ≤ normalizer (centralizerLift U z (conjugateElement z x) : Set G))
    (hUT : U ≤ (T : Subgroup G))
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hlocal : ∃ P : Sylow 2 (centralizer ({z} : Set G) ⊓
        normalizer (centralizerLift U z (conjugateElement z x) : Set G) : Subgroup G),
      (P : Subgroup (centralizer ({z} : Set G) ⊓
        normalizer (centralizerLift U z (conjugateElement z x) : Set G) : Subgroup G)) =
      (localSylow (T : Subgroup G) (centralizerLift U z (conjugateElement z x))).subgroupOf
        (centralizer ({z} : Set G) ⊓
          normalizer (centralizerLift U z (conjugateElement z x) : Set G))) :
    let D := centralizerLift U z (conjugateElement z x)
    let N := normalizer (D : Set G)
    IsElementaryAbelian 2 D ∧ Nat.card D = 64 ∧
      D ≤ N.pCoreIn 2 ∧ N.pCoreIn 2 ≤ centralizer (D : Set G) ∧
      (U ⊔ D) ⊓ N.pCoreIn 2 = D ∧
      ∃ P : Sylow 2 N, (P : Subgroup N) = (localSylow (T : Subgroup G) D).subgroupOf N := by
  let i := conjugateElement z x
  let K := diagonalResidual (centralizer ({z} : Set G)) i
  have hKi : K ≤ centralizer ({i} : Set G) :=
    (map_subtype_le (pResidual 2 (centralizer ({z} : Set G) ⊓
      centralizer ({i} : Set G) : Subgroup G))).trans inf_le_right
  have hi : orderOf i = 2 := by
    simpa only [i, conjugateElement, MulEquiv.orderOf_eq] using hz
  obtain ⟨hD,hDcard,hA,hAcard⟩ := centralizerLift_elementary_and_card U K z i hz hi
    hZ hiU hiz hout hKU hKi hmoved hirr
  have hCU := centralizerLift_fixed_line U z i hz hi hZ hiU hD hAcard
  have hnorm := lift_normalized_by_residual_join_core U K z i hZ hiU hKU hKi hmoved
  have hY : symmetricActor U z x ≤ normalizer (centralizerLift U z i : Set G) :=
    sup_le hnorm hUxD
  have hself := centralizerLift_self_centralizer U z i hZ hiU hUcard hD hA hAcard
  obtain ⟨hDN,hND,hinter⟩ := lift_normalizer_core U z x hz
    (IsExtraspecial.isPGroup 2 U) hD hY hCU hCUx hself
  exact ⟨hD,hDcard,hDN,hND,hinter,lift_normalizer_sylow U T z i hz hUT
    (le_sup_right.trans hnorm) hTz hCU hlocal⟩


end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
