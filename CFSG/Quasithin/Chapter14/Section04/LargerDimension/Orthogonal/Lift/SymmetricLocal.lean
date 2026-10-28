module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.Core
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.Symmetry
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.LocalSylow
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.Assembly

/-!
# Symmetric core identities and the local Sylow for the orthogonal lift

This interface connects the intrinsic core calculations, identification
of the exchanged lift, and Sylow pullback for the original T. The Assembly
module discharges the two quotient-core bounds, component interchange,
the exchanged moved section, and the quotient Sylow centralizer calculation
from the actual earlier case-(3) and selected-action inputs. It applies the
existing normalizer deductions with all symmetry/local premises proved.
The full exclusion in Lemma 14.4.9 remains with the parent source assembly,
which must also construct those earlier inputs and the terminal sieve.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G] [Finite G]

/-- Apply the existing normalizer promotion theorem to the quotient-derived
local witness. The Sylow appearing in the conclusion is the original T_D. -/
theorem lift_normalizer_sylow_from_quotient
    (U : Subgroup G) (T : Sylow 2 G) (z i : G) (hz : orderOf z = 2)
    (hUT : U ≤ (T : Subgroup G))
    (hUD : U ≤ normalizer (centralizerLift U z i : Set G))
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hiz : i ∈ centralizer ({z} : Set G))
    (hCU : centralizerLift U z i ⊓ centralizer (U : Set G) = zpowers z)
    (hpre : (normalizer (centralizerLift U z i : Set G)).subgroupOf
        (centralizer ({z} : Set G)) =
      (centralizer ({QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))) ⟨i,hiz⟩} :
        Set ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))).comap
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))
    (hbar : let H := centralizer ({z} : Set G)
      let q := QuotientGroup.mk' (pCore 2 H)
      let B := centralizer ({q ⟨i,hiz⟩} : Set (H ⧸ pCore 2 H))
      ∃ P : Sylow 2 B, (P : Subgroup B) =
        (((T : Subgroup G).subgroupOf H).map q).subgroupOf B) :
    ∃ P : Sylow 2 (normalizer (centralizerLift U z i : Set G)),
      (P : Subgroup (normalizer (centralizerLift U z i : Set G))) =
        (localSylow (T : Subgroup G) (centralizerLift U z i)).subgroupOf
          (normalizer (centralizerLift U z i : Set G)) := by
  exact lift_normalizer_sylow U T z i hz hUT hUD hTz hCU
    (lift_local_sylow_of_quotient T z i (centralizerLift U z i) hTz hiz hpre hbar)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
