module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Defs
public import Theory.GroupTheory.TwoFixedLinesIrreducible
public import Theory.GroupTheory.IrreducibleNormalizerCore
public import Theory.GroupTheory.FixedLineSylowPromotion

/-!
# The normalizer deductions in Lemma 14.4.9

The two actual fixed lines C_D(U) = ⟨z⟩ and C_D(U^x) = ⟨i⟩ force
irreducibility on D = [U,i]⟨i,z⟩. The p-core fixed-point argument then gives
D ≤ Z(O₂(N_G(D))) and UD ∩ O₂(N_G(D)) = D. Finally, the fixed line of
T_D gives Sylow promotion from N_H(D) to N_G(D), with H = C_G(z).

These deductions are conditional on the preceding extraspecial lift and
centralizer calculations. They do not prove the choice of x, the order-64
lift, local Sylow maximality, or the terminal component/Appendix A sieve.
The full exclusion remains with the Orthogonal assembly owner.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G] [Finite G]

/-- The source symmetry forces irreducibility on the literal lift. -/
theorem lift_irreducible_of_symmetric_centralizers
    (U : Subgroup G) (z x : G) (hz : orderOf z = 2)
    (hU : IsPGroup 2 U)
    (hD : IsElementaryAbelian 2 (centralizerLift U z (conjugateElement z x)))
    (hCU : centralizerLift U z (conjugateElement z x) ⊓ centralizer (U : Set G) =
      zpowers z)
    (hCUx : centralizerLift U z (conjugateElement z x) ⊓
      centralizer (conjugateCore U x : Set G) = zpowers (conjugateElement z x)) :
    ∀ E : Subgroup G, E ≤ centralizerLift U z (conjugateElement z x) →
      symmetricActor U z x ≤ normalizer (E : Set G) →
      E = ⊥ ∨ E = centralizerLift U z (conjugateElement z x) := by
  let : IsElementaryAbelian 2 (centralizerLift U z (conjugateElement z x)) := hD
  have hi : orderOf (conjugateElement z x) = 2 := by
    simpa only [conjugateElement, MulEquiv.orderOf_eq] using hz
  exact commutator_join_irreducible_of_two_fixed_lines U (conjugateCore U x)
    (symmetricActor U z x) z (conjugateElement z x) hz hi hU
    (hU.map (MulAut.conj x⁻¹).toMonoidHom)
    (le_sup_right.trans le_sup_left) le_sup_right
    (IsElementaryAbelian.isPGroup 2 (centralizerLift U z (conjugateElement z x))) hCU hCUx

/-- The actual source lift is central in the normalizer's two-core, and
its self-centralization in UD identifies the required core intersection. -/
theorem lift_normalizer_core
    (U : Subgroup G) (z x : G) (hz : orderOf z = 2)
    (hU : IsPGroup 2 U)
    (hD : IsElementaryAbelian 2 (centralizerLift U z (conjugateElement z x)))
    (hY : symmetricActor U z x ≤
      normalizer (centralizerLift U z (conjugateElement z x) : Set G))
    (hCU : centralizerLift U z (conjugateElement z x) ⊓ centralizer (U : Set G) =
      zpowers z)
    (hCUx : centralizerLift U z (conjugateElement z x) ⊓
      centralizer (conjugateCore U x : Set G) = zpowers (conjugateElement z x))
    (hself : (U ⊔ centralizerLift U z (conjugateElement z x)) ⊓
      centralizer (centralizerLift U z (conjugateElement z x) : Set G) =
        centralizerLift U z (conjugateElement z x)) :
    let D := centralizerLift U z (conjugateElement z x)
    let N := normalizer (D : Set G)
    D ≤ N.pCoreIn 2 ∧ N.pCoreIn 2 ≤ centralizer (D : Set G) ∧
      (U ⊔ D) ⊓ N.pCoreIn 2 = D := by
  let D := centralizerLift U z (conjugateElement z x)
  let : IsElementaryAbelian 2 D := hD
  have hp : IsPGroup 2 D := IsElementaryAbelian.isPGroup 2 D
  have hirr := lift_irreducible_of_symmetric_centralizers U z x hz hU hD hCU hCUx
  exact ⟨le_pCoreIn_of_normalizes hp D.le_normalizer le_rfl,
    pCoreIn_le_centralizer_of_irreducible D (symmetricActor U z x) _ hp
      D.le_normalizer le_rfl hY hirr,
    inf_pCoreIn_normalizer_eq_of_irreducible D U (symmetricActor U z x) hp hY hirr hself⟩

/-- The fixed line of U is also the fixed line of T_D; local Sylow
maximality therefore promotes to the full normalizer of the actual lift. -/
theorem lift_normalizer_sylow
    (U : Subgroup G) (T : Sylow 2 G) (z i : G) (hz : orderOf z = 2)
    (hUT : U ≤ (T : Subgroup G))
    (hUD : U ≤ normalizer (centralizerLift U z i : Set G))
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hCU : centralizerLift U z i ⊓ centralizer (U : Set G) = zpowers z)
    (hlocal : ∃ P : Sylow 2
        (centralizer ({z} : Set G) ⊓ normalizer (centralizerLift U z i : Set G) : Subgroup G),
      (P : Subgroup (centralizer ({z} : Set G) ⊓
          normalizer (centralizerLift U z i : Set G) : Subgroup G)) =
        (localSylow (T : Subgroup G) (centralizerLift U z i)).subgroupOf
          (centralizer ({z} : Set G) ⊓ normalizer (centralizerLift U z i : Set G))) :
    ∃ P : Sylow 2 (normalizer (centralizerLift U z i : Set G)),
      (P : Subgroup (normalizer (centralizerLift U z i : Set G))) =
        (localSylow (T : Subgroup G) (centralizerLift U z i)).subgroupOf
          (normalizer (centralizerLift U z i : Set G)) := by
  let D := centralizerLift U z i
  let S := localSylow (T : Subgroup G) D
  have hUS : U ≤ S := le_inf hUT hUD
  have hfix : D ⊓ centralizer (S : Set G) = zpowers z := by
    apply le_antisymm
    · exact (inf_le_inf_left D (centralizer_le hUS)).trans (le_of_eq hCU)
    · refine le_inf (show zpowers z ≤ D from le_sup_right) (zpowers_le.mpr ?_)
      intro s hs
      exact mem_centralizer_singleton_iff.mp (hTz hs.1)
  obtain ⟨P, hP⟩ := hlocal
  have hindex := P.not_dvd_index
  rw [hP] at hindex
  exact exists_sylow_normalizer_of_fixed_line D S z hz
    (T.isPGroup'.to_le inf_le_left) inf_le_right hfix hindex

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
