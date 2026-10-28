module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.GroupDeductions

/-!
# The containing component commutes with the source I modulo its two-core

The action kernel on U is a proper normal subgroup of K_U. Quasisimplicity
makes it central modulo O₂(K_U); perfectness and the three-subgroups lemma
then give [K_U,C_G(U)] ≤ O₂(K_U). Apply this to the literal I ≤ C_G(U).
This is the commuting-section input of the four-space rank argument, with
normality relative to N_G(U), and does not assume an exact action kernel.

Source: Aschbacher–Smith, opening and penultimate paragraphs of the proof
of 8.2.8, printed pp.718–719 (PDF pp.735–736).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection
variable {G : Type*} [Group G] [Finite G]

/-- The source I centralizes the containing component modulo its actual
O₂(K_U), as required before the SQTK cubic-rank deduction. -/
theorem containingComponent_commutator (L K U I : Subgroup G)
    [Group.IsPerfect K] [Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K)]
    (hRK : localResidual L U ≤ K) (hKN : K ≤ normalizer (U : Set G))
    (hNK : normalizer (U : Set G) ≤ normalizer (K : Set G))
    (hnontriv : ¬ localResidual L U ≤ centralizer (U : Set G))
    (hIC : I ≤ centralizer (U : Set G)) : ⁅K, I⁆ ≤ K.pCoreIn 2 := by
  let C := (centralizer (U : Set G)).subgroupOf K
  have hNC : normalizer (U : Set G) ≤ normalizer (centralizer (U : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp inferInstance
  let : C.Normal := normal_subgroupOf_of_le_normalizer (hKN.trans hNC)
  have hproper : C ≠ ⊤ := by
    intro he
    apply hnontriv
    intro r hr
    exact (show (⟨r, hRK hr⟩ : K) ∈ C from he ▸ mem_top _)
  have hCm : C.map K.subtype = K ⊓ centralizer (U : Set G) := by
    rw [subgroupOf_map_subtype, inf_comm]
  have hker : ⁅K ⊓ centralizer (U : Set G), K⁆ ≤ K.pCoreIn 2 := by
    have hm := map_mono (f := K.subtype) (normal_kernel_commutator_le_twoCore C hproper)
    simpa only [map_commutator, hCm, ← MonoidHom.range_eq_map, range_subtype, pCoreIn] using hm
  exact (commutator_mono le_rfl hIC).trans (perfect_core_commutator K U hKN hNK hker)

end CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection
