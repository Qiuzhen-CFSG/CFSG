module

public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupAction.SylowFixedElementaryDisplacement
public import Theory.ElementaryAbelian.Join
public import Stellmacher.OmegaOneCenterMap

/-!
# Central elementary Sylow subgroups acting on blocks

Let K be finite with F*(K) = O₂(K), Q a Sylow two-subgroup, and L an actual
short subnormal subgroup of K. Every elementary abelian V contained in Z(Q)
normalizes L and acts on it by elements of Ω₁(Z(L ∩ Q)). The conclusion holds
for all blocks; the SQTK and chi-zero restrictions in the E.6.7 application
are unnecessary for this step.

Self-centralization of F*(K) puts C_K(Q) inside O₂(K). Subnormal two-perfection
then gives both normalization of L and [O₂(K),L] ≤ U(L). The image U of U(L)
lies in L ∩ Q, so A = UV is elementary abelian and normalized by L. Each
v in V is fixed by the Sylow subgroup L ∩ Q. Multiplying its odd conjugacy
orbit inside A gives an element b centralizing L and congruent to v modulo U.
Thus z = v / b lies in U, squares to one, centralizes L ∩ Q, and has the
same literal conjugation on L as v.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the action
step in the proof of E.6.7, printed p.246. This proof establishes passage to
short blocks directly, without assuming C.1.9, C.1.13, or the action conclusion
and without applying quasisimple Lemma 16.1.6 (printed p.1172) to L.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.ChapterE.Section06

variable {K : Type*} [Group K] [Finite K]

/-- In characteristic two, the whole centralizer of a Sylow two-subgroup lies in the two-core. -/
theorem central_sylow_le_core (hK : generalizedFitting K = pCore 2 K)
    (Q : Sylow 2 K) : centralizer (Q : Set K) ≤ pCore 2 K := by
  have hc : centralizer (pCore 2 K : Set K) ≤ pCore 2 K := by
    simpa only [hK] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := K))
  exact (centralizer_le (pCore_isPGroup.le_sylow_of_normal Q)).trans hc

/-- Centralizing the ambient Sylow subgroup forces normalization of each short subnormal subgroup. -/
theorem central_sylow_normalizes_block (hK : generalizedFitting K = pCore 2 K)
    (Q : Sylow 2 K) (L : Subgroup K) (hL : ChapterC.IsBlock L) :
    centralizer (Q : Set K) ≤ normalizer (L : Set K) := by
  apply (central_sylow_le_core hK Q).trans
  exact le_normalizer_of_isSubnormal_isPPerfect L (pCore 2 K)
    hL.subnormal hL.short.twoPerfect pCore_isPGroup (by rw [normalizer_eq_top]; exact le_top)

/-- The external action displaces a block only inside its elementary commutator layer. -/
theorem central_sylow_block_commutator (hK : generalizedFitting K = pCore 2 K)
    (Q : Sylow 2 K) (L : Subgroup K) (hL : ChapterC.IsBlock L) :
    ⁅centralizer (Q : Set K), L⁆ ≤ (ChapterC.blockU L).map L.subtype := by
  exact (commutator_mono (central_sylow_le_core hK Q) le_rfl).trans
    (commutator_le_core_commutator_of_isSubnormal L (pCore 2 K)
      hL.subnormal hL.short.twoPerfect pCore_isPGroup
      (by rw [normalizer_eq_top]; exact le_top))

/-- The E.6.7 action step, valid for every actual block: each element of V
acts by an actual element of Ω₁(Z(L ∩ Q)), with literal conjugation equality. -/
theorem central_elementary_sylow_block_action
    (hK : generalizedFitting K = pCore 2 K) (Q : Sylow 2 K)
    (L : Subgroup K) (hL : ChapterC.IsBlock L)
    (V : Subgroup K) [IsElementaryAbelian 2 V]
    (hV : V ≤ (Q : Subgroup K) ⊓ centralizer (Q : Set K)) :
    V ≤ normalizer (L : Set K) ∧
      ∀ v ∈ V, ∃ z ∈ Stellmacher.omegaOneCenterAmbient (L ⊓ Q),
        ∀ l ∈ L, z * l * z⁻¹ = v * l * v⁻¹ := by
  let U := (ChapterC.blockU L).map L.subtype
  let : IsElementaryAbelian 2 (ChapterC.blockU L) := hL.short.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map L.subtype
  obtain ⟨S, hS⟩ := Q.exists_subgroupOf_eq_of_subnormal L hL.subnormal
  have hUQ : U ≤ Q := by
    rintro x ⟨u, hu, rfl⟩
    have hh := (IsElementaryAbelian.isPGroup 2 (ChapterC.blockU L)).le_sylow_of_normal S hu
    change u ∈ (S : Subgroup L) at hh
    rwa [hS] at hh
  have hVU : V ≤ centralizer (U : Set K) :=
    (hV.trans inf_le_right).trans (centralizer_le hUQ)
  let A := U ⊔ V
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.sup_of_le_centralizer hVU
  have hLU : L ≤ normalizer (U : Set K) := by
    apply le_normalizer_iff.mpr
    rintro l hl u ⟨uL, huL, rfl⟩
    exact ⟨⟨l, hl⟩ * uL * ⟨l, hl⟩⁻¹,
      (ChapterC.blockU_normal L).conj_mem uL huL ⟨l, hl⟩, rfl⟩
  have hc : ⁅V, L⁆ ≤ U :=
    (commutator_mono (hV.trans inf_le_right) le_rfl).trans
      (central_sylow_block_commutator hK Q L hL)
  have hLA : L ≤ normalizer (A : Set K) := by
    apply le_normalizer_iff.mpr
    intro l hl a ha
    have hm : A.map (MulAut.conj l).toMonoidHom ≤ A := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨u, hu, rfl⟩
        exact (show U ≤ A from le_sup_left) ((hLU hl u).mp hu)
      · rintro _ ⟨v, hv, rfl⟩
        have hh : ⁅l, v⁆ ∈ U := by
          rw [commutator_comm] at hc
          exact hc (commutator_mem_commutator hl hv)
        have := A.mul_mem ((show U ≤ A from le_sup_left) hh) ((show V ≤ A from le_sup_right) hv)
        change l * v * l⁻¹ ∈ A
        simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using this
    exact hm ⟨a, ha, rfl⟩
  refine ⟨(hV.trans inf_le_right).trans (central_sylow_normalizes_block hK Q L hL), ?_⟩
  intro v hv
  have hvfix (s : L) (hs : s ∈ S) : (s : K) * v * (s : K)⁻¹ = v := by
    have hsQ : (s : K) ∈ Q := by
      change s ∈ (S : Subgroup L) at hs
      rwa [hS] at hs
    rw [mem_centralizer_iff.mp (hV hv).2 s hsQ, mul_inv_cancel_right]
  obtain ⟨z, hzU, hz2, hz⟩ :=
    Theory.GroupAction.exists_conjugating_element_of_elementary_displacement
      L U A hLA S ⟨v, (show V ≤ A from le_sup_right) hv⟩ hvfix (fun l => by
        rw [commutator_comm] at hc
        exact hc (commutator_mem_commutator l.property hv))
  refine ⟨z, (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨⟨map_subtype_le _ hzU, hUQ hzU⟩, hz2, ?_⟩, fun l hl => hz ⟨l, hl⟩⟩
  intro s hs
  have he := hz ⟨s, hs.1⟩
  have hvs : v * s * v⁻¹ = s := by
    rw [← mem_centralizer_iff.mp (hV hv).2 s hs.2, mul_inv_cancel_right]
  rw [hvs] at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

end CFSG.Quasithin.ChapterE.Section06
