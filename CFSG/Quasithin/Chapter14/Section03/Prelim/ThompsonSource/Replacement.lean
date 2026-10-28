module

public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import Stellmacher.ElementaryAbelianMaxSylowImages
public import Theory.GroupTheory.ElementaryThompsonFrattini

/-!
# Equal-weight replacement and Thompson normality

B.2.8 lifts an equal-weight image subgroup to a maximal elementary subgroup
of the original Sylow. An actual conjugator and kernel conjugacy preserve
this maximality and the prescribed image. If every nontrivial image inside D
admits a conjugate escaping D within the Sylow image, then J(S) lies in the
action kernel. When the kernel is a two-group, Thompson heredity and its
normality make J(S) normal.

Source: Aschbacher–Smith, B.2.8 and 14.3.9(2), printed pp.76 and 992–993.
-/

public section

open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section03.ThompsonSource

variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

theorem thompson_le_kernel_of_image_escape
    (S : Sylow 2 G) (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* Q) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G)) (hVS : V ≤ S)
    (D : Subgroup Q)
    (hJ : (elementaryAbelianMaxJ (S : Subgroup G)).map q ≤ D)
    (escape : ∀ B : Subgroup Q, B ≤ D → B ≠ ⊥ → IsElementaryAbelian 2 B →
      ∃ C : Subgroup Q, IsElementaryTwo C ∧
        EqualWeightLE (NormalElementaryQuotient.representation V q hq hker) C B ∧
        ∃ g : Q, C.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G).map q ∧
          ¬ C.map (MulAut.conj g).toMonoidHom ≤ D) :
    elementaryAbelianMaxJ (S : Subgroup G) ≤ q.ker := by
  classical
  apply sSup_le
  intro A hA
  by_contra hn
  have hne : A.map q ≠ ⊥ := fun he => hn ((map_eq_bot_iff A).mp he)
  have hAJ : A ≤ elementaryAbelianMaxJ (S : Subgroup G) := le_sSup hA
  obtain ⟨C, hC, heq, g, hgS, hgD⟩ :=
    escape (A.map q) ((map_mono hAJ).trans hJ) hne (hA.2.1.map q)
  have hD := ChapterB.lemma_B_2_8_construct V q hq hker
    (S : Subgroup G) hVS A hA C hC heq
  let A' := (A ⊓ C.comap q) ⊔ (V ⊓ centralizer (A ⊓ C.comap q : Set G))
  have hA' : A' ∈ elementaryAbelianMaxSubgroups (S : Subgroup G) := hD.1
  have hA'q : A'.map q = C := hD.2
  obtain ⟨x, rfl⟩ := hq g
  let B := A'.map (MulAut.conj x).toMonoidHom
  have hB : B ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G) := by
    have hh := (maxFamily_map_injective_iff (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective ⊤ A').mpr ((maxFamily_sylow_iff S A').mp hA').2
    rwa [map_top_of_surjective (MulAut.conj x).toMonoidHom
      (MulAut.conj x).surjective] at hh
  have hBq : B.map q = C.map (MulAut.conj (q x)).toMonoidHom := by
    rw [← hA'q, map_map, map_map]
    congr 1
    ext a
    simp [MulAut.conj_apply]
  obtain ⟨B', hB', hB'q⟩ := exists_maxFamily_sylow_same_image S q B hB
    (hBq ▸ hgS)
  apply hgD
  rw [← hBq, ← hB'q]
  exact (map_mono (le_sSup hB')).trans hJ

theorem thompson_normal_of_image_escape
    (S : Sylow 2 G) (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* Q) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G)) (hk2 : IsPGroup 2 q.ker)
    (hVS : V ≤ S) (D : Subgroup Q)
    (hJ : (elementaryAbelianMaxJ (S : Subgroup G)).map q ≤ D)
    (escape : ∀ B : Subgroup Q, B ≤ D → B ≠ ⊥ → IsElementaryAbelian 2 B →
      ∃ C : Subgroup Q, IsElementaryTwo C ∧
        EqualWeightLE (NormalElementaryQuotient.representation V q hq hker) C B ∧
        ∃ g : Q, C.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G).map q ∧
          ¬ C.map (MulAut.conj g).toMonoidHom ≤ D) :
    (elementaryAbelianMaxJ (S : Subgroup G)).Normal := by
  have hJK := thompson_le_kernel_of_image_escape S V q hq hker hVS D hJ escape
  have hKS : q.ker ≤ (S : Subgroup G) := hk2.le_sylow_of_normal S
  have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq q.ker (S : Subgroup G) hKS
  have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le
    (S : Subgroup G) q.ker hJK
  have horder : elementaryAbelianMaxOrder q.ker =
      elementaryAbelianMaxOrder (S : Subgroup G) :=
    le_antisymm hsmall.1 hlarge.1
  have he : elementaryAbelianMaxJ q.ker =
      elementaryAbelianMaxJ (S : Subgroup G) :=
    le_antisymm (hsmall.2 horder) (hlarge.2 horder.symm)
  rw [← he]
  apply normal_iff_map_conj_eq.mpr
  intro g
  change (elementaryAbelianMaxJ q.ker).map (MulAut.conj g).toMonoidHom = _
  rw [← elementaryAbelianMaxJ_map_equiv (MulAut.conj g) q.ker]
  congr 1
  exact (normal_iff_map_conj_eq.mp q.normal_ker) g

end CFSG.Quasithin.Chapter14.Section03.ThompsonSource
