module

public import Theory.GroupTheory.OmegaCenterProduct
public import Theory.GroupTheory.ElementaryThompsonFrattini
public import CFSG.Quasithin.ChapterB.Section02.Thompson

/-!
# Thompson and Baumann subgroups after maximum-elementary placement

For disjoint commuting subgroups A,C of R, placement of every maximum
elementary subgroup of R in AC determines J(R). If J(A)=A and the
centralizer in R of Ω₁(Z(A)) lies in AC, the Baumann subgroup is
A Baum(C). The proof uses the actual multiplication equivalence and
centralizer intersections; no product decomposition is assumed.

These are conditional finite-group reductions for the symplectic branch
of Aschbacher–Smith 13.6.6, printed p.927. The model-specific placement
and center-action premises must be proved before applying the source theorem.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem omega_le (A : Subgroup G) : omegaOneCenterAmbient A ≤ A :=
  fun x hx => ((mem_omegaOneCenterAmbient_iff A x).mp hx).1

omit [Finite G] in
private theorem j_le (A : Subgroup G) : elementaryAbelianMaxJ A ≤ A :=
  sSup_le fun _ h => h.1

omit [Finite G] in
private theorem centralizer_sup_eq (A B : Subgroup G) :
    centralizer ((A ⊔ B : Subgroup G) : Set G) = centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf (centralizer_le (show A ≤ A ⊔ B from le_sup_left))
      (centralizer_le (show B ≤ A ⊔ B from le_sup_right))
  · apply le_centralizer_iff.mpr
    apply sup_le
    · exact le_centralizer_iff.mp inf_le_left
    · exact le_centralizer_iff.mp inf_le_right

theorem thompson_product_of_maximal_placement (R A C : Subgroup G)
    (hAR : A ≤ R) (hCR : C ≤ R) (hd : Disjoint A C)
    (hc : A ≤ centralizer (C : Set G))
    (hmax : ∀ E ∈ elementaryAbelianMaxSubgroups R, E ≤ A ⊔ C) :
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ A ⊔ elementaryAbelianMaxJ C := by
  rw [← elementaryAbelianMaxJ_eq_of_intermediate R (A ⊔ C)
    (sSup_le hmax) (sup_le hAR hCR)]
  exact elementaryAbelianMaxJ_sup_of_disjoint_of_commuting A C hd hc

theorem thompsonAlpha_product_of_maximal_placement (R A C : Subgroup G)
    (hAR : A ≤ R) (hCR : C ≤ R) (hd : Disjoint A C)
    (hc : A ≤ centralizer (C : Set G))
    (hmax : ∀ E ∈ elementaryAbelianMaxSubgroups R, E ≤ A ⊔ C)
    (hJA : elementaryAbelianMaxJ A = A) :
    thompsonAlpha R = omegaOneCenterAmbient A ⊔ thompsonAlpha C := by
  unfold thompsonAlpha
  rw [thompson_product_of_maximal_placement R A C hAR hCR hd hc hmax, hJA]
  exact omegaOneCenterAmbient_sup_of_disjoint_of_commuting A _
    (hd.mono_right (j_le C)) (hc.trans (centralizer_le (j_le C)))

theorem baumann_product_of_maximal_placement (R A C : Subgroup G)
    (hAR : A ≤ R) (hCR : C ≤ R) (hd : Disjoint A C)
    (hc : A ≤ centralizer (C : Set G))
    (hmax : ∀ E ∈ elementaryAbelianMaxSubgroups R, E ≤ A ⊔ C)
    (hJA : elementaryAbelianMaxJ A = A)
    (hkernel : R ⊓ centralizer (omegaOneCenterAmbient A : Set G) ≤ A ⊔ C) :
    baumann R = A ⊔ baumann C := by
  have halpha := thompsonAlpha_product_of_maximal_placement R A C hAR hCR hd hc hmax hJA
  have hAC : A ≤ centralizer (thompsonAlpha C : Set G) :=
    hc.trans (centralizer_le ((omega_le _).trans (j_le C)))
  have hAZ : A ≤ centralizer (omegaOneCenterAmbient A : Set G) := by
    intro a ha z hz
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 a ha).symm
  have hCZ : C ≤ centralizer (omegaOneCenterAmbient A : Set G) :=
    (le_centralizer_iff.mp hc).trans (centralizer_le (omega_le A))
  have hBR : baumann R = R ⊓
      (centralizer (omegaOneCenterAmbient A : Set G) ⊓
       centralizer (thompsonAlpha C : Set G)) := by
    rw [baumann, halpha, centralizer_sup_eq]
  rw [hBR]
  apply le_antisymm
  · intro x hx
    obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A C hd hc
    let y := e.symm ⟨x, hkernel ⟨hx.1, hx.2.1⟩⟩
    have hxy : (y.1 : G) * (y.2 : G) = x :=
      (he y.1 y.2).symm.trans (congrArg Subtype.val (e.apply_symm_apply _))
    have hyc : (y.2 : G) ∈ centralizer (thompsonAlpha C : Set G) := by
      have hh := (centralizer (thompsonAlpha C : Set G)).mul_mem
        ((centralizer _).inv_mem (hAC y.1.property)) hx.2.2
      rwa [← hxy, inv_mul_cancel_left] at hh
    rw [← hxy]
    exact mul_mem_sup y.1.property ⟨y.2.property, hyc⟩
  · apply sup_le
    · exact le_inf hAR (le_inf hAZ hAC)
    · exact le_inf (inf_le_left.trans hCR)
        (le_inf (inf_le_left.trans hCZ) inf_le_right)
end CFSG.Quasithin.ChapterB
