module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Basic
public import Theory.GroupTheory.PPerfectHom


/-!
# Characteristic two closes a diagonal residual supplement

Write Q=O₂(J) and F=C_Q(K). If Q=F × V and [Q,A]≤V, invariance gives
[F,A]≤F∩V=1. Thus both K and A fix F. A two-perfect supplement D with
KD=KA fixing V now fixes Q, so characteristic two puts D in Q. A
homomorphism from a two-perfect group to a two-group is trivial, giving
D=1 and A≤K.

The source application has A=L₊, V=W_K and D the two-residual of the
quotient centralizer. The direct decomposition and chief-count commutator
bound are explicit inputs here and must still be proved in source assembly.
This argument avoids using the full quotient centralizer as a coprime actor.
Source: Aschbacher–Smith, Lemma 13.3.14, last paragraph, printed p.893.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal
variable {G : Type*} [Group G]

private theorem normalizes_centralizer (K : Subgroup G) :
    normalizer (K : Set G) ≤ normalizer (centralizer (K : Set G) : Set G) :=
  (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp inferInstance

/-- The invariant direct factor C_Q(K) is fixed by L₊ as soon as its
 commutators lie in the disjoint factor W_K. -/
theorem centralizes_core_fixed_factor (J K A V : Subgroup G)
    (hAJ : A ≤ J) (hn : A ≤ normalizer K)
    (hdis : Disjoint (J.pCoreIn 2 ⊓ centralizer (K : Set G)) V)
    (hm : ⁅J.pCoreIn 2, A⁆ ≤ V) :
    A ≤ centralizer ((J.pCoreIn 2 ⊓ centralizer (K : Set G)) : Set G) := by
  let F := J.pCoreIn 2 ⊓ centralizer (K : Set G)
  have hAQ : A ≤ normalizer (J.pCoreIn 2 : Set G) :=
    (hAJ.trans J.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hAC := hn.trans (normalizes_centralizer K)
  have hAF : A ≤ normalizer (F : Set G) := by
    apply le_normalizer_iff.mpr
    intro a ha x hx
    exact ⟨le_normalizer_iff.mp hAQ a ha x hx.1,
      le_normalizer_iff.mp hAC a ha x hx.2⟩
  have hc : ⁅F, A⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (le_inf (le_normalizer_iff_commutator_le_left.mp hAF)
      ((commutator_mono inf_le_left le_rfl).trans hm)).trans hdis.le_bot
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)

/-- The terminal characteristic-two argument. The supplement D is
 two-perfect (in the source it is O²(C_KL₊(K/O₂(K)))). Its fixation of
 W_K, the direct decomposition and the chief-count commutator bound force
 D=1, hence L₊≤K. No chief-factor or block identification is asserted here. -/
theorem le_component_of_core_decomposition (J K A D V : Subgroup G)
    (hJ : J ∈ Chapter1.He G) (hAJ : A ≤ J) (hDJ : D ≤ J)
    (hn : A ≤ normalizer K) (hD : IsPPerfect 2 D)
    (hgen : K ⊔ D = K ⊔ A)
    (hDV : D ≤ centralizer (V : Set G))
    (hsplit : (J.pCoreIn 2 ⊓ centralizer (K : Set G)) ⊔ V = J.pCoreIn 2)
    (hdis : Disjoint (J.pCoreIn 2 ⊓ centralizer (K : Set G)) V)
    (hm : ⁅J.pCoreIn 2, A⁆ ≤ V) : A ≤ K := by
  let F := J.pCoreIn 2 ⊓ centralizer (K : Set G)
  have hAF : A ≤ centralizer (F : Set G) :=
    centralizes_core_fixed_factor J K A V hAJ hn hdis hm
  have hKF : K ≤ centralizer (F : Set G) := le_centralizer_iff.mpr inf_le_right
  have hDF : D ≤ centralizer (F : Set G) := by
    apply (show D ≤ K ⊔ D from le_sup_right).trans
    rw [hgen]
    exact sup_le hKF hAF
  have hDQ : D ≤ centralizer (J.pCoreIn 2 : Set G) := by
    apply le_centralizer_iff.mpr
    rw [← hsplit]
    exact sup_le (le_centralizer_iff.mp hDF) (le_centralizer_iff.mp hDV)
  have hDcore : D ≤ J.pCoreIn 2 := (le_inf hDJ hDQ).trans hJ
  have he : inclusion hDcore = 1 :=
    hD.hom_eq_one_of_isPGroup (isPGroup_pCoreIn 2 J) (inclusion hDcore)
  have hDbot : D = ⊥ := by
    apply le_bot_iff.mp
    intro d hd
    exact congrArg Subtype.val (DFunLike.congr_fun he ⟨d, hd⟩)
  have hAK : A ≤ K ⊔ D := hgen.symm ▸ (show A ≤ K ⊔ A from le_sup_right)
  simpa only [hDbot, sup_bot_eq] using hAK

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal
