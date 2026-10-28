module
public import Theory.GroupTheory.Commutator.NormalClosureSupplement
public import Theory.GroupTheory.Commutator.NormalizesSupplement
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The residual of a normally generated two-subgroup

Suppose a normal subgroup A of odd order is supplemented by P, and R is a
two-subgroup centralized by P. The normal closure N of R satisfies
N=R[N,G], with [N,G]=[R,A]. Its commutator subgroup lies in the odd group A,
so it is two-perfect, while R is a two-group supplement. Hence O²(N)=[A,R].

Application: the literal image calculation in Aschbacher--Smith15.2.3,
printed p.1105, where A=O²(M-bar) and P is its abelian Sylow two-subgroup.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- The exact normal-closure residual under an odd normal and a centralizing supplement. -/
theorem embedded_twoResidual_normalClosure_eq_commutator
    (A P R : Subgroup G) [A.Normal]
    (hgen : A ⊔ P = ⊤) (hodd : Nat.Coprime 2 (Nat.card A))
    (hR : IsPGroup 2 R) (hRP : R ≤ centralizer (P : Set G)) :
    (pResidual 2 (normalClosure (R : Set G))).map (normalClosure (R : Set G)).subtype =
      ⁅A, R⁆ := by
  let N := normalClosure (R : Set G)
  let C := ⁅N, (⊤ : Subgroup G)⁆
  have he : C = ⁅R, A⁆ := normalClosure_commutator_eq_of_centralizing_supplement R A P hgen hRP
  have hCA : C ≤ A := he.le.trans (commutator_le_right _ _)
  have hCN : C ≤ N := commutator_le_left _ _
  let : C.Normal := inferInstance
  have hnormal : (R ⊔ C : Subgroup G).Normal := by
    apply normalizer_eq_top_iff.mp
    exact top_unique (le_normalizer_sup_of_commutator_le R ⊤ R C le_rfl
      (commutator_mono le_normalClosure le_rfl))
  have hN : N = C ⊔ R := by
    rw [sup_comm]
    exact le_antisymm (normalClosure_le_normal (show R ≤ R ⊔ C from le_sup_left))
      (sup_le le_normalClosure hCN)
  have hp : IsPPerfect 2 C := by
    apply (pResidual_eq_top_iff 2 C).mp
    apply top_unique
    intro c _
    exact mem_pResidual_of_orderOf_coprime
      (hodd.of_dvd_right ((_root_.orderOf_dvd_natCard c).trans (card_dvd_of_le hCA)))
  change (pResidual 2 N).map N.subtype = ⁅A, R⁆
  rw [hN]
  exact (embedded_pResidual_join_pGroup C R hp hR le_normalizer_of_normal).trans
    (he.trans (commutator_comm R A))

end Subgroup
