module

public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Lifting normality of a p-perfect subgroup

Let f have p-group kernel. If that kernel normalizes the p-perfect subgroup
L and f(L) is normal, then L is normal. The inverse image of f(L) is L ker(f);
its p-residual is L, so L is characteristic in a normal subgroup. Neither a
central kernel nor ordinary perfectness of L is required. Kernel normalization
is essential and is an explicit hypothesis.

Source application: Aschbacher–Smith, proof of 13.8.20, printed p.955
(combined manuscript of 1 March 2004), lifting the normality of L₀* in H*.
-/

public section
namespace Subgroup
variable {G D : Type*} [Group G] [Group D] {p : ℕ}

/-- Normality lifts across a normalizing p-group kernel for p-perfect subgroups. -/
theorem normal_of_map_normal_of_pPerfect (f : G →* D) (L : Subgroup G)
    (hL : IsPPerfect p L) (hker : IsPGroup p f.ker)
    (hn : f.ker ≤ normalizer (L : Set G)) [(L.map f).Normal] : L.Normal := by
  let P := L ⊔ f.ker
  have hP : P = (L.map f).comap f := (comap_map_eq f L).symm
  let : P.Normal := hP ▸ inferInstance
  have hLP : (L.subgroupOf P).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hn)
  let := hLP
  have hp : IsPPerfect p (L.subgroupOf P) :=
    hL.of_surjective (subgroupOfEquivOfLe (show L ≤ P from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show L ≤ P from le_sup_left)).symm.surjective
  have hs : L.subgroupOf P ⊔ f.ker.subgroupOf P = ⊤ := by
    rw [← subgroupOf_sup (show L ≤ P from le_sup_left)
      (show f.ker ≤ P from le_sup_right)]
    exact subgroupOf_self P
  have he : (pResidual p P).map P.subtype = L := by
    rw [pResidual_eq_of_isPPerfect_sup (L.subgroupOf P) (f.ker.subgroupOf P)
      hp hker.comap_subtype hs, map_subgroupOf_eq_of_le (show L ≤ P from le_sup_left)]
  rw [← he]
  infer_instance

end Subgroup
