module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Solvable

/-!
# Transport from a conjugate parabolic

Suppose solvable overgroups of S inside P normalize S. If a conjugate of a
solvable overgroup H of S lies in P, Sylow conjugacy inside P aligns the
conjugated S with the original S. The combined conjugation preserves S and
sends H into P, so the normalization conclusion transports back to H.

This preserves the explicit conjugation witness in the parabolic step of
Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528),
`refs/quasithin.pdf`.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Placement.ParabolicBorel

/-- Align the two Sylows inside the given overgroup before applying its normalization theorem. -/
theorem normalizes_of_conjugate_into
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (P H : Subgroup G)
    (hSP : (S : Subgroup G) ≤ P) (hSH : (S : Subgroup G) ≤ H)
    [Group.IsSolvable H]
    (hP : ∀ K : Subgroup G, K ≤ P → (S : Subgroup G) ≤ K →
      Group.IsSolvable K → K ≤ normalizer (S : Set G))
    (g : G) (hg : H.map (MulAut.conj g).toMonoidHom ≤ P) :
    H ≤ normalizer (S : Set G) := by
  let c := MulAut.conj g
  let T := S.mapSurjective (f := c.toMonoidHom) c.surjective
  have hTP : (T : Subgroup G) ≤ P := (map_mono hSH).trans hg
  let SP := S.subtype hSP
  let TP := T.subtype hTP
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq P TP SP
  let d := MulAut.conj (a : G)
  have he : (T : Subgroup G).map d.toMonoidHom = (S : Subgroup G) := by
    have hc := congrArg (fun R : Sylow 2 P => (R : Subgroup P).map P.subtype) ha
    change (((TP : Subgroup P).map (MulAut.conj a).toMonoidHom).map P.subtype) =
      (SP : Subgroup P).map P.subtype at hc
    rw [Subgroup.map_map] at hc
    have hcomp : P.subtype.comp (MulAut.conj a).toMonoidHom =
        d.toMonoidHom.comp P.subtype := rfl
    rw [hcomp, ← Subgroup.map_map] at hc
    simpa only [TP,SP,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTP,
      map_subgroupOf_eq_of_le hSP] using hc
  let e := c.trans d
  have hS : (S : Subgroup G).map e.toMonoidHom = (S : Subgroup G) := by
    change (S : Subgroup G).map (d.toMonoidHom.comp c.toMonoidHom) = _
    rw [← Subgroup.map_map]
    exact he
  have hHP : H.map e.toMonoidHom ≤ P := by
    change H.map (d.toMonoidHom.comp c.toMonoidHom) ≤ P
    rw [← Subgroup.map_map]
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact P.mul_mem (P.mul_mem a.property (hg hy)) (P.inv_mem a.property)
  have hSE : (S : Subgroup G) ≤ H.map e.toMonoidHom := by
    rw [← hS]
    exact map_mono hSH
  have hsol : Group.IsSolvable (H.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective H)
  have hN := hP _ hHP hSE hsol
  have hnorm : (normalizer (S : Set G)).map e.toMonoidHom = normalizer (S : Set G) := by
    have heq := map_equiv_normalizer_eq (S : Subgroup G) e
    rw [hS] at heq
    exact heq
  rw [← hnorm] at hN
  exact (map_le_map_iff_of_injective e.injective).mp hN

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Placement.ParabolicBorel
