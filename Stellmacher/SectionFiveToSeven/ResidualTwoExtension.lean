module
public import Stellmacher.SectionFiveToSeven.Defs
public import Stellmacher.SectionThree.LemmaThreeSeven
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift

/-!
# Residual stability under a normal two-group extension

Let E be the two-residual of K. If a two-group Q normalizes E, adjoining Q
does not change the two-residual: O²(EQ)=E. This identifies a characteristic
subgroup of the product in the centralizer argument of Stellmacher (7.7).

The quotient EQ/E is a two-group, so its residual lies in E. Conversely E
is residual-perfect, hence maps trivially into every two-group quotient of
EQ and belongs to the intersection defining that residual. We use the
existing residual kernel and normal-extension lemmas from Section Three.
Source: refs/latex/stellmacher-n-group.tex, (7.7), journal p.36.
-/

namespace Stellmacher.SectionsFiveToSeven

open BenderSuzuki.External Stellmacher.SectionThree

public theorem twoResidualIn_sup_twoGroup_eq
    {G : Type*} [Group G] [Finite G]
    (K Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hnorm : Q ≤ Subgroup.normalizer (twoResidualIn K : Set G)) :
    twoResidualIn (twoResidualIn K ⊔ Q) = twoResidualIn K := by
  let E := twoResidualIn K
  let L := E ⊔ Q
  have hEL : E ≤ L := le_sup_left
  have hn : (E.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEL).mpr
      (sup_le E.le_normalizer hnorm)
  apply le_antisymm
  · exact twoResidualAmbient_le_left_of_le_sup E Q L hn hQ le_rfl
  · intro x hx
    let xL : L := ⟨x, hEL hx⟩
    have hxres : xL ∈ twoResidualSubgroup L := by
      rw [twoResidualSubgroup, Subgroup.mem_sInf]
      intro N hN
      let _ : N.Normal := hN.1
      let f : E →* L ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hEL)
      have hquot : IsPGroup 2 (L ⧸ N) := by
        rw [IsPGroup.iff_card]
        obtain ⟨n, hn⟩ := hN.2
        exact ⟨n, by simpa [← Subgroup.index_eq_card] using hn⟩
      have hker : hktPResidual 2 E ≤ f.ker := hktPResidual_le_ker_of_isPGroup f hquot
      have hperfect : hktPResidual 2 E = ⊤ := twoResidualAmbient_has_top_twoResidual K
      rw [hperfect] at hker
      have hf : f ⟨x, hx⟩ = 1 := hker (Subgroup.mem_top _)
      exact (QuotientGroup.eq_one_iff (N := N) xL).mp hf
    exact Subgroup.mem_map_of_mem L.subtype hxres

end Stellmacher.SectionsFiveToSeven

