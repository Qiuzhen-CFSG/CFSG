module
public import Theory.GroupTheory.Commutator.CentralRow

/-!
# A single central commutator row bounds the relative centralizer index

If t lies in Q and [t,Q] lies in a finite subgroup Z centralizing Q, the
commutator map Q → Q has kernel C_Q(t) and image contained in Z. Its
kernel index is therefore at most |Z|. Q need not be abelian or finite.

The source consumer uses this with Q = Q_y, t in V_y, and Z = Z_y in
DGS85, Groups and Graphs, (12.5), printed p.182.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

/-- Central commutators with a single element bound its centralizer index. -/
theorem central_singleton_centralizer_index_le
    (Q Z : Subgroup G) [Finite Z] (hZQ : Z ≤ Q)
    (hZ : Z ≤ centralizer (Q : Set G)) {t : G} (ht : t ∈ Q)
    (hc : ⁅zpowers t,Q⁆ ≤ Z) :
    (centralizer ({t} : Set G)).relIndex Q ≤ Nat.card Z := by
  let u : Q := ⟨t,ht⟩
  have hm : (⁅zpowers u,(⊤ : Subgroup Q)⁆ : Subgroup Q).map Q.subtype = ⁅zpowers t,Q⁆ := by
    rw [map_commutator,MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype]
    rfl
  have hz : ⁅zpowers u,(⊤ : Subgroup Q)⁆ ≤ center Q := by
    intro z hzz
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (hZ (hc (hm ▸ mem_map_of_mem Q.subtype hzz)) x x.property)
  have hker : (CentralRow.commutatorHom u hz).ker =
      (centralizer ({t} : Set G)).subgroupOf Q := by
    rw [CentralRow.commutatorHom_ker]
    ext x
    simp only [mem_centralizer_singleton_iff,mem_subgroupOf]
    exact Subtype.ext_iff
  have hle : ⁅zpowers u,(⊤ : Subgroup Q)⁆ ≤ Z.subgroupOf Q := by
    intro z hzz
    exact hc (hm ▸ mem_map_of_mem Q.subtype hzz)
  let : Finite (Z.subgroupOf Q) := Finite.of_injective
    (subgroupOfEquivOfLe hZQ) (subgroupOfEquivOfLe hZQ).injective
  change ((centralizer ({t} : Set G)).subgroupOf Q).index ≤ _
  rw [←hker,index_ker,CentralRow.commutatorHom_range]
  exact (Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective _)).trans_eq
    (Nat.card_congr (subgroupOfEquivOfLe hZQ).toEquiv)

end Subgroup
