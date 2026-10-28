module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadOvergroup
public import Theory.GroupAction.SimpleCosets
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Faithfulness of the actual linear/hexad join action

The original linear subgroup is not normal in the join with the literal
hexad overgroup. Otherwise its intersection with that overgroup would give
a normal subgroup of index six in A6. Simplicity of the linear subgroup
then makes its coset action faithful. No degree or Mathieu recognition is
assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] {A : Subgroup G} [IsElementaryAbelian 2 A]
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F

/-- The literal linear group is not normal in the subgroup generated with
its retained alternating-six preimage. -/
theorem NaturalEndpointData.linear_not_normal_hexad_join (d : NaturalEndpointData A)
    (L : Subgroup G) (hPL : d.carrier ≤ L) (e : L ≃* Matrix.PSL3Four.PSL)
    (hmark : (d.carrier.subgroupOf L).map e.toMonoidHom = Point) :
    ¬ (L.subgroupOf (L⊔d.hexad_overgroup)).Normal := by
  obtain ⟨_,hAD,hPD,hDcard,hLD,π,hπs,hπker,_,_,_⟩ :=
    d.hexad_overgroup_structure L hPL e hmark
  let D := d.hexad_overgroup
  let K := L⊔D
  let P := d.carrier.subgroupOf D
  intro hn
  have hconj := (normal_subgroupOf_iff (show L≤K from le_sup_left)).mp hn
  have hPn : P.Normal := by
    constructor
    intro x hx g
    have hm : (g:G)*(x:G)*(g:G)⁻¹ ∈ L⊓D :=
      ⟨hconj x g (hPL hx) ((show D≤K from le_sup_right) g.property),
        D.mul_mem (D.mul_mem g.property x.property) (D.inv_mem g.property)⟩
    rwa [hLD] at hm
  let Q := P.map π
  have hQn : Q.Normal := hPn.map π hπs
  have hker : π.ker ≤ P := by
    rw [hπker]
    exact fun _ hx => d.kernel_le hx
  have hPi : P.index = 6 := by
    have hh := P.card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hPD).toEquiv,d.carrier_card,hDcard] at hh
    omega
  have hQi : Q.index = 6 := (P.index_map_eq hπs hker).trans hPi
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases hQn.eq_bot_or_eq_top with hb | ht
  · rw [hb,index_bot,nat_card_alternatingGroup,Nat.card_fin] at hQi
    norm_num [Nat.factorial] at hQi
  · rw [ht,index_top] at hQi
    omega

/-- The actual coset action of the linear/hexad join on its original linear
subgroup is faithful; its degree remains to be established separately. -/
theorem NaturalEndpointData.linear_hexad_join_coset_faithful (d : NaturalEndpointData A)
    (L : Subgroup G) (hPL : d.carrier ≤ L) (e : L ≃* Matrix.PSL3Four.PSL)
    (hmark : (d.carrier.subgroupOf L).map e.toMonoidHom = Point) :
    Function.Injective (MulAction.toPermHom (L⊔d.hexad_overgroup : Subgroup G)
      ((L⊔d.hexad_overgroup : Subgroup G) ⧸ L.subgroupOf (L⊔d.hexad_overgroup))) := by
  let K := L⊔d.hexad_overgroup
  let P := L.subgroupOf K
  let N := P.normalCore
  let eP : P ≃* Matrix.PSL3Four.PSL :=
    (subgroupOfEquivOfLe (show L≤K from le_sup_left)).trans e
  let : IsSimpleGroup Matrix.PSL3Four.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup P := eP.isSimpleGroup
  have hcore : N = ⊥ := by
    rcases (inferInstance : (N.subgroupOf P).Normal).eq_bot_or_eq_top with hn | hn
    · have hh := congrArg (Subgroup.map P.subtype) hn
      simpa only [subgroupOf_map_subtype,
        show N⊓P=N from inf_eq_left.mpr P.normalCore_le,Subgroup.map_bot] using hh
    · have hPN : P ≤ N := by
        intro x hx
        exact (show (⟨x,hx⟩:P) ∈ N.subgroupOf P by rw [hn]; trivial)
      have he : P=N := le_antisymm hPN P.normalCore_le
      have hp : P.Normal := he.symm ▸ (inferInstance : N.Normal)
      exact (d.linear_not_normal_hexad_join L hPL e hmark hp).elim
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [← normalCore_eq_ker]
  exact hcore

end CFSG.Quasithin.HigmanSims
