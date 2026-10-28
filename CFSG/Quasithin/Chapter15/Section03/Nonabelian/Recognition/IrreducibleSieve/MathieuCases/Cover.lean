module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.MathieuCases.Models
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Exclusion of the ambient triple-M₂₂ extension

Minimal normality and nonsolvability make the component join perfect, so it
lies in the kernel of the ambient cyclic quotient. A normal subgroup of the
quasisimple kernel is central or the whole kernel. The first option contradicts
nonsolvability, and the second contradicts centerlessness of the component join.
This uses both actual normal subgroups, without identifying the component join
with a central quotient or assuming a twelve-dimensional module model.

Source: Aschbacher–Smith, G.9.3(2) and 15.3.58, printed pp.353 and 1149.
-/

public section

open scoped IsMulCommutative
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.MathieuCases
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {K : Subgroup H}

private theorem component_perfect (hK : ComponentData ρ K) : Group.IsPerfect K := by
  let : K.Normal := hK.normal
  rcases hK.minimal ⁅K, K⁆ inferInstance (commutator_le_left K K) with hb | ht
  · let : IsMulCommutative K := commutator_self_eq_bot_iff.mp hb
    exact (hK.nonsolvable inferInstance).elim
  · exact isPerfect_iff.mpr ht

/-- A nonsolvable minimal normal component join cannot lie in the genuine
ambient triple-cover extension. No module recognition is needed. -/
theorem not_tripleExtension (hK : ComponentData ρ K)
    (e : TripleExtension H) : False := by
  let : K.Normal := hK.normal
  let : Group.IsPerfect K := component_perfect hK
  let J := e.projection.ker
  let : IsQuasisimple J := e.cover.quasisimple
  have hKJ : K ≤ J := by
    intro k hk
    exact Abelianization.commutator_subset_ker (e.projection.comp K.subtype)
      (Group.IsPerfect.mem_commutator (g := (⟨k, hk⟩ : K)))
  rcases IsQuasisimple.normal_le_center_or_eq_top (K.subgroupOf J) with hc | ht
  · let f : K →* center J := (inclusion hKJ).codRestrict (center J) (fun k => hc k.property)
    have hf : Function.Injective f := by
      intro x y h
      exact Subtype.ext (congrArg (fun z : center J => ((z : J) : H)) h)
    exact hK.nonsolvable (Group.isSolvable_of_isSolvable_injective hf)
  · have he : K = J := le_antisymm hKJ (fun x hx =>
      show (⟨x, hx⟩ : J) ∈ K.subgroupOf J from ht ▸ mem_top _)
    have hz : Nat.card (center J) = 3 := e.cover.center_card
    rw [← he, hK.center_eq_bot, card_bot] at hz
    norm_num at hz
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.MathieuCases

