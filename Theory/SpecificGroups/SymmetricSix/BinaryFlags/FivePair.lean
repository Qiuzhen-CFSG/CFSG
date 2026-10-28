module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.EvenPointCoreNormal

/-!
# Two even point cores generate the source five-letter subgroup

Choose the cubic mover (04)(14), fixing5 and moving the distinguished
pair. The two resulting four-groups lie in the even stabilizer of5.
Their generated group has order divisible by4,3,5, using two explicit
products of generators, so it is the entire sixty-element stabilizer.
Conjugation gives the result in every simultaneous marking.

Source: Aschbacher–Smith,13.5.14(3), printed p.919.
-/

@[expose] public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.FivePair

def five : Subgroup S := MulAction.stabilizer S (5 : Fin 6) ⊓ alternatingGroup (Fin 6)
def mover : S := Equiv.swap 0 4 * Equiv.swap 1 4
private def a : S := swap01*swap23
private def b : S := Equiv.swap 0 2*Equiv.swap 1 3
private theorem a_mem : a ∈ pointCoreEven := by
  refine ⟨?_,by change Equiv.Perm.sign a=1;decide +kernel⟩
  rw [pointCore_eq_closure]
  exact subset_closure (by simp [a])
private theorem b_mem : b ∈ pointCoreEven := by
  refine ⟨?_,by change Equiv.Perm.sign b=1;decide +kernel⟩
  rw [pointCore_eq_closure]
  exact subset_closure (by simp [b])

private def words : List S := (permsOfList [0,1,2,3,4]).filter (fun g => decide (Equiv.Perm.sign g=1))
private theorem mem_words (g : S) : g∈words ↔ g∈five := by
  rw [words,List.mem_filter,decide_eq_true_eq]
  constructor
  · intro hg
    refine ⟨?_,hg.2⟩
    change g 5=5
    by_contra hn
    have hh := mem_of_mem_permsOfList hg.1 hn
    simp at hh
  · intro hg
    refine ⟨?_,hg.2⟩
    apply mem_permsOfList_of_mem
    intro i hi
    fin_cases i <;> simp_all
    exact (hi hg.1).elim
private instance : Fintype five := Fintype.ofFinset words.toFinset (by
  intro g
  rw [List.mem_toFinset]
  exact mem_words g)

theorem five_card : Nat.card five=60 := by rw [Nat.card_eq_fintype_card];decide +kernel

theorem mover_mem : mover∈five := by
  change mover 5=5 ∧ Equiv.Perm.sign mover=1
  decide +kernel

theorem mover_moves_line : mover∉H1 := by decide +kernel

theorem pointCore_le_five : pointCoreEven≤five :=
  fun _ hx => ⟨(pointCoreEven_le_K hx).1.2,hx.2⟩

/-- The two actual even point cores generate the five-letter A₅ subgroup. -/
theorem pair_generates : pointCoreEven ⊔ pointCoreEven.map (MulAut.conj mover⁻¹).toMonoidHom = five := by
  let I := pointCoreEven ⊔ pointCoreEven.map (MulAut.conj mover⁻¹).toMonoidHom
  have hle : I≤five := by
    apply sup_le pointCore_le_five
    rintro _ ⟨x,hx,rfl⟩
    exact five.mul_mem (five.mul_mem (five.inv_mem mover_mem) (pointCore_le_five hx)) mover_mem
  have h4 : 4∣Nat.card I := pointCoreEven_card ▸ card_dvd_of_le (show pointCoreEven≤I from le_sup_left)
  have h3 : 3∣Nat.card I := by
    let c := a*(mover⁻¹*a*mover)
    have hc : c∈I := mul_mem (mem_sup_left a_mem) (mem_sup_right (mem_map_of_mem _ a_mem))
    have ho : orderOf c=3 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
    exact ho ▸ I.orderOf_dvd_natCard hc
  have h5 : 5∣Nat.card I := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    let c := a*(mover⁻¹*b*mover)
    have hc : c∈I := mul_mem (mem_sup_left a_mem) (mem_sup_right (mem_map_of_mem _ b_mem))
    have ho : orderOf c=5 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
    exact ho ▸ I.orderOf_dvd_natCard hc
  have h60 : 60∣Nat.card I :=
    (by decide : Nat.Coprime 12 5).mul_dvd_of_dvd_of_dvd
      ((by decide : Nat.Coprime 4 3).mul_dvd_of_dvd_of_dvd h4 h3) h5
  exact eq_of_le_of_card_ge hle (by rw [five_card];exact Nat.le_of_dvd Nat.card_pos h60)

/-- Pair generation is compatible with the actual simultaneous flag marking. -/
theorem marked_pair_generates (s : S) :
    pointCoreEven.map (MulAut.conj s).toMonoidHom ⊔
      (pointCoreEven.map (MulAut.conj s).toMonoidHom).map
        (MulAut.conj (s*mover*s⁻¹)⁻¹).toMonoidHom =
      five.map (MulAut.conj s).toMonoidHom := by
  have hc : (pointCoreEven.map (MulAut.conj s).toMonoidHom).map
      (MulAut.conj (s*mover*s⁻¹)⁻¹).toMonoidHom =
      (pointCoreEven.map (MulAut.conj mover⁻¹).toMonoidHom).map
        (MulAut.conj s).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change (s*mover*s⁻¹)⁻¹*(s*x*s⁻¹)*((s*mover*s⁻¹)⁻¹)⁻¹ =
      s*(mover⁻¹*x*(mover⁻¹)⁻¹)*s⁻¹
    group
  rw [hc,←Subgroup.map_sup,pair_generates]

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.FivePair
end
