module
public import Mathlib.GroupTheory.Perm.Centralizer
public import Theory.GroupTheory.ElementaryNormalizerThreeRank
public import Theory.GroupTheory.NormalizerActionSurjective
/-!
# The full automizer of a five-subgroup in S₅

The centralizer of a five-cycle has order5. Conjugation therefore bounds the
normalizer order by20; its Sylow congruence modulo25 makes that bound exact.
Kernel and image counting then proves that every automorphism of the original
five-subgroup is realized by its normalizer.

Source application: Aschbacher--Smith J.3.6, printed p.439, through the literal
Ru₂ quotient map H → S₅.
-/

public section
open Subgroup Equiv.Perm
namespace Equiv.Perm
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem five_subgroup_centralizer_card (P : Subgroup (Equiv.Perm (Fin 5)))
    (hP : Nat.card P=5) : Nat.card (centralizer (P : Set (Equiv.Perm (Fin 5))))=5 := by
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G:=P) 5 (by rw [hP])
  have ho : orderOf (x : Equiv.Perm (Fin 5))=5 := (orderOf_coe x).trans hx
  have hcycle : (x : Equiv.Perm (Fin 5)).IsCycle := isCycle_of_prime_order'' (by decide) (by simpa using ho)
  have htype : (x : Equiv.Perm (Fin 5)).cycleType = {5} := by
    rw [hcycle.cycleType,← hcycle.orderOf,ho]
  have hg : zpowers (x : Equiv.Perm (Fin 5))=P :=
    eq_of_le_of_card_ge (zpowers_le.mpr x.property) (by rw [Nat.card_zpowers,ho,hP])
  rw [← hg,zpowers_eq_closure,centralizer_closure,nat_card_centralizer,htype]
  norm_num

theorem five_subgroup_normalizer_card (P : Subgroup (Equiv.Perm (Fin 5)))
    (hP : Nat.card P=5) : Nat.card (normalizer (P : Set (Equiv.Perm (Fin 5))))=20 := by
  let : IsCyclic P := isCyclic_of_prime_card hP
  have ha : Nat.card (MulAut P)=4 := by rw [IsCyclic.card_mulAut,hP]; decide
  have hd := P.card_normalizer_dvd_card_centralizer_mul_card_mulAut
  rw [five_subgroup_centralizer_card P hP,ha] at hd
  have hb : Nat.card (normalizer (P : Set (Equiv.Perm (Fin 5))))≤20 := Nat.le_of_dvd (by decide) hd
  have hg : Nat.card (Equiv.Perm (Fin 5))=120 := by norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
  have hm := Sylow.card_normalizer_modEq_card (p:=5) (n:=1) (H:=P) hP
  rw [hg] at hm
  change _ %25=120%25 at hm
  omega

theorem five_subgroup_full_automizer (P : Subgroup (Equiv.Perm (Fin 5)))
    (hP : Nat.card P=5) : Function.Surjective P.normalizerMonoidHom := by
  let : IsCyclic P := isCyclic_of_prime_card hP
  have ha : Nat.card (MulAut P)=4 := by rw [IsCyclic.card_mulAut,hP]; decide
  have hk : Nat.card P.normalizerMonoidHom.ker=5 := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (P : Set (Equiv.Perm (Fin 5))))).toEquiv,
      five_subgroup_centralizer_card P hP]
  have he := P.normalizerMonoidHom.ker.card_mul_index
  rw [hk,index_ker,five_subgroup_normalizer_card P hP] at he
  apply MonoidHom.range_eq_top.mp
  apply eq_top_of_card_eq
  rw [ha]
  omega

end Equiv.Perm
