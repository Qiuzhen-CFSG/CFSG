module
public import Theory.GroupTheory.SylowImageLocalization

/-!
# Kernel conjugation over a group of order twenty

A group of order twenty has a unique Sylow-five subgroup. Thus every
five-subgroup maps into the image of a chosen Sylow-five subgroup under a
surjection, and Sylow conjugacy can be performed inside its kernel.
The original J.4 endpoint marking uses this with the two-core kernel.
-/

public noncomputable section
open Subgroup
namespace Sylow
local instance : Fact (Nat.Prime 5):=⟨by decide⟩

 theorem subsingleton_five_of_card_twenty {M:Type*} [Group M] [Finite M]
    (hc:Nat.card M=20) : Subsingleton (Sylow 5 M) := by
  let P:Sylow 5 M:=Classical.choice inferInstance
  have hP:Nat.card P=5:=by rw [P.card_eq_multiplicity,hc];decide +kernel
  have hi:(P:Subgroup M).index=4:=by
    have hh:=(P:Subgroup M).card_mul_index
    rw [hP,hc] at hh
    omega
  have hn:Nat.card (Sylow 5 M)=1:=by
    have hd:=P.card_dvd_index
    rw [hi] at hd
    have hb:=Nat.le_of_dvd (by decide:0<4) hd
    have hm:=card_sylow_modEq_one 5 M
    change Nat.card (Sylow 5 M)%5=1%5 at hm
    omega
  exact (Nat.card_eq_one_iff_unique.mp hn).1

 theorem exists_kernel_conjugate_le_of_card_twenty
    {G M:Type*} [Group G] [Finite G] [Group M] [Finite M]
    (R:Sylow 5 G) (q:G→*M) (hq:Function.Surjective q) (hc:Nat.card M=20)
    (A:Subgroup G) (hA:IsPGroup 5 A) :
    ∃g:G,q g=1 ∧ A.map (MulAut.conj g).toMonoidHom≤R := by
  let : Subsingleton (Sylow 5 M):=subsingleton_five_of_card_twenty hc
  obtain ⟨P,hP⟩:=(hA.map q).exists_le_sylow
  have he:P=R.mapSurjective hq:=Subsingleton.elim _ _
  apply R.exists_kernel_conjugate_le q A hA
  simpa only [he,Sylow.coe_mapSurjective] using hP
end Sylow
