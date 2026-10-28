module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.ReducibleEndpoints
public import Theory.GroupTheory.NormalizedSupCard
/-!
# The literal elementary-nine kernel is the three-core

The cyclic D.2.17 endpoint generates the actor from its normal elementary
kernel of order nine and one involution. Its index is two, so the kernel is
a normal Sylow three subgroup and equals the three-core. This identifies the
marked kernel with the core used by the original component irreducibility
consumer in 15.1.2 (printed p.1085).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}
omit [Finite G] in
theorem LocalGeneration.kernel_eq_threeCore_of_elementary_nine (l : LocalGeneration ρ)
    (he : IsElementaryAbelian 3 l.kernel) (hc : Nat.card l.kernel = 9) :
    l.kernel = pCore 3 G := by
  let := l.normal
  let := he
  have hp : IsPGroup 3 l.kernel := IsElementaryAbelian.isPGroup 3 l.kernel
  have ht : Nat.card (zpowers l.involution) = 2 := by rw [Nat.card_zpowers,l.order_two]
  have hd : Disjoint l.kernel (zpowers l.involution) := IsPGroup.disjoint_of_coprime
    hp (IsPGroup.of_card (n := 1) (by simpa using ht)) (by decide)
  have hcard := card_sup_eq_mul_of_normalizes_of_disjoint l.kernel (zpowers l.involution)
    le_normalizer_of_normal hd
  rw [l.generated,card_top,hc,ht] at hcard
  have hi : l.kernel.index = 2 := by
    have hh := l.kernel.card_mul_index
    rw [hc,hcard] at hh
    omega
  let S : Sylow 3 G := hp.toSylow (by rw [hi]; decide)
  exact le_antisymm (le_sSup ⟨l.normal,hp⟩) (pCore_isPGroup.le_sylow_of_normal S)
end CFSG.Quasithin.ChapterD.CyclicSource
