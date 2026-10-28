module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.ReflectedMarking.LocalNormalizer

/-!
# The actual order-eight subgroup of the cubic normalizer

The original normalizer has order72. Its Sylow two-subgroup contains the
marked central involution and has that line as its intersection with both
the extraspecial core and the cubic centralizer. The source residual-square
identity then places every square in the line. The last theorem retains
both original Sylow inclusions, for use in the reflection construction.

Source: Aschbacher, Sporadic Groups,45.3(5), printed p.243.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z:G}
namespace IsType
variable (h : IsType z) (X : Subgroup G) (hX : Nat.card X=9) (hXH : X≤centralizer z)
variable (S : Sylow 2 (centralizer z⊓normalizer (X:Set G) : Subgroup G))
include h hX hXH

theorem local_cubic_sylow_card : Nat.card S=8 := by
  rw [S.card_eq_multiplicity,h.cubic_local_normalizer_card X hX hXH]
  decide +kernel

omit hX in
theorem local_cubic_sylow_line :
    zpowers z≤(S:Subgroup (centralizer z⊓normalizer (X:Set G) : Subgroup G)).map
      (centralizer z⊓normalizer (X:Set G)).subtype := by
  let N : Subgroup G := centralizer z⊓normalizer (X:Set G)
  have hzN : zpowers z≤N := le_inf
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
    ((zpowers_le.mpr (show z∈Subgroup.centralizer (X:Set G) from
      fun x hx=>mem_centralizer_singleton_iff.mp (hXH hx))).trans (centralizer_le_normalizer _))
  let Z := (zpowers z).subgroupOf N
  let : Z.Normal := (normal_subgroupOf_iff_le_normalizer hzN).mpr (by
    rw [normalizer_zpowers_eq_centralizer_of_order_two z h.involution]
    exact inf_le_left)
  have hZ : IsPGroup 2 Z := IsPGroup.of_card (n:=1) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hzN).toEquiv,Nat.card_zpowers,h.involution]
    decide)
  have hh := map_mono (hZ.le_sylow_of_normal S) (f:=N.subtype)
  rwa [map_subgroupOf_eq_of_le hzN] at hh

theorem local_cubic_sylow_core_intersection :
    core z⊓((S:Subgroup (centralizer z⊓normalizer (X:Set G) : Subgroup G)).map
      (centralizer z⊓normalizer (X:Set G)).subtype)=zpowers z := by
  apply le_antisymm
  · have hSN : ((S:Subgroup (centralizer z⊓normalizer (X:Set G) : Subgroup G)).map
        (centralizer z⊓normalizer (X:Set G)).subtype)≤normalizer (X:Set G) :=
        (map_subtype_le _).trans inf_le_right
    exact (inf_le_inf_left (core z) hSN).trans
      (h.core_cubic_normalizer_intersection X hX hXH).le
  · exact le_inf h.toCentralizerHypothesis.line_le_core (h.local_cubic_sylow_line X hXH S)

theorem local_cubic_sylow_centralizer_intersection :
    ((S:Subgroup (centralizer z⊓normalizer (X:Set G) : Subgroup G)).map
      (centralizer z⊓normalizer (X:Set G)).subtype)⊓Subgroup.centralizer (X:Set G)=zpowers z := by
  let U := ((S:Subgroup (centralizer z⊓normalizer (X:Set G) : Subgroup G)).map
      (centralizer z⊓normalizer (X:Set G)).subtype)
  have hU : Nat.card U=8 := (card_map_of_injective (centralizer z⊓normalizer (X:Set G)).subtype_injective).trans
    (h.local_cubic_sylow_card X hX hXH S)
  have hd : Disjoint U X := disjoint_of_coprime_natCard (by rw [hU,hX]; decide)
  have hZU := h.local_cubic_sylow_line X hXH S
  have hZX : zpowers z≤Subgroup.centralizer (X:Set G) :=
    zpowers_le.mpr (fun x hx=>mem_centralizer_singleton_iff.mp (hXH hx))
  apply le_antisymm
  · intro g hg
    have hgC : g∈X⊔zpowers z := h.toCentralizerHypothesis.cubic_centralizer X hX hXH ▸
      ⟨((map_subtype_le _).trans inf_le_left) hg.1,hg.2⟩
    have hp : g∈(X:Set G)*(zpowers z:Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right X (zpowers z)
        ((le_centralizer_iff.mp hZX).trans (centralizer_le_normalizer _))]
      exact hgC
    obtain ⟨x,hx,w,hw,rfl⟩ := hp
    have hxU : x∈U := by simpa using U.mul_mem hg.1 (U.inv_mem (hZU hw))
    have hx1 : x=1 := mem_bot.mp (hd.eq_bot ▸ show x∈U⊓X from ⟨hxU,hx⟩)
    change x*w∈zpowers z
    rw [hx1,one_mul]
    exact hw
  · exact le_inf hZU hZX

theorem local_cubic_sylow_square_mem_line
    (s:G) (hs:s∈((S:Subgroup (centralizer z⊓normalizer (X:Set G) : Subgroup G)).map
      (centralizer z⊓normalizer (X:Set G)).subtype)) : s^2∈zpowers z := by
  rw [←h.local_cubic_sylow_centralizer_intersection X hX hXH S]
  refine ⟨pow_mem hs 2,?_⟩
  have hn := map_subtype_le _ hs
  exact h.cubic_normalizer_square_centralizes X hX hXH s ⟨hn.2,hn.1⟩

omit hX hXH in
/-- The literal original Sylow-three consumer of the local order-eight data. -/
theorem cubic_normalizer_sylow_source (P : Sylow 3 (centralizer z))
    (S : Sylow 2 (centralizer z⊓normalizer
      (((P:Subgroup (centralizer z)).map (centralizer z).subtype):Set G) : Subgroup G)) :
    let X := (P:Subgroup (centralizer z)).map (centralizer z).subtype
    let U := (S:Subgroup (centralizer z⊓normalizer (X:Set G) : Subgroup G)).map
      (centralizer z⊓normalizer (X:Set G)).subtype
    Nat.card U=8 ∧ core z⊓U=zpowers z ∧
      U⊓Subgroup.centralizer (X:Set G)=zpowers z ∧ ∀u∈U,u^2∈zpowers z := by
  dsimp only
  let X := (P:Subgroup (centralizer z)).map (centralizer z).subtype
  have hX : Nat.card X=9 := h.cubic_sylow_image_card P
  have hXH : X≤centralizer z := map_subtype_le _
  refine ⟨?_,h.local_cubic_sylow_core_intersection X hX hXH S,
    h.local_cubic_sylow_centralizer_intersection X hX hXH S,
    h.local_cubic_sylow_square_mem_line X hX hXH S⟩
  rw [card_map_of_injective (centralizer z⊓normalizer (X:Set G)).subtype_injective]
  exact h.local_cubic_sylow_card X hX hXH S
end IsType
end Theory.GroupTheory.Recognition.UnitaryFourThree
