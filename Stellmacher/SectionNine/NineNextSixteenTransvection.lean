module
public import Stellmacher.SectionNine.NineNextFaithfulQuotient
public import Theory.GroupAction.ElementaryEightInvolution
public import Theory.GroupAction.SubgroupQuotientCommutatorImage

/-!
# Local involutions on an order-sixteen next module

For an actual next-orbit vertex at critical distance greater than one,
suppose its neighbor module V has order sixteen. Every local element t
outside the two-core with t²=1 is a transvection on the literal quotient
V/Z: the ambient subgroup [V,⟨t⟩] joined with Z has index two over Z. No
local quotient-model premise is needed, and both ambient carriers remain.

The genuine next quotient packet gives |Z|=2, an elementary quotient of
order eight, and the exact action kernel O₂(G_vertex). Thus the specified
actor has a nonidentity involution image. An involution on an elementary
eight fixes four elements; involution rank-nullity makes its displacement
have order two. The exact quotient-conjugation commutator image formula
and the native relative-index formula transport this count to the stated
ambient subgroup quotient, preserving the actual t and V/Z.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (9.6), printed
p.53 / PDF p.43, the order-sixteen module branch. Its consumer chooses t in
the elementary terminal module's residual commutator and outside the first
core; no existence or path-offset assertion is assumed by this calculation.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem nine_next_involution_transvection_of_card_sixteen
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (vertex : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep vertex)
    (hcard : Nat.card (VAt ctx.Γ vertex) = 16)
    (t : G) (ht : t ∈ GAt ctx.Γ vertex) (houtside : t ∉ QAt ctx.Γ vertex)
    (hsquare : t ^ 2 = 1) :
    QuotientCardEq (⁅VAt ctx.Γ vertex,Subgroup.zpowers t⁆ ⊔ ZAt ctx.Γ vertex)
      (ZAt ctx.Γ vertex) 2 := by
  classical
  let P := GAt ctx.Γ vertex
  let V := VAt ctx.Γ vertex
  let Z := ZAt ctx.Γ vertex
  let D := Subgroup.zpowers t
  let actor : P := ⟨t,ht⟩
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v ctx.Γ vertex
  have hQP : QAt ctx.Γ vertex ≤ P := by
    change ctx.Γ.twoCoreAt vertex ≤ ctx.Γ.vertexStabilizer vertex
    rw [ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hdata := nine_next_center_commutator_and_kernel ctx hb vertex horbit
  have hZcard : Nat.card Z = 2 := hdata.1
  have hZV : Z ≤ V := hdata.2.1.symm.le.trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPV))
  obtain ⟨hN,hW,action,haction,hkernel⟩ :=
    nine_next_quotient_conjugation_action ctx hb vertex horbit
  let _ := hN
  let _ := hW
  let W := V ⧸ Z.subgroupOf V
  have hWcard : Nat.card W = 8 := by
    have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv,hZcard,
      show Nat.card V = 16 from hcard] at hprod
    change 16 = Nat.card W * 2 at hprod
    omega
  have hne : action actor ≠ 1 := by
    intro hone
    have hk : actor ∈ action.ker := MonoidHom.mem_ker.mpr hone
    rw [hkernel] at hk
    apply houtside
    change t ∈ ctx.Γ.twoCoreAt vertex
    rw [ctx.Γ.twoCoreAt_def]
    exact Subgroup.mem_map_of_mem P.subtype hk
  have hpow : (action actor) ^ 2 = 1 := by
    rw [←map_pow]
    have hp : actor ^ 2 = 1 := Subtype.ext hsquare
    rw [hp,map_one]
  let cyclic := Subgroup.zpowers (action actor)
  let generator : cyclic := ⟨action actor,Subgroup.mem_zpowers _⟩
  have hgenerator : generator ≠ 1 ∧ generator ^ 2 = 1 :=
    ⟨fun h => hne (congrArg Subtype.val h),Subtype.ext hpow⟩
  have hcyclic : Nat.card cyclic = 2 := by
    rw [Nat.card_zpowers,orderOf_eq_prime hpow hne]
  have hmove : ∃ w : W, generator • w ≠ w := by
    by_contra! hfix
    apply hne
    ext w
    exact hfix w
  have hfixed := fixed_subgroup_card_four_of_nontrivial_involution_on_eight
    generator hgenerator hcyclic hWcard hmove
  let _ : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by rw [hWcard]; decide)
  have hprod := (card_two_action_fixed_commutator_card_data
    (U := W) generator hgenerator hcyclic).1
  rw [hWcard,hfixed] at hprod
  have hdisplacement : Nat.card (commutatorAction cyclic W) = 2 := by omega
  have hDP : D ≤ P := Subgroup.zpowers_le.mpr ht
  have hDV : ⁅V,D⁆ ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hDP.trans hPV)
  have hint : D.subgroupOf P = Subgroup.zpowers actor := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hDP,MonoidHom.map_zpowers]
    rfl
  have hrel := Subgroup.quotient_conjugation_commutatorAction_card
    P V Z D hPV hDP hN action haction
  rw [hint,MonoidHom.map_zpowers] at hrel
  have hindex : Z.relIndex ⁅V,D⁆ = 2 := hrel.symm.trans hdisplacement
  have hsuprel := Subgroup.relIndex_sup_right ((⁅V,D⁆).subgroupOf V) (Z.subgroupOf V)
  rw [←Subgroup.subgroupOf_sup hDV hZV,
    Subgroup.relIndex_subgroupOf (sup_le hDV hZV),Subgroup.relIndex_subgroupOf hDV] at hsuprel
  have hsupindex : Z.relIndex (⁅V,D⁆ ⊔ Z) = 2 := hsuprel.trans hindex
  have hcount := (Z.subgroupOf (⁅V,D⁆ ⊔ Z)).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show Z ≤ ⁅V,D⁆ ⊔ Z from le_sup_right)).toEquiv] at hcount
  change Z.relIndex (⁅V,D⁆ ⊔ Z) * Nat.card Z = Nat.card (⁅V,D⁆ ⊔ Z : Subgroup G) at hcount
  rw [hsupindex] at hcount
  exact hcount.symm

end Stellmacher.SectionNine
