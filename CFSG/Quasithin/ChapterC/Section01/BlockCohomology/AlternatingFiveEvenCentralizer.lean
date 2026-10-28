module
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveCentralizer
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import Theory.GroupTheory.CharacteristicPGroupExtension
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# A large normalizing Sylow forces an even deleted-block centralizer

Let B be a deleted alternating-five block normal in G, with G/B a two-group.
If C_G(B) has odd order, the projective module split makes O₂(G) equal to
the actual elementary layer U(B), of order sixteen. Characteristic-two
inheritance makes this core self-centralizing. Conjugation on the core has
kernel contained in that core and image in GL₄(2), so |G| divides 322560.

Applying this to the literal join B S proves that a Sylow normalizing B
has even block centralizer whenever its order does not divide 322560.
The block's core may initially be larger than its layer: the odd-centralizer
argument proves the collapse and does not assume it. No local-component,
Sylow-order bound, or normalizer-control premise is added.

Source: Aschbacher–Smith C.1.13(c), printed pp.124–125; application to
original 10.2.1, printed p.743, and the J₄ involution-centralizer rows.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- An odd block centralizer bounds a normal two-extension by the actual
order-sixteen layer and its full linear automorphism group. -/
theorem IsAlternatingBlock.normal_extension_card_dvd_of_odd_centralizer
    (B : Subgroup G) [B.Normal] (hB : IsAlternatingBlock B 5)
    (hq : IsPGroup 2 (G ⧸ B)) (hodd : Odd (Nat.card (centralizer (B : Set G)))) :
    Nat.card G ∣ 322560 := by
  let U := (blockU B).map B.subtype
  have hU : U ≤ pCore 2 G :=
    le_sSup ⟨inferInstance, (pCore_isPGroup.to_le blockU_le_core).map B.subtype⟩
  have hcomm : ⁅B, pCore 2 G⁆ ≤ B.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes
      (pCore_isPGroup.to_le (le_normalizer_iff_commutator_le_right.mp
        (show B ≤ normalizer (pCore 2 G : Set G) from le_normalizer_of_normal)))
      (le_normalizer_iff_commutator_le_left.mp
        (show pCore 2 G ≤ normalizer (B : Set G) from le_normalizer_of_normal))
      (normalizer_commutator_ge_left B (pCore 2 G))
  have hsplit := hB.two_subgroup_eq_module_sup_centralizer pCore_isPGroup
    (show B ≤ normalizer (pCore 2 G : Set G) from le_normalizer_of_normal) hU hcomm
  have hdis : Disjoint (pCore 2 G) (centralizer (B : Set G)) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_left.mpr hodd).pow_left n
  have hcore : pCore 2 G = U := by
    simpa only [hdis.eq_bot, sup_bot_eq] using hsplit
  have hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G :=
    centralizer_pCore_le_of_normal_pGroup_quotient 2 B
      ((centralizer_le blockU_le_core).trans_eq hB.2.1.centralizer_blockU) hq
  let := hB.2.1.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map B.subtype
  let : IsElementaryAbelian 2 (pCore 2 G) := hcore ▸ (inferInstance : IsElementaryAbelian 2 U)
  have hcard : Nat.card (pCore 2 G) = 16 := by
    rw [hcore, card_map_of_injective B.subtype_injective, hB.blockU_card]
  have hAut : Nat.card (MulAut (pCore 2 G)) = 20160 := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow (pCore 2 G) 4 (by simpa using hcard)]
    decide
  let a : G →* MulAut (pCore 2 G) := MulAut.conjNormal
  have hk : a.ker ≤ pCore 2 G := by
    intro x hx
    apply hc
    intro q hq
    have hh := congrArg (fun f : MulAut (pCore 2 G) => (f ⟨q,hq⟩ : G))
      (MonoidHom.mem_ker.mp hx)
    change x*q*x⁻¹=q at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hkcard : Nat.card a.ker ∣ 16 := hcard ▸ card_dvd_of_le hk
  have hr : Nat.card a.range ∣ 20160 := hAut ▸ a.range.card_subgroup_dvd_card
  have he := a.ker.card_mul_index
  rw [index_ker] at he
  rw [←he]
  exact Nat.mul_dvd_mul hkcard hr

/-- The original normalizing Sylow forces even centralizer when its order
cannot occur in the normal deleted-block extension. -/
theorem IsAlternatingBlock.even_centralizer_of_normalizing_sylow_card
    (S : Sylow 2 G) (B : Subgroup G) (hB : IsAlternatingBlock B 5)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hsize : ¬ Nat.card S ∣ 322560) : 2 ∣ Nat.card (centralizer (B : Set G)) := by
  by_contra ho
  have hodd : Odd (Nat.card (centralizer (B : Set G))) :=
    Nat.not_even_iff_odd.mp (fun hh => ho hh.two_dvd)
  let H := B ⊔ (S : Subgroup G)
  let B' := B.subgroupOf H
  let : B'.Normal := normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hn)
  have hgen : B' ⊔ (S : Subgroup G).subgroupOf H = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le le_sup_right,
      ← MonoidHom.range_eq_map,range_subtype]
  have hq : IsPGroup 2 (H ⧸ B') := isPGroup_quotient_of_sup_eq_top B'
    ((S : Subgroup G).subgroupOf H) S.isPGroup'.comap_subtype hgen
  have hB' : IsAlternatingBlock B' 5 := RankOne.Solvable.isAlternatingBlock_of_equiv
    (subgroupOfEquivOfLe (show B ≤ H from le_sup_left)).symm hB
  let f : centralizer (B' : Set H) →* centralizer (B : Set G) :=
    { toFun := fun x => ⟨x.val.val, by
        intro b hb
        exact congrArg H.subtype (x.property ⟨b,(show B ≤ H from le_sup_left) hb⟩ hb)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y hh
    exact Subtype.ext (Subtype.ext (congrArg (fun x : centralizer (B : Set G) => x.val) hh))
  have hod : Odd (Nat.card (centralizer (B' : Set H))) :=
    hodd.of_dvd_nat (card_dvd_of_injective f hf)
  have hdiv := hB'.normal_extension_card_dvd_of_odd_centralizer B' hq hod
  have hs : Nat.card S ∣ Nat.card H :=
    card_dvd_of_injective (inclusion (show (S : Subgroup G) ≤ H from le_sup_right))
      (inclusion_injective _)
  exact hsize (hs.trans hdiv)

end CFSG.Quasithin.ChapterC
