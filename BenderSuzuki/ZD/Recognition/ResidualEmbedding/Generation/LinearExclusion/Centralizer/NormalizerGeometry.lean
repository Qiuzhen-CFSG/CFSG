module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.InitialStructure
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.Conjugation
public import Theory.GroupTheory.SubgroupProductCard

/-!
# Involution transport, TI geometry and the local normalizer index

For the original proper PSL₂ subgroup L, the completed centralizer-closure
formula implies that any conjugator taking an involution of J=C_G(L) back
into J normalizes L. This controls normalizers of every even subgroup of J
and proves N_G(J)=N_G(L), without assuming that J has order two. It does
not prove normalizer control for arbitrary odd subgroups of J.

A nontrivial intersection of conjugate two-subgroups contains an involution.
Consequently any two-subgroup U of J normalized by N_G(L) is a TI subgroup.
In particular this applies to the actual image of O₂(J). Its normalizer
is N_G(L) whenever O₂(J) is nontrivial; that nontriviality remains the
independent source Lemma 15.4 obligation.

The marked PSL₂ Sylow root identifies O₂(M∩L) with A=⟨Z∩M⟩. The existing
normalizer product therefore gives N_M(L)=AD of order q|D|. Since the
original coset count gives |M|=q³|D|, the normalizer index and the number
of M-conjugates of each subgroup with this normalizer are q². The final
applications use J itself and the literal two-core of J, with its sole
remaining nontriviality premise explicit.

Source: GLS IV, Chapter 2, Proposition 13.1, Lemma 15.2(b,c), equation
(15E), and the opening paragraph of Lemma 15.6, in
refs/KGroup/GLS4/Chapter2.tex. These results do not assert the later
order-two or normal-closure count of Lemma 15.6.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d
local notation "L" => residualGenerated M z t
local notation "D" => residualPairStabilizer M t
local notation "A" => closure (Z ∩ (M : Set G))
local notation "J" => centralizer (L : Set G)

private theorem centralizer_le_pair : J ≤ D :=
  centralizer_residualGenerated_le_pair d.minimal.disconnected d.z_mem d.z_mem_M

/-- Conjugating an involution of J to another involution of J preserves L. -/
public theorem Context.involution_transporter_normalizes {g v : G}
    (hvJ : v ∈ J) (hv : PFAppendixIII.IsInvolution v)
    (hgvJ : MulAut.conj g v ∈ J) : g ∈ normalizer (L : Set G) := by
  have hgv := BenderSuzuki.IsInvolution.map_of_injective hv
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hvL := d.centralizer_closure (centralizer_le_pair d hvJ) hv
  have hgvL := d.centralizer_closure (centralizer_le_pair d hgvJ) hgv
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro x ⟨w, hw, rfl⟩
    rw [← hgvL]
    exact centralizerClosure_conj_mem d.minimal.disconnected g v (hvL.symm ▸ hw)
  · rw [card_map_of_injective (MulAut.conj g).injective]

/-- The even-subgroup case of the source normalizer assertion, with no order-two assumption. -/
public theorem Context.even_subgroup_normalizer_le {Y : Subgroup G}
    (hYJ : Y ≤ J) (heven : Even (Nat.card Y)) :
    normalizer (Y : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := Y) 2 heven.two_dvd
  have hvi : PFAppendixIII.IsInvolution (v : G) :=
    BenderSuzuki.IsInvolution.map_of_injective (orderOf_eq_prime_iff.mp hv).symm
      Y.subtype Subtype.val_injective
  intro g hg
  exact d.involution_transporter_normalizes (hYJ v.property) hvi
    (hYJ ((mem_normalizer_iff.mp hg v).mp v.property))

/-- The full centralizer itself has the source normalizer because its order is even. -/
public theorem Context.centralizer_normalizer_eq :
    normalizer (J : Set G) = normalizer (L : Set G) :=
  le_antisymm (d.even_subgroup_normalizer_le le_rfl d.centralizer_even)
    (normalizer_le_normalizer_centralizer L)

/-- The centralizer of every involution in J normalizes the actual L. -/
public theorem Context.involution_centralizer_le {v : G}
    (hvJ : v ∈ J) (hv : PFAppendixIII.IsInvolution v) :
    centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  intro g hg
  apply d.involution_transporter_normalizes hvJ hv
  have he : MulAut.conj g v = v := by
    rw [MulAut.conj_apply, (mem_centralizer_singleton_iff.mp hg), mul_inv_cancel_right]
  rwa [he]

/-- A nontrivial intersection supplies an involution whose transporter normalizes L. -/
public theorem Context.two_subgroup_intersection_forces_normalizer {U : Subgroup G}
    (hU : IsPGroup 2 U) (hUJ : U ≤ J) {g : G}
    (hne : U ⊓ U.conjBy g ≠ ⊥) : g ∈ normalizer (L : Set G) := by
  let H := U ⊓ U.conjBy g
  have hH : IsPGroup 2 H := hU.of_injective (inclusion inf_le_left) (inclusion_injective inf_le_left)
  have heven : Even (Nat.card H) := even_iff_two_dvd.mpr
    (hH.card_eq_or_dvd.resolve_left (fun he => hne (card_eq_one.mp he)))
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 heven.two_dvd
  have hvi : PFAppendixIII.IsInvolution (v : G) :=
    BenderSuzuki.IsInvolution.map_of_injective (orderOf_eq_prime_iff.mp hv).symm
      H.subtype Subtype.val_injective
  obtain ⟨w, hw, he⟩ := v.property.2
  have hwi : PFAppendixIII.IsInvolution w := by
    have hh := BenderSuzuki.IsInvolution.map_of_injective hvi
      (MulAut.conj g).symm.toMonoidHom (MulAut.conj g).symm.injective
    simpa only [← he, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using hh
  exact d.involution_transporter_normalizes (hUJ hw) hwi (he.symm ▸ hUJ v.property.1)

/-- Two-subgroups of J invariant under N_G(L) have trivial intersection with distinct conjugates. -/
public theorem Context.two_subgroup_ti {U : Subgroup G}
    (hU : IsPGroup 2 U) (hUJ : U ≤ J)
    (hNU : normalizer (L : Set G) ≤ normalizer (U : Set G)) (g : G) :
    U.conjBy g = U ∨ Disjoint U (U.conjBy g) := by
  by_cases hd : Disjoint U (U.conjBy g)
  · exact Or.inr hd
  · have hne : U ⊓ U.conjBy g ≠ ⊥ := fun he => hd (disjoint_iff.mpr he)
    exact Or.inl (mem_normalizer_iff_map_conj_eq.mp
      (hNU (d.two_subgroup_intersection_forces_normalizer hU hUJ hne)))

/-- Every nontrivial invariant two-subgroup of J has the source normalizer. -/
public theorem Context.two_subgroup_normalizer_eq {U : Subgroup G}
    (hU : IsPGroup 2 U) (hUJ : U ≤ J) (hne : U ≠ ⊥)
    (hNU : normalizer (L : Set G) ≤ normalizer (U : Set G)) :
    normalizer (U : Set G) = normalizer (L : Set G) := by
  apply le_antisymm _ hNU
  apply d.even_subgroup_normalizer_le hUJ
  exact even_iff_two_dvd.mpr
    (hU.card_eq_or_dvd.resolve_left (fun he => hne (card_eq_one.mp he)))

private theorem distinguished_disjoint_pair : Disjoint A D := by
  apply disjoint_def.mpr
  intro a ha hd
  by_contra hne
  have hsq : a ^ 2 = 1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      d.distinguished_elementary_card.1.exponent_dvd_p ⟨a, ha⟩)
  have hi : PFAppendixIII.IsInvolution a := ⟨hne, hsq⟩
  have hzA := (isInvolution_iff_mem_Z_in_proper_residualGenerated
    d.minimal.disconnected d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper (d.distinguished_le ha)).mp hi
  exact not_mem_Z_of_mem_residualPairStabilizer d.minimal.disconnected
    d.t_not_mem_M hd hzA

/-- The two-core of the actual PSL₂ Borel is the distinguished root subgroup. -/
public theorem Context.borel_twoCore_eq_distinguished :
    (pCore 2 (M ⊓ L : Subgroup G)).map (M ⊓ L : Subgroup G).subtype = A := by
  let B := M ⊓ L
  let P := (pCore 2 B).map B.subtype
  have hAB : A ≤ B := le_inf distinguishedClosure_le d.distinguished_le
  let : ((A).subgroupOf B).Normal := normal_subgroupOf_of_le_normalizer (by
    rw [distinguishedClosure_normalizer d.minimal.disconnected]
    exact inf_le_left)
  have hABp : IsPGroup 2 ((A).subgroupOf B) :=
    (IsPGroup.of_card d.distinguished_elementary_card.2).of_equiv
      (subgroupOfEquivOfLe hAB).symm
  have hcore : (A).subgroupOf B ≤ pCore 2 B := le_sSup ⟨inferInstance, hABp⟩
  have hAP : A ≤ P := by
    intro a ha
    exact ⟨⟨a, hAB ha⟩, hcore ha, rfl⟩
  have hPL : P ≤ L := (map_subtype_le _).trans inf_le_right
  obtain ⟨S, hS⟩ := linear_distinguishedClosure_sylow d.minimal.disconnected d.reduction
    d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.parameter d.model d.distinguished_le
  have hPp : IsPGroup 2 P := pCore_isPGroup.map _
  have hPLp : IsPGroup 2 (P.subgroupOf L) :=
    hPp.of_equiv (subgroupOfEquivOfLe hPL).symm
  have he : P.subgroupOf L = (A).subgroupOf L := by
    rw [← hS]
    apply S.is_maximal' hPLp
    rw [hS]
    exact fun _ hx => hAP hx
  apply le_antisymm _ hAP
  intro x hx
  have hx' : (⟨x, hPL hx⟩ : L) ∈ P.subgroupOf L := hx
  rw [he] at hx'
  exact hx'

/-- The source local normalizer product, with its two-core identified as A. -/
public theorem Context.point_normalizer_product :
    ((M ⊓ normalizer (L : Set G) : Subgroup G) : Set G) =
      (A : Set G) * (D : Set G) := by
  have hh := d.normalizer_pair_structure.2.1
  rwa [d.borel_twoCore_eq_distinguished] at hh

/-- The local normalizer has order q|D| before any centralizer-order conclusion. -/
public theorem Context.point_normalizer_card :
    Nat.card (M ⊓ normalizer (L : Set G) : Subgroup G) =
      2 ^ n * Nat.card D := by
  have hh := card_set_mul_mul_card_inf A D
  rw [← d.point_normalizer_product, (distinguished_disjoint_pair d).eq_bot,
    card_bot, mul_one, d.distinguished_elementary_card.2] at hh
  exact hh

/-- The local normalizer has index q² in the original point stabilizer. -/
public theorem Context.point_normalizer_index :
    (M ⊓ normalizer (L : Set G) : Subgroup G).relIndex M = (2 ^ n) ^ 2 := by
  let H := M ⊓ normalizer (L : Set G)
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) H M bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, d.point_normalizer_card,
    linear_stabilizer_card_of_degree d.action d.t_not_mem_M d.degree_and_fixed.1] at hc
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ n * Nat.card D from Nat.mul_pos (pow_pos (by decide : 0 < 2) n) Nat.card_pos)
  calc
    2 ^ n * Nat.card D * H.relIndex M = (2 ^ n) ^ 3 * Nat.card D := hc
    _ = 2 ^ n * Nat.card D * (2 ^ n) ^ 2 := by ring

omit [Finite G] d in
private theorem twoCore_normalized :
    normalizer (L : Set G) ≤ normalizer ((pCore 2 J).map (J).subtype : Set G) :=
  (normalizer_le_normalizer_centralizer L).trans
    (normalizer_le_normalizer_characteristic_image J (pCore 2 J))

omit [Finite G] d in
private theorem twoCore_ne_bot (hne : pCore 2 J ≠ ⊥) :
    (pCore 2 J).map (J).subtype ≠ ⊥ := by
  intro he
  have hi := (map_eq_bot_iff (pCore 2 J)).mp he
  apply hne
  apply bot_unique
  intro x hx
  exact Subtype.ext (hi hx)

/-- Source (15E) for the actual two-core of J, assuming only its nontriviality. -/
public theorem Context.centralizer_twoCore_normalizer_eq (hne : pCore 2 J ≠ ⊥) :
    normalizer ((pCore 2 J).map (J).subtype : Set G) = normalizer (L : Set G) :=
  d.two_subgroup_normalizer_eq (pCore_isPGroup.map _) (map_subtype_le _)
    (twoCore_ne_bot hne) twoCore_normalized

/-- The actual two-core of J is a TI subgroup, including the trivial case. -/
public theorem Context.centralizer_twoCore_ti (g : G) :
    ((pCore 2 J).map (J).subtype).conjBy g = (pCore 2 J).map (J).subtype ∨
      Disjoint ((pCore 2 J).map (J).subtype) (((pCore 2 J).map (J).subtype).conjBy g) :=
  d.two_subgroup_ti (pCore_isPGroup.map _) (map_subtype_le _) twoCore_normalized g

/-- Count literal M-conjugate subgroups using the established local index. -/
public theorem Context.conjugates_card_of_normalizer_eq {U : Subgroup G}
    (hN : normalizer (U : Set G) = normalizer (L : Set G)) :
    Nat.card (Set.range fun m : M => U.conjBy (m : G)) = (2 ^ n) ^ 2 := by
  let : MulAction M (Subgroup G) :=
    MulAction.compHom (Subgroup G) (MulAut.conj.comp M.subtype)
  have hstab : MulAction.stabilizer M U = (normalizer (U : Set G)).subgroupOf M := by
    ext m
    exact mem_normalizer_iff_map_conj_eq.symm
  have hc : Nat.card (Set.range fun m : M => U.conjBy (m : G)) =
      (normalizer (U : Set G)).relIndex M := by
    change Nat.card (MulAction.orbit M U) = _
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer M U), hstab]
    rfl
  rw [hc, hN, ← inf_relIndex_left]
  exact d.point_normalizer_index

/-- The actual nontrivial two-core of J has exactly q² conjugates under M. -/
public theorem Context.centralizer_twoCore_conjugates_card (hne : pCore 2 J ≠ ⊥) :
    Nat.card (Set.range fun m : M => ((pCore 2 J).map (J).subtype).conjBy (m : G)) =
      (2 ^ n) ^ 2 :=
  d.conjugates_card_of_normalizer_eq (d.centralizer_twoCore_normalizer_eq hne)

/-- The original centralizer has exactly q² M-conjugates, with no assumption on its two-core. -/
public theorem Context.centralizer_conjugates_card :
    Nat.card (Set.range fun m : M => (J).conjBy (m : G)) = (2 ^ n) ^ 2 :=
  d.conjugates_card_of_normalizer_eq d.centralizer_normalizer_eq

end BenderSuzuki.ZD.LinearExclusion
