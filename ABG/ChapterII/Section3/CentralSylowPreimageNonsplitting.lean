module
public import ABG.ChapterII.Section1.FourSubgroupCenter
public import ABG.ChapterII.Section2.WeakCenterTransport
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Nonsplitting of central Sylow preimages

For a Sylow two-subgroup whose every Klein four meets its center, with
globally central center image N, no subgroup has a split quotient by N if
that quotient contains a Klein four subgroup. A section would lift a
Klein four disjoint from N. Sylow conjugacy moves the lift into the chosen
Sylow subgroup, contradicting its nontrivial center intersection.

This is the nonsplitting step in ABG II.3 Proposition2, article p22, and
Lemma2, article p24. The original semidihedral/wreathed wrapper supplies
the four-subgroup property; the generalized Q-group geometry also supplies
it. The later PSL2 specialization includes the field of order three and
does not restrict the order of the cyclic two-kernel.
-/

namespace ABG

private theorem klein_four_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hA : IsKleinFour A) : IsKleinFour B := by
  exact {
    card_four := (Nat.card_congr e.toEquiv).symm.trans hA.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv e.symm).trans hA.exponent_two }

private theorem ambient_four_inf_center_ne_bot
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hfour : ∀ V : Subgroup S, IsKleinFour V → V ⊓ Subgroup.center S ≠ ⊥)
    (N : Subgroup G) (hN : N = subgroupCenter (S : Subgroup G))
    (hcentral : N ≤ Subgroup.center G)
    (V : Subgroup G) (hV : IsKleinFour V) : V ⊓ N ≠ ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVtwo : IsPGroup 2 V := IsPGroup.of_card (n := 2) hV.card_four
  obtain ⟨T, hVT⟩ := hVtwo.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  have hmap : (T : Subgroup G).map (MulAut.conj g).toMonoidHom = (S : Subgroup G) :=
    congrArg (fun U : Sylow 2 G => (U : Subgroup G)) hg
  let Vg := V.map (MulAut.conj g).toMonoidHom
  have hVgS : Vg ≤ (S : Subgroup G) := by
    rw [← hmap]
    exact Subgroup.map_mono hVT
  have hVg : IsKleinFour Vg := klein_four_equiv
    (Subgroup.equivMapOfInjective V _ (MulAut.conj g).injective) hV
  have hVi : IsKleinFour (Vg.subgroupOf (S : Subgroup G)) :=
    klein_four_equiv (Subgroup.subgroupOfEquivOfLe hVgS).symm hVg
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (hfour _ hVi)
  have hxN : (x.1 : G) ∈ N := by
    rw [hN]
    exact ⟨x.1, x.2.2, rfl⟩
  obtain ⟨v, hv, hvg⟩ := x.2.1
  have hxcentral := hcentral hxN
  have hvx : v = (x.1 : G) := by
    apply (MulAut.conj g).injective
    change (MulAut.conj g).toMonoidHom v = (MulAut.conj g) (x.1 : G)
    rw [hvg]
    change (x.1 : G) = g * (x.1 : G) * g⁻¹
    rw [Subgroup.mem_center_iff.mp hxcentral g]
    simp
  intro hbot
  have hxone : (x.1 : G) = 1 := Subgroup.mem_bot.mp (hbot ▸ ⟨hvx ▸ hv, hxN⟩)
  exact hx (Subtype.ext (Subtype.ext hxone))

public theorem no_section_preimage_sylow_center_of_four
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hfour : ∀ V : Subgroup S, IsKleinFour V → V ⊓ Subgroup.center S ≠ ⊥)
    (N : Subgroup G) [N.Normal]
    (hN : N = subgroupCenter (S : Subgroup G))
    (hcentral : N ≤ Subgroup.center G) (E : Subgroup G)
    (W : Subgroup (E ⧸ N.subgroupOf E)) (hW : IsKleinFour W) :
    ¬ ∃ s : (E ⧸ N.subgroupOf E) →* E,
      (QuotientGroup.mk' (N.subgroupOf E)).comp s = MonoidHom.id _ := by
  rintro ⟨s, hs⟩
  have hleft : Function.LeftInverse (QuotientGroup.mk' (N.subgroupOf E)) s :=
    fun x => DFunLike.congr_fun hs x
  let f : (E ⧸ N.subgroupOf E) →* G := E.subtype.comp s
  have hf : Function.Injective f := E.subtype_injective.comp hleft.injective
  let V := W.map f
  have hV : IsKleinFour V := klein_four_equiv
    (Subgroup.equivMapOfInjective W f hf) hW
  apply ambient_four_inf_center_ne_bot S hfour N hN hcentral V hV
  apply le_antisymm _ bot_le
  rintro x ⟨⟨w, _hw, rfl⟩, hxN⟩
  have hszero : (QuotientGroup.mk' (N.subgroupOf E)) (s w) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hxN
  have hwone : w = 1 := (hleft w).symm.trans hszero
  simp [hwone]

public theorem no_section_preimage_sylow_center
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S)
    (N : Subgroup G) [N.Normal]
    (hN : N = subgroupCenter (S : Subgroup G))
    (hcentral : N ≤ Subgroup.center G) (E : Subgroup G)
    (W : Subgroup (E ⧸ N.subgroupOf E)) (hW : IsKleinFour W) :
    ¬ ∃ s : (E ⧸ N.subgroupOf E) →* E,
      (QuotientGroup.mk' (N.subgroupOf E)).comp s = MonoidHom.id _ :=
  no_section_preimage_sylow_center_of_four S
    (fun V hV => four_subgroup_inf_center_ne_bot hS V hV) N hN hcentral E W hW

end ABG
