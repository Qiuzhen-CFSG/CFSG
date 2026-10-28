module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Four-groups that are Sylow in their centralizers

Suppose every Klein four-subgroup of a Sylow two-subgroup is self-centralizing
inside that Sylow subgroup. Then every ambient Klein four-group is Sylow in its
own centralizer. Choose a Sylow subgroup of the centralizer containing the
four-group and conjugate its ambient image into the specified Sylow subgroup.
The uniform hypothesis bounds that image by the conjugated four-group.

This is the Sylow-centralizer step in Aschbacher–Smith, *The Classification of
Quasithin Groups*, combined 1 March 2004 manuscript, Lemma 2.5.21, printed p.566.
The conclusion retains the literal centralizer inclusion into the ambient group.
-/

open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.FourCentralizerSylow

/-- A uniform self-centralizer bound on the four-groups of a Sylow subgroup
makes every ambient four-group Sylow in its own centralizer. -/
public theorem exists_sylow_centralizer {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G)
    (hself : ∀ V : Subgroup G, IsKleinFour V → V ≤ (P : Subgroup G) →
      (P : Subgroup G) ⊓ centralizer (V : Set G) ≤ V)
    (R : Subgroup G) (hR : IsKleinFour R) :
    ∃ Q : Sylow 2 (centralizer (R : Set G)),
      (Q : Subgroup (centralizer (R : Set G))).map
        (centralizer (R : Set G)).subtype = R := by
  let := hR
  let : IsMulCommutative R := IsKleinFour.isMulCommutative
  let C := centralizer (R : Set G)
  have hRC : R ≤ C := by
    intro r hr
    rw [mem_centralizer_iff]
    intro s hs
    exact congrArg Subtype.val (mul_comm (⟨s, hs⟩ : R) ⟨r, hr⟩)
  have hRc : IsPGroup 2 (R.subgroupOf C) := IsPGroup.of_card
    (show Nat.card (R.subgroupOf C) = 2 ^ 2 from
      (Nat.card_congr (subgroupOfEquivOfLe hRC).toEquiv).trans IsKleinFour.card_four)
  obtain ⟨Q, hQ⟩ := hRc.exists_le_sylow
  let U : Subgroup G := (Q : Subgroup C).map C.subtype
  have hRU : R ≤ U := by
    rw [← map_subgroupOf_eq_of_le hRC]
    exact map_mono hQ
  have hUC : U ≤ C := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hU : IsPGroup 2 U := Q.isPGroup'.map C.subtype
  obtain ⟨S, hS⟩ := hU.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  let e := MulAut.conj g
  have hSP : (S : Subgroup G).map e.toMonoidHom = (P : Subgroup G) :=
    congrArg Sylow.toSubgroup hg
  let V := R.map e.toMonoidHom
  let W := U.map e.toMonoidHom
  have hWP : W ≤ (P : Subgroup G) := by
    rw [← hSP]
    exact map_mono hS
  have hVW : V ≤ W := map_mono hRU
  let eR := R.equivMapOfInjective e.toMonoidHom e.injective
  have hV : IsKleinFour V := {
    card_four := (Nat.card_congr eR.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eR).symm.trans IsKleinFour.exponent_two }
  have hWC : W ≤ centralizer (V : Set G) := by
    rintro x ⟨u, hu, rfl⟩
    rw [mem_centralizer_iff]
    rintro y ⟨r, hr, rfl⟩
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      congrArg e (mem_centralizer_iff.mp (hUC hu) r hr)
  have hWV : W ≤ V := (le_inf hWP hWC).trans (hself V hV (hVW.trans hWP))
  have hUV : U.map e.toMonoidHom = R.map e.toMonoidHom := le_antisymm hWV hVW
  exact ⟨Q, map_injective e.injective hUV⟩

end Theory.GroupTheory.FourCentralizerSylow

