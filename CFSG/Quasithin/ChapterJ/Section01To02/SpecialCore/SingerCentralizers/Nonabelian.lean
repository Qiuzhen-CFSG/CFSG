module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.Basic
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility

/-!
# Nonabelian element centralizers in the Ru two-core

Assume the full-commutator assertion of J.2.3(6). Every noncentral element
centralizer then has order 256. If one were abelian, its intersection with
every L-conjugate would have at least 32 elements, hence contain an element
outside V. Both abelian subgroups would be that element's centralizer.
Thus the original centralizer would be L-invariant, contradicting
irreducibility of the literal Steinberg section S/V. Exponent dividing
four, already proved in Basic, is consequently exponent exactly four.

This is the intersecting five-dimensional images argument on printed p.434,
expressed by the equivalent subgroup-index bound inside S of order 2048.
The full-commutator premise remains with the independent J.2.3(6) producer.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma J.2.3(3),(5),(6), printed pp.433–434 (PDF pp.444–445).
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterJ.RuOne
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G} (r : RuOne L V)
include r

omit [Finite G] in
/-- Irreducibility of the genuine Steinberg section rules out an intermediate
L-invariant subgroup between V and S. -/
theorem eq_V_or_S_of_normalized (A : Subgroup G)
    (hVA : V ≤ A) (hAS : A ≤ L.pCoreIn 2) (hn : L ≤ normalizer A) :
    A = V ∨ A = L.pCoreIn 2 := by
  let F : Subrepresentation BinaryLinearThree.S := {
    toSubmodule := AddSubgroup.toZModSubmodule 2
      (((A.subgroupOf (L.pCoreIn 2)).map r.steinberg.coordinates).toAddSubgroup')
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨l, rfl⟩ := r.quotient_surjective g
      obtain ⟨a, ha, he⟩ := hv
      refine ⟨⟨l * a * (l : G)⁻¹,
        (mem_normalizer_iff.mp (r.steinberg.normalized l.property) a).mp a.property⟩,
        (mem_normalizer_iff.mp (hn l.property) a).mp ha, ?_⟩
      apply Multiplicative.toAdd.injective
      exact (r.steinberg.equivariant l a).trans (congrArg (BinaryLinearThree.S (r.quotientMap l)) he) }
  let _ : IsIrreducible BinaryLinearThree.S :=
    BinaryLinearThree.IrreducibleCatalogue.steinberg_irreducible
  rcases eq_bot_or_eq_top F with hb | ht
  · left
    apply le_antisymm _ hVA
    intro a ha
    apply (r.steinberg.coordinates_eq_one_iff ⟨a,hAS ha⟩).mp
    have hv : (r.steinberg.coordinates ⟨a,hAS ha⟩).toAdd ∈ F :=
      ⟨⟨a,hAS ha⟩,ha,rfl⟩
    rw [hb] at hv
    exact hv
  · right
    apply le_antisymm hAS
    intro s hs
    have hv : (r.steinberg.coordinates ⟨s,hs⟩).toAdd ∈ F := by
      rw [ht]; trivial
    obtain ⟨a,ha,he⟩ := hv
    change r.steinberg.coordinates a = r.steinberg.coordinates ⟨s,hs⟩ at he
    have hvker : (s * (a : G)⁻¹) ∈ V := by
      apply (r.steinberg.coordinates_eq_one_iff (⟨s,hs⟩ * a⁻¹)).mp
      rw [map_mul, map_inv, he]
      exact mul_inv_cancel (r.steinberg.coordinates ⟨s,hs⟩)
    simpa using A.mul_mem (hVA hvker) ha

omit [Finite G] in
private theorem large_intersection (A D : Subgroup G)
    (hA : A ≤ L.pCoreIn 2) (hD : D ≤ L.pCoreIn 2)
    (hAc : Nat.card A = 256) (hDc : Nat.card D = 256) :
    32 ≤ Nat.card (A ⊓ D : Subgroup G) := by
  have ha : Nat.card (A.subgroupOf (L.pCoreIn 2)) = 256 :=
    (Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv).trans hAc
  have hd : Nat.card (D.subgroupOf (L.pCoreIn 2)) = 256 :=
    (Nat.card_congr (subgroupOfEquivOfLe hD).toEquiv).trans hDc
  have hiA := (A.subgroupOf (L.pCoreIn 2)).index_mul_card
  have hiD := (D.subgroupOf (L.pCoreIn 2)).index_mul_card
  rw [ha,r.card_S] at hiA
  rw [hd,r.card_S] at hiD
  have hle := index_inf_le (H := A.subgroupOf (L.pCoreIn 2))
    (K := D.subgroupOf (L.pCoreIn 2))
  have hi := ((A ⊓ D).subgroupOf (L.pCoreIn 2)).index_mul_card
  have hic : Nat.card ((A ⊓ D).subgroupOf (L.pCoreIn 2)) =
      Nat.card (A ⊓ D : Subgroup G) :=
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hA)).toEquiv
  rw [hic,r.card_S] at hi
  have hiA' : (A.subgroupOf (L.pCoreIn 2)).index = 8 := by omega
  have hiD' : (D.subgroupOf (L.pCoreIn 2)).index = 8 := by omega
  rw [hiA',hiD'] at hle
  change ((A ⊓ D).subgroupOf (L.pCoreIn 2)).index ≤ 8 * 8 at hle
  nlinarith

/-- The intersecting five-dimensional images argument in J.2.3 proves
nonabelianness for every noncentral element centralizer. -/
theorem coreCentralizer_nonabelian
    (hfull : ∀ t : L.pCoreIn 2, (t : G) ∉ V →
      ⁅zpowers (t : G), L.pCoreIn 2⁆ = V)
    (s : L.pCoreIn 2) (hs : (s : G) ∉ V) :
    ¬ IsMulCommutative (L.pCoreIn 2 ⊓ centralizer ({(s : G)} : Set G) : Subgroup G) := by
  let C := L.pCoreIn 2 ⊓ centralizer ({(s : G)} : Set G)
  intro hab
  have hcard : Nat.card C = 256 := r.centralizer_card_of_full_commutator s (hfull s hs)
  have hcomm (x y : G) (hx : x ∈ C) (hy : y ∈ C) : x * y = y * x :=
    congrArg Subtype.val (hab.is_comm.comm ⟨x,hx⟩ ⟨y,hy⟩)
  have hn : L ≤ normalizer C := by
    intro l hl
    let f := MulAut.conj l
    let D := C.map f.toMonoidHom
    have hDS : D ≤ L.pCoreIn 2 := by
      rintro x ⟨a,ha,rfl⟩
      exact (mem_normalizer_iff.mp (r.steinberg.normalized hl) a).mp ha.1
    have hDcard : Nat.card D = 256 :=
      (card_map_of_injective f.injective).trans hcard
    have hDC (x y : G) (hx : x ∈ D) (hy : y ∈ D) : x * y = y * x := by
      obtain ⟨a,ha,rfl⟩ := hx
      obtain ⟨b,hb,rfl⟩ := hy
      simpa only [map_mul] using congrArg f.toMonoidHom (hcomm a b ha hb)
    have hlarge := r.large_intersection C D inf_le_left hDS hcard hDcard
    have hex : ∃ t ∈ C ⊓ D, t ∉ V := by
      by_contra! h
      have hle : C ⊓ D ≤ V := h
      have hc := card_le_of_le hle
      rw [r.card_V] at hc
      omega
    obtain ⟨t,ht,htV⟩ := hex
    let ct := L.pCoreIn 2 ⊓ centralizer ({t} : Set G)
    have hct : Nat.card ct = 256 :=
      r.centralizer_card_of_full_commutator ⟨t,ht.1.1⟩ (hfull ⟨t,ht.1.1⟩ htV)
    have hCct : C ≤ ct := by
      intro x hx
      exact ⟨hx.1,mem_centralizer_singleton_iff.mpr (hcomm x t hx ht.1)⟩
    have hDct : D ≤ ct := by
      intro x hx
      exact ⟨hDS hx,mem_centralizer_singleton_iff.mpr (hDC x t hx ht.2)⟩
    have hCe : C = ct := eq_of_le_of_card_ge hCct (by rw [hcard,hct])
    have hDe : D = ct := eq_of_le_of_card_ge hDct (by rw [hDcard,hct])
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hDe.trans hCe.symm
  rcases r.eq_V_or_S_of_normalized C (r.V_le_coreCentralizer s) inf_le_left hn with he | he
  · have hc := congrArg (fun K : Subgroup G => Nat.card K) he
    rw [hcard,r.card_V] at hc
    omega
  · have hc := congrArg (fun K : Subgroup G => Nat.card K) he
    rw [hcard,r.card_S] at hc
    omega

/-- The upper bound four is exact: exponent dividing two would make the
centralizer abelian, contradicting the geometric argument. -/
theorem coreCentralizer_exponent_eq_four
    (hfull : ∀ t : L.pCoreIn 2, (t : G) ∉ V →
      ⁅zpowers (t : G), L.pCoreIn 2⁆ = V)
    (s : L.pCoreIn 2) (hs : (s : G) ∉ V) :
    Monoid.exponent (L.pCoreIn 2 ⊓ centralizer ({(s : G)} : Set G) : Subgroup G) = 4 := by
  have hdiv := r.coreCentralizer_exponent_dvd_four (s : G)
  have hcases : ∀ n : ℕ, n ∣ 4 → n = 1 ∨ n = 2 ∨ n = 4 := by
    intro n hn
    have hle := Nat.le_of_dvd (by decide : 0 < 4) hn
    interval_cases n <;> norm_num at *
  rcases hcases _ hdiv with h1 | h2 | h4
  · exfalso
    apply r.coreCentralizer_nonabelian hfull s hs
    exact ⟨⟨fun a b => (Commute.of_orderOf_dvd_two (fun x =>
      (Monoid.order_dvd_exponent x).trans (by rw [h1]; exact one_dvd 2)) a b).eq⟩⟩
  · exfalso
    apply r.coreCentralizer_nonabelian hfull s hs
    exact ⟨⟨mul_comm_of_exponent_two h2⟩⟩
  · exact h4
end CFSG.Quasithin.ChapterJ.RuOne
