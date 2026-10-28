module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Equivalence

/-!+# The actual actors in the transvection alternative

There is a typographical problem in 13.8.8(1): the printed δ=γg_b⁻¹
equals γ₁, whereas the preceding proof uses γ₁g_b⁻¹. These vertices
are proved distinct below. The corrected formulation retains the actors
actually obtained in F.9.16(1),(3): U_H transported back by g_b⁻¹,
or the similarly transported V_H in the commuting case. If D_H is
full and Dγ is strict, the actual Uγ already supplies the actor.

The commuting case uses precisely [V_H,H_C]≤V₁ from 13.7.3(7),
and the noncentrality [Uγ,V]≰A₁ from F.9.13(5). The actions below are
the actual conjugation action on U_H/V₁, with nontrivial displacement;
in particular the identity in Mathlib's transvection set cannot be used
to trigger 13.8.5.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.8.8(1), printed p.949, and F.9.16(1),(3), printed pp.323–324.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.Reorientation
open AsymmetricPair
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
variable {G : Type*} [Group G] [Finite G] {L T H V : Subgroup G}

/-- Nontriviality concerns the action image, and every element of that image
has the genuine linear transvection formula. -/
structure TransvectionGroup {U Z : Subgroup G} [IsElementaryAbelian 2 U]
    [(Z.subgroupOf U).Normal] (Q : CenterQuotientAction H U Z) (P : Subgroup G) : Prop where
  in_H : P ≤ H
  nontrivial : (P.subgroupOf H).map Q.action ≠ ⊥
  displacement : Nat.card (commutatorAction ((P.subgroupOf H).map Q.action)
    (U ⧸ Z.subgroupOf U)) = 2
  transvections : ∀ a ∈ (P.subgroupOf H).map Q.action,
    binaryLinear a ∈ LinearEquiv.transvections (ZMod 2) (Additive (U ⧸ Z.subgroupOf U))

omit [Finite G] in
theorem TransvectionGroup.nonidentity_actor {U Z P : Subgroup G} [IsElementaryAbelian 2 U]
    [(Z.subgroupOf U).Normal] {Q : CenterQuotientAction H U Z}
    (h : TransvectionGroup Q P) :
    ∃ t : H, (t : G) ∈ P ∧ Q.action t ≠ 1 ∧ binaryLinear (Q.action t) ∈
      LinearEquiv.transvections (ZMod 2) (Additive (U ⧸ Z.subgroupOf U)) := by
  obtain ⟨a, ha, hn⟩ : ∃ a ∈ (P.subgroupOf H).map Q.action, a ≠ 1 := by
    by_contra! hn
    exact h.nontrivial (eq_bot_iff.mpr hn)
  obtain ⟨t, ht, rfl⟩ := ha
  exact ⟨t, ht, hn, h.transvections _ (mem_map_of_mem Q.action ht)⟩

theorem transvectionGroup_of_commutator {U Z A P : Subgroup G} [IsElementaryAbelian 2 U]
    [(Z.subgroupOf U).Normal] (Q : CenterQuotientAction H U Z)
    (hP : P ≤ H) (hc : ⁅U, P⁆ = A) (hcard : Nat.card A = 2) (hdis : Z ⊓ A = ⊥) :
    TransvectionGroup Q P := by
  obtain ⟨hn, hs, _⟩ := quotient_displacement_from_commutator Q hP hc hcard hdis
  exact ⟨hP, hn, hs, transvections_of_displacement_card_two _ hs⟩

/-- The full conjugate span at the corrected vertex g_b⁻¹γ₁. -/
def Valpha (c : CriticalPair L T H V) : Subgroup G :=
  (Source.VH H V).map (MulAut.conj (returnElement c : G)).toMonoidHom

omit [Finite G] in
theorem printed_delta_eq_base (c : CriticalPair L T H V) :
    returnElement c • c.gamma = base L T H true := returnElement_gamma c

omit [Finite G] in
/-- Under the source length bound, the corrected δ cannot equal the printed δ. -/
theorem corrected_delta_ne_printed (c : CriticalPair L T H V) (hb : 3 ≤ c.path.length) :
    alpha c ≠ returnElement c • c.gamma := by
  intro he
  have hg : base L T H true = c.gamma :=
    (MulAction.injective (returnElement c)) he
  have hd : (graph L T H).dist (base L T H false) c.gamma = 1 := by
    rw [← hg]
    exact (SimpleGraph.dist_eq_one_iff_adj).mpr
      ⟨Bool.false_ne_true, CosetGeometry.incident_base _ _ _⟩
  have hh := c.distance_eq
  omega

private theorem eq_line_of_nontrivial_le (A Z : Subgroup G)
    (hZ : Nat.card Z = 2) (hAZ : A ≤ Z) (hne : A ≠ ⊥) : A = Z := by
  have hd : Nat.card A ∣ 2 := hZ ▸ card_dvd_of_le hAZ
  have hc : Nat.card A = 2 := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
    (fun h => hne (card_eq_one.mp h))
  exact eq_of_le_of_card_ge hAZ (by rw [hc, hZ])

private theorem returned_transvection
    (c : CriticalPair L T H V) (V₃ Z P : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [(Z.subgroupOf (Source.UH H V₃)).Normal]
    (Q : CenterQuotientAction H (Source.UH H V₃) Z)
    (hP : P ≤ vertexGroup L T H c.gamma) (hcomm : ⁅P, c.Ugamma V₃⁆ = Z)
    (hcard : Nat.card Z = 2) (hdis : Z ⊓ c.Aone Z = ⊥) :
    TransvectionGroup Q (P.map (MulAut.conj (returnElement c : G)).toMonoidHom) := by
  have hc := congrArg (fun X : Subgroup G =>
    X.map (MulAut.conj (returnElement c : G)).toMonoidHom) hcomm
  have hU : (c.Ugamma V₃).map (MulAut.conj (returnElement c : G)).toMonoidHom =
      Source.UH H V₃ := conjBy_inv (Source.UH H V₃) (c.gb : G)
  rw [map_commutator, hU, commutator_comm] at hc
  have hA : (c.Aone Z).map (MulAut.conj (returnElement c : G)).toMonoidHom = Z :=
    conjBy_inv Z (c.gb : G)
  have hd := congrArg (fun X : Subgroup G =>
    X.map (MulAut.conj (returnElement c : G)).toMonoidHom) hdis
  rw [map_inf _ _ _ (MulAut.conj _).injective, hA, Subgroup.map_bot, inf_comm] at hd
  exact transvectionGroup_of_commutator Q (return_conjugate_le_H c P hP) hc
    (by rw [card_map_of_injective (MulAut.conj _).injective, hcard]) hd

/-- The full-right-denominator branch. In F.9.16(1ii), the seed actor
enlarges to the full Vα using the earlier centralizer bound 13.7.3(7). -/
theorem transvection_of_Dgamma_eq
    (c : CriticalPair L T H V) (V₃ Z : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [(Z.subgroupOf (Source.UH H V₃)).Normal]
    (Q : CenterQuotientAction H (Source.UH H V₃) Z)
    (hV₃ : V₃ ≤ V) (hZ : H ≤ normalizer (Z : Set G))
    (hcard : Nat.card Z = 2) (hγH : c.Ugamma V₃ ≤ H)
    (hVHend : Source.VH H V ≤ vertexGroup L T H c.gamma)
    (hUA : Source.UH H V₃ ≤ normalizer (c.Aone Z : Set G))
    (hdis : Z ⊓ c.Aone Z = ⊥)
    (hcentral : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ Z)
    (hbad : ¬ ⁅c.Ugamma V₃, V⁆ ≤ c.Aone Z)
    (hfull : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z = c.Ugamma V₃) :
    TransvectionGroup Q (Ualpha c V₃) ∨ TransvectionGroup Q (Valpha c) := by
  by_cases hs : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z) < Source.UH H V₃
  · exact Or.inl (returned_transvection c V₃ Z (Source.UH H V₃) Q
      ((conjugateSpanBy_mono hV₃ le_rfl).trans hVHend)
      (commutator_eq_line_of_asymmetry _ _ _ _ hcard (hγH.trans hZ) hs hfull) hcard hdis)
  have he := eq_of_le_of_not_lt (commutatorPreimage_le (Source.UH H V₃)
    (c.Ugamma V₃) (c.Aone Z)) hs
  have hA : ⁅Source.UH H V₃, c.Ugamma V₃⁆ ≤ c.Aone Z := by
    conv_lhs => lhs; rw [← he]
    exact commutator_commutatorPreimage_le _ _ _ hUA
  have hC : ⁅Source.UH H V₃, c.Ugamma V₃⁆ ≤ Z := by
    rw [commutator_comm]
    conv_lhs => lhs; rw [← hfull]
    exact commutator_commutatorPreimage_le _ _ _ (hγH.trans hZ)
  have hcomm : ⁅Source.UH H V₃, c.Ugamma V₃⁆ = ⊥ :=
    le_bot_iff.mp ((le_inf hC hA).trans hdis.le)
  have hUgC : c.Ugamma V₃ ≤ Source.HC H V₃ := by
    refine le_inf hγH (commutator_eq_bot_iff_le_centralizer.mp ?_)
    rw [commutator_comm]
    exact hcomm
  have hVC : ⁅Source.VH H V, c.Ugamma V₃⁆ = Z := by
    apply eq_line_of_nontrivial_le _ Z hcard ((commutator_mono le_rfl hUgC).trans hcentral)
    intro he
    apply hbad
    rw [commutator_comm]
    exact (commutator_mono (le_conjugateSpanBy V H) le_rfl).trans (he.le.trans bot_le)
  exact Or.inr (returned_transvection c V₃ Z (Source.VH H V) Q
    hVHend hVC hcard hdis)

/-- In the other asymmetric orientation, Uγ itself acts nontrivially on Ũ_H. -/
theorem transvection_of_DH_eq_Dgamma_lt
    (c : CriticalPair L T H V) (V₃ Z : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [(Z.subgroupOf (Source.UH H V₃)).Normal]
    (Q : CenterQuotientAction H (Source.UH H V₃) Z)
    (hcard : Nat.card Z = 2) (hγH : c.Ugamma V₃ ≤ H)
    (hUA : Source.UH H V₃ ≤ normalizer (c.Aone Z : Set G))
    (hdis : Z ⊓ c.Aone Z = ⊥)
    (hfull : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z) = Source.UH H V₃)
    (hstrict : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z < c.Ugamma V₃) :
    TransvectionGroup Q (c.Ugamma V₃) := by
  have hsize : Nat.card (c.Aone Z) = 2 := by
    rw [CriticalPair.Aone, card_map_of_injective (MulAut.conj _).injective, hcard]
  have hc := commutator_eq_line_of_asymmetry (c.Ugamma V₃) (Source.UH H V₃)
    (c.Aone Z) Z hsize hUA hstrict hfull
  rw [commutator_comm] at hc
  exact transvectionGroup_of_commutator Q hγH hc hsize hdis

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.Reorientation
end
