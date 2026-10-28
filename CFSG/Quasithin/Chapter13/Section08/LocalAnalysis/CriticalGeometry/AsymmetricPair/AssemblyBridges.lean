module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CenterOrbits
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CoverHyperplanes
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CoverSymplecticGeometry
public import CFSG.Quasithin.Chapter13.Section08.Elementary
/-!
# Action and relative-centralizer bridges for the asymmetric pair

Ambient commutators give a nonidentity transvection center in any genuine
quotient-conjugation action. In the five-dimensional cover, equality of star
images makes the actual fixed preimage centralize the transported U_H: its
commutator lies both in V₁ and in the disjoint transported center. The relative
centralizer H_C is transported by the same conjugator. The earlier abelian
V_H also supplies the centralizer-generated closure needed for 13.8.3.

Source: Aschbacher–Smith 13.8.7, printed pp.948–949, using 13.7.3(7),
13.8.2–3 and the quotient conventions of F.9.2.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
variable {G : Type*} [Group G]

/-- Ambient commutators determine the center for any genuine quotient action. -/
theorem quotient_displacement_from_commutator [Finite G]
    {H U Z A P : Subgroup G} [IsElementaryAbelian 2 U] [(Z.subgroupOf U).Normal]
    (Q : CenterQuotientAction H U Z) (hPH : P ≤ H)
    (hc : ⁅U, P⁆ = A) (hcard : Nat.card A = 2) (hdis : Z ⊓ A = ⊥) :
    (P.subgroupOf H).map Q.action ≠ ⊥ ∧
      Nat.card (commutatorAction ((P.subgroupOf H).map Q.action) (U ⧸ Z.subgroupOf U)) = 2 ∧
      commutatorAction ((P.subgroupOf H).map Q.action) (U ⧸ Z.subgroupOf U) =
        (A.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
  have he := quotient_conjugation_commutatorAction_eq_image H U Z P Q.normalizes
    hPH inferInstance Q.action Q.apply_mk
  rw [hc] at he
  have hs := quotient_conjugation_commutatorAction_card H U Z P Q.normalizes
    hPH inferInstance Q.action Q.apply_mk
  rw [hc, ← inf_relIndex_right Z A, hdis, relIndex_bot_left, hcard] at hs
  refine ⟨?_, hs, he⟩
  intro hz
  rw [hz] at hs
  -- The displacement of the trivial actor is trivial.
  have ht : commutatorAction (⊥ : Subgroup (MulAut (U ⧸ Z.subgroupOf U)))
      (U ⧸ Z.subgroupOf U) = ⊥ := by
    rw [commutatorAction_eq_closure]
    apply le_bot_iff.mp
    apply (closure_le _).mpr
    rintro x ⟨a, w, rfl⟩
    have ha : (a : MulAut (U ⧸ Z.subgroupOf U)) = 1 := mem_bot.mp a.property
    change w⁻¹ * (a : MulAut (U ⧸ Z.subgroupOf U)) w ∈ _
    simp [ha]
  rw [ht] at hs
  simp at hs

/-- The ambient line is a nontrivial center for the actual H-action. -/
theorem nontrivialCenter_of_commutator [Finite G]
    {H U Z A P : Subgroup G} [IsElementaryAbelian 2 U] [(Z.subgroupOf U).Normal]
    (Q : CenterQuotientAction H U Z) (hPH : P ≤ H)
    (hc : ⁅U, P⁆ = A) (hcard : Nat.card A = 2) (hdis : Z ⊓ A = ⊥) :
    Q.IsNontrivialCenter A := by
  obtain ⟨hn, _, he⟩ := quotient_displacement_from_commutator Q hPH hc hcard hdis
  exact Q.isNontrivialCenter_of_displacement (P.subgroupOf H) A hn he.le

/-- A nonidentity actor inducing a transvection, as required by 13.8.5. -/
theorem transvection_actor_of_commutator [Finite G]
    {H U Z A P : Subgroup G} [IsElementaryAbelian 2 U] [(Z.subgroupOf U).Normal]
    (Q : CenterQuotientAction H U Z) (hPH : P ≤ H)
    (hc : ⁅U, P⁆ = A) (hcard : Nat.card A = 2) (hdis : Z ⊓ A = ⊥) :
    ∃ t : H, Q.action t ≠ 1 ∧ binaryLinear (Q.action t) ∈
      LinearEquiv.transvections (ZMod 2) (Additive (U ⧸ Z.subgroupOf U)) := by
  obtain ⟨hn, hs, _⟩ := quotient_displacement_from_commutator Q hPH hc hcard hdis
  obtain ⟨a, ha, hna⟩ : ∃ a ∈ (P.subgroupOf H).map Q.action, a ≠ 1 := by
    by_contra! h
    exact hn (eq_bot_iff.mpr h)
  obtain ⟨t, ht, rfl⟩ := ha
  exact ⟨t, hna, transvections_of_displacement_card_two
    ((P.subgroupOf H).map Q.action) hs (Q.action t) (mem_map_of_mem Q.action ht)⟩

/-- The earlier abelian V_H gives the actual centralizer-generated closure. -/
theorem centralizerClosure_abelian {H V : Subgroup G} {z : G}
    (hH : H = centralizer ({z} : Set G)) [IsMulCommutative (Source.VH H V)] :
    IsMulCommutative (centralizerConjugateClosure V z) := by
  have hle : centralizerConjugateClosure V z ≤ Source.VH H V := by
    apply iSup_le
    rintro c x ⟨v, hv, rfl⟩
    exact subset_closure ⟨c, hH ▸ c.property, v, hv, rfl⟩
  apply commutator_self_eq_bot_iff.mp
  apply le_bot_iff.mp
  exact (commutator_mono hle hle).trans
    (commutator_self_eq_bot_iff.mpr inferInstance).le

/-- Centralizing the transported U_H, inside its vertex group, is precisely
membership in the transported relative centralizer H_C. -/
theorem le_conjugate_HC {H C E : Subgroup G} (g : G)
    (hEH : E ≤ H.conjBy g)
    (hc : ⁅E, (Source.UH H C).conjBy g⁆ = ⊥) :
    E ≤ (Source.HC H C).conjBy g := by
  have hi : E.conjBy g⁻¹ ≤ H := by
    have hi := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hEH
    change E.conjBy g⁻¹ ≤ (H.conjBy g).conjBy g⁻¹ at hi
    rwa [conjBy_inv] at hi
  have hci : ⁅E.conjBy g⁻¹, Source.UH H C⁆ = ⊥ := by
    have hh := congrArg (fun X : Subgroup G => X.map (MulAut.conj g⁻¹).toMonoidHom) hc
    rw [map_commutator, Subgroup.map_bot] at hh
    change ⁅E.conjBy g⁻¹, ((Source.UH H C).conjBy g).conjBy g⁻¹⁆ = ⊥ at hh
    rwa [conjBy_inv] at hh
  have hle : E.conjBy g⁻¹ ≤ Source.HC H C :=
    le_inf hi (commutator_eq_bot_iff_le_centralizer.mp hci)
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hle
  change (E.conjBy g⁻¹).conjBy g ≤ (Source.HC H C).conjBy g at hh
  rwa [conjBy_inv'] at hh

namespace CoverHyperplanes.CoverCoordinates
variable {H C Z : Subgroup G} [IsElementaryAbelian 2 (Source.UH H C)]
  [(Z.subgroupOf (Source.UH H C)).Normal]
variable (d : CoverCoordinates H C Z)

/-- The fixed preimage retains its ambient carrier U_H. -/
theorem fixedPreimage_le (B : Subgroup G) : d.fixedPreimage B ≤ Source.UH H C := by
  rintro x ⟨u, _, rfl⟩
  exact u.property

/-- Fixing the coordinate image means the actual commutator lies in V₁. -/
theorem commutator_fixedPreimage_le (P B : Subgroup G) (hPH : P ≤ H)
    (he : Source.starImage H P = Source.starImage H B) :
    ⁅P, d.fixedPreimage B⁆ ≤ Z := by
  apply commutator_le.mpr
  intro p hp u hu
  let ph : H := ⟨p, hPH hp⟩
  let uu : Source.UH H C := ⟨u, d.fixedPreimage_le B hu⟩
  have hf := (d.mem_fixedPreimage B uu).mp hu
  have hp' : d.groupEquiv (QuotientGroup.mk' (pCore 2 H) ph) ∈ d.modelImage B := by
    apply (d.mem_modelImage B _).mpr
    have hi : QuotientGroup.mk' (pCore 2 H) ph ∈ Source.starImage H B :=
      he ▸ mem_map_of_mem (QuotientGroup.mk' (pCore 2 H)) hp
    obtain ⟨b, hb, heq⟩ := hi
    exact ⟨b, hb, congrArg d.groupEquiv heq⟩
  have hh := hf _ hp'
  change act _ (d.linearEquiv (Additive.ofMul (QuotientGroup.mk' _ uu))) =
    d.linearEquiv (Additive.ofMul (QuotientGroup.mk' _ uu)) at hh
  rw [d.intertwines ph uu] at hh
  have hquot := d.linearEquiv.injective hh
  have hd := QuotientGroup.eq_iff_div_mem.mp hquot
  change (p * u * p⁻¹) / u ∈ Z at hd
  simpa only [div_eq_mul_inv, commutatorElement_def] using hd

/-- The common center and fixed-space bounds force genuine centralization. -/
theorem fixedPreimage_centralizes (P B A : Subgroup G) (hPH : P ≤ H)
    (he : Source.starImage H P = Source.starImage H B)
    (hc : ⁅Source.UH H C, P⁆ = A) (hdis : Z ⊓ A = ⊥) :
    ⁅P, d.fixedPreimage B⁆ = ⊥ := by
  apply le_bot_iff.mp
  rw [← hdis]
  refine le_inf (d.commutator_fixedPreimage_le P B hPH he) ?_
  rw [← hc, commutator_comm (Source.UH H C) P]
  exact commutator_mono le_rfl (d.fixedPreimage_le B)
end CoverHyperplanes.CoverCoordinates
end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
end
