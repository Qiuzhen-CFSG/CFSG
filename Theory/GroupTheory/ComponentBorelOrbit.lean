module
public import Theory.GroupTheory.ComponentLocalDirectPowerSection
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
/-!
# Odd quotients of invariant local component orbits

Conjugates of a local subgroup in distinct components commute. If the seed
has self-centralizing two-core, its orbit has the same property; its quotient
by the full two-core is a finite direct power of the seed quotient. In
particular an odd seed quotient gives an odd orbit quotient. The relative
version preserves the literal inclusion into a larger ambient group.

Source application: Aschbacher--Smith 15.1.20, the orbit Borel on printed
p.1094, using the component calculus of A.3.3.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Characteristic two and odd core quotient pass to an invariant local orbit. -/
theorem IsComponent.local_orbit_fitting_odd
    {L B A : Subgroup G} (hL : IsComponent G L) (hBL : B ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (B : Set G))
    (hself : centralizer (pCore 2 B : Set B) ≤ pCore 2 B)
    (ho : Odd (Nat.card (B ⧸ pCore 2 B))) :
    generalizedFitting (componentOrbit B A) = pCore 2 (componentOrbit B A) ∧
      Odd (Nat.card (componentOrbit B A ⧸ pCore 2 (componentOrbit B A))) := by
  let D := componentOrbit B A
  let Q := componentOrbit (B.pCoreIn 2) A
  obtain ⟨hQ,hQD,hnQ⟩ := hL.local_core_orbit (p := 2) hBL hinv
  have hQcore : Q ≤ D.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hQ hQD ((componentOrbit_le_sup B A).trans hnQ)
  have hc : D ⊓ centralizer (D.pCoreIn 2 : Set G) ≤ D.pCoreIn 2 :=
    (inf_le_inf_left D (centralizer_le hQcore)).trans
      ((hL.local_orbit_centralizer hBL hinv
        ((inf_centralizer_pCoreIn_le_iff 2 B).mpr hself)).trans hQcore)
  refine ⟨generalizedFitting_eq_pCore_of_selfCentralizing 2
    ((inf_centralizer_pCoreIn_le_iff 2 D).mp hc),?_⟩
  obtain ⟨n,⟨e⟩⟩ := hL.local_orbit_quotient_core_equiv_power hBL hinv hself
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_fin]
  exact ho.pow

/-- The same orbit calculation for a component of a specified ambient subgroup. -/
theorem IsComponent.relative_local_orbit_fitting_odd
    {H L B A : Subgroup G} (hL : IsComponent H (L.subgroupOf H))
    (hLH : L ≤ H) (hBL : B ≤ L) (hAH : A ≤ H)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (B : Set G))
    (hself : centralizer (pCore 2 B : Set B) ≤ pCore 2 B)
    (ho : Odd (Nat.card (B ⧸ pCore 2 B))) :
    generalizedFitting (componentOrbit B A) = pCore 2 (componentOrbit B A) ∧
      Odd (Nat.card (componentOrbit B A ⧸ pCore 2 (componentOrbit B A))) := by
  let B0 := B.subgroupOf H
  let A0 := A.subgroupOf H
  let e : B0 ≃* B := subgroupOfEquivOfLe (hBL.trans hLH)
  have hinv0 : A0 ⊓ normalizer (L.subgroupOf H : Set H) ≤ normalizer (B0 : Set H) := by
    rw [←subgroupOf_normalizer_eq hLH, ←subgroupOf_normalizer_eq (hBL.trans hLH)]
    exact fun _ hx => hinv hx
  have hc0 := (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr hself
  have ho0 : Odd (Nat.card (B0 ⧸ pCore 2 B0)) := by
    rwa [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
  obtain ⟨hf,hod⟩ := hL.local_orbit_fitting_odd (subgroupOf_mono H hBL) hinv0 hc0 ho0
  have hm : (componentOrbit B0 A0).map H.subtype = componentOrbit B A := by
    rw [map_componentOrbit, map_subgroupOf_eq_of_le (hBL.trans hLH),
      map_subgroupOf_eq_of_le hAH]
  let f := (equivMapOfInjective (componentOrbit B0 A0) H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hm)
  refine ⟨?_,?_⟩
  · have hh := congrArg (Subgroup.map f.toMonoidHom) hf
    rw [map_generalizedFitting_equiv f, pCore_map_iso 2 f] at hh
    exact hh
  · rwa [←Nat.card_congr (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).toEquiv]

end Theory.GroupTheory
