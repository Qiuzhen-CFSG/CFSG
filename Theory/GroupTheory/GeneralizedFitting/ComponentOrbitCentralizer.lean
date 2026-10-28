module
public import Theory.GroupTheory.GeneralizedFitting.ComponentCentralizerCore
public import Theory.GroupTheory.GeneralizedFitting.ComponentLayerStructure
public import FeitThompson.FinalTheorem

/-!
# Centralizers and closure of a component orbit

An ordinary component outside a prescribed conjugate orbit commutes with
every component in that orbit. This gives prime-core freeness of the orbit
centralizer when the ambient prime core is trivial, without assuming that
the orbit is normal.

If the orbit centralizer has odd order, no component can lie outside the
orbit, by odd-order solvability. The orbit is then the whole component
layer, hence normal, and its centralizer is exactly the odd core. A perfect
actor inducing inner automorphisms of that orbit therefore lies in it.
These conclusions concern the whole orbit, which may have several factors.

Source: Aschbacher–Smith, 4.4.10–11, printed p.621.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- An ordinary component is a prescribed orbit factor or centralizes the
entire orbit. -/
theorem IsComponent.conjugate_or_le_orbit_centralizer
    {K D : Subgroup G} (hK : IsComponent G K) (hD : IsComponent G D)
    (A : Subgroup G) :
    (∃ a : A, D = K.map (MulAut.conj (a : G)).toMonoidHom) ∨
      D ≤ centralizer (componentOrbit K A : Set G) := by
  classical
  by_cases he : ∃ a : A, D = K.map (MulAut.conj (a : G)).toMonoidHom
  · exact Or.inl he
  · right
    apply le_centralizer_iff.mpr
    apply iSup_le
    intro a
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (hD.commutator_eq_bot_of_ne (hK.map_conj (a : G)) (fun h => he ⟨a,h⟩)))

/-- Trivial ambient prime core passes to the centralizer of any component
orbit, even when that orbit is not normal. -/
theorem IsComponent.orbit_centralizer_pCore_eq_bot_of_pCore_eq_bot
    {K : Subgroup G} (hK : IsComponent G K) (A : Subgroup G)
    (p : ℕ) [Fact p.Prime] (hcore : pCore p G = ⊥) :
    pCore p (centralizer (componentOrbit K A : Set G)) = ⊥ := by
  let J := componentOrbit K A
  let C := centralizer (J : Set G)
  let R := fittingSubgroup G
  let P := C.pCoreIn p
  have hRC : R ≤ C := by
    apply le_centralizer_iff.mpr
    exact iSup_le fun a => (hK.map_conj (a : G)).le_centralizer_of_solvable_normal R
  have hcop : Nat.Coprime p (Nat.card (R.subgroupOf C)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRC).toEquiv]
    exact Nat.Coprime.of_dvd_right (card_dvd_of_le
      (fitting_le_pPrimeCore_of_pCore_eq_bot p hcore)) pPrimeCore_coprime_card
  have hd : Disjoint (pCore p C) (R.subgroupOf C) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := p) (G := C)).exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact hcop.pow_left n
  have hf : P ≤ centralizer (R : Set G) := by
    have he : ⁅pCore p C,R.subgroupOf C⁆ = ⊥ := le_bot_iff.mp
      ((commutator_le_inf _ _).trans hd.le_bot)
    have hh := congrArg (Subgroup.map C.subtype) he
    rw [map_commutator,map_subgroupOf_eq_of_le hRC,Subgroup.map_bot] at hh
    exact commutator_eq_bot_iff_le_centralizer.mp hh
  have hb : P = ⊥ := by
    by_contra hn
    obtain ⟨D,hD,hm⟩ := exists_component_moved_of_centralizes_fitting p P
      (isPGroup_pCoreIn p C) hn hcore hf
    apply hm
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rcases hK.conjugate_or_le_orbit_centralizer hD A with ⟨a,rfl⟩ | hDC
    · exact (le_iSup (fun a : A => K.map (MulAut.conj (a : G)).toMonoidHom) a).trans
        (le_centralizer_iff.mp (pCoreIn_le p C))
    · let : Group.IsNilpotent (pCore p C) := pCore_isNilpotent
      have hc : D.subgroupOf C ≤ centralizer (pCore p C : Set C) :=
        (hD.subgroupOf hDC).le_centralizer_of_solvable_normal (pCore p C)
      intro d hd x hx
      obtain ⟨w,hw,rfl⟩ := hx
      exact congrArg Subtype.val (hc
        (show (⟨d,hDC hd⟩ : C) ∈ D.subgroupOf C from hd) w hw)
  exact ((pCore p C).map_eq_bot_iff_of_injective C.subtype_injective).mp hb

/-- Odd centralizer forces every component to be one of the actual orbit
factors. -/
theorem IsComponent.exists_conjugate_of_odd_orbit_centralizer
    {K D : Subgroup G} (hK : IsComponent G K) (hD : IsComponent G D)
    (A : Subgroup G) (ho : Odd (Nat.card (centralizer (componentOrbit K A : Set G)))) :
    ∃ a : A, D = K.map (MulAut.conj (a : G)).toMonoidHom := by
  rcases hK.conjugate_or_le_orbit_centralizer hD A with he | hc
  · exact he
  · let : IsQuasisimple D := hD.2
    let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
    let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
    exact (Group.IsPerfect.not_isSolvable D
      (_root_.odd_order_theorem D (ho.of_dvd_nat (card_dvd_of_le hc)))).elim

/-- A component orbit with odd centralizer is the entire component layer. -/
theorem IsComponent.orbit_eq_componentLayer_of_odd_centralizer
    {K : Subgroup G} (hK : IsComponent G K) (A : Subgroup G)
    (ho : Odd (Nat.card (centralizer (componentOrbit K A : Set G)))) :
    componentOrbit K A = componentLayer G := by
  apply le_antisymm
  · exact iSup_le fun a => le_sSup (hK.map_conj (a : G))
  · apply sSup_le
    intro D hD
    obtain ⟨a,rfl⟩ := hK.exists_conjugate_of_odd_orbit_centralizer hD A ho
    exact le_iSup (fun a : A => K.map (MulAut.conj (a : G)).toMonoidHom) a

/-- Odd orbit centralizer makes the whole component orbit normal. -/
theorem IsComponent.orbit_normal_of_odd_centralizer
    {K : Subgroup G} (hK : IsComponent G K) (A : Subgroup G)
    (ho : Odd (Nat.card (centralizer (componentOrbit K A : Set G)))) :
    (componentOrbit K A).Normal := by
  rw [hK.orbit_eq_componentLayer_of_odd_centralizer A ho]
  infer_instance

/-- The actual odd centralizer of the component orbit is the whole odd core. -/
theorem IsComponent.orbit_centralizer_eq_oddCore_of_odd_centralizer
    {K : Subgroup G} (hK : IsComponent G K) (A : Subgroup G)
    (ho : Odd (Nat.card (centralizer (componentOrbit K A : Set G)))) :
    centralizer (componentOrbit K A : Set G) = pPrimeCore 2 G := by
  let : (componentOrbit K A).Normal := hK.orbit_normal_of_odd_centralizer A ho
  apply le_antisymm
  · exact le_sSup ⟨inferInstance,ho.coprime_two_left⟩
  · let : Group.IsSolvable (pPrimeCore 2 G) := _root_.odd_order_theorem _
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    apply le_centralizer_iff.mpr
    exact iSup_le fun a => (hK.map_conj (a : G)).le_centralizer_of_solvable_normal _

/-- A perfect actor with inner action on an orbit of odd centralizer lies in
that orbit. -/
theorem IsComponent.perfect_actor_le_orbit_of_odd_centralizer
    {K : Subgroup G} (hK : IsComponent G K) (A : Subgroup G)
    (ho : Odd (Nat.card (centralizer (componentOrbit K A : Set G))))
    (F : Subgroup G) [Group.IsPerfect F]
    (hinner : F ≤ componentOrbit K A ⊔ centralizer (componentOrbit K A : Set G)) :
    F ≤ componentOrbit K A := by
  let J := componentOrbit K A
  let : J.Normal := hK.orbit_normal_of_odd_centralizer A ho
  let C := centralizer (J : Set G)
  let q := QuotientGroup.mk' J
  let : Group.IsSolvable C := _root_.odd_order_theorem C ho
  let : Group.IsSolvable (C.map q) := Group.isSolvable_of_surjective (q.subgroupMap_surjective C)
  have hFQ : F.map q ≤ C.map q := by
    have hh := map_mono (f := q) hinner
    rwa [Subgroup.map_sup,QuotientGroup.map_mk'_self,bot_sup_eq] at hh
  let : Group.IsSolvable (F.map q) := Group.isSolvable_of_isSolvable_injective (inclusion_injective hFQ)
  let : Group.IsPerfect (F.map q) := Group.IsPerfect.map _
  have hb : F.map q = ⊥ := by
    by_contra hn
    let : Nontrivial (F.map q) := (nontrivial_iff_ne_bot _).mpr hn
    exact Group.IsPerfect.not_isSolvable (F.map q) inferInstance
  simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hb

end Theory.GroupTheory
