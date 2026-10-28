module
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# Two-components and ordinary components

A two-component is a C-component whose quotient by its intrinsic odd core
is quasisimple. The definition uses the shared A.3 C-component API.

Subnormal monotonicity places the intrinsic odd core inside the ambient
odd core. Consequently a two-component centralizing the ambient odd core
is a perfect central cover of a quasisimple group and is ordinary. Ordinary
components are two-components when their odd cores are solvable; the finite
case is discharged by the odd order theorem in the source consumer.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, I.3,
p.414; GLS II, Proposition 4.7 and Lemma 4.11.
-/

@[expose] public section
open Subgroup Theory.GroupTheory

namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- A C-component with quasisimple quotient by its own odd core. -/
def IsTwoComponent (L : Subgroup G) : Prop :=
  L.IsCComponent ∧ IsQuasisimple (L ⧸ pPrimeCore 2 L)

private theorem oddCoreQuotient_equiv (e : G ≃* H) :
    Nonempty ((G ⧸ pPrimeCore 2 G) ≃* (H ⧸ pPrimeCore 2 H)) :=
  ⟨QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)⟩

namespace IsTwoComponent
variable {L K : Subgroup G}

theorem map_equiv (hL : L.IsTwoComponent) (e : G ≃* H) :
    (L.map e.toMonoidHom).IsTwoComponent := by
  let := hL.2
  obtain ⟨f⟩ := oddCoreQuotient_equiv (e.subgroupMap L)
  exact ⟨hL.1.map_equiv e, IsQuasisimple.of_mulEquiv f⟩

theorem subgroupOf (hL : L.IsTwoComponent) (hLK : L ≤ K) :
    (L.subgroupOf K).IsTwoComponent := by
  let := hL.2
  obtain ⟨e⟩ := oddCoreQuotient_equiv (subgroupOfEquivOfLe hLK).symm
  exact ⟨hL.1.subgroupOf hLK, IsQuasisimple.of_mulEquiv e⟩

theorem map_subtype (hK : K.IsSubnormal) {L : Subgroup K}
    (hL : L.IsTwoComponent) : (L.map K.subtype).IsTwoComponent := by
  let := hL.2
  obtain ⟨e⟩ := oddCoreQuotient_equiv (equivMapOfInjective L K.subtype K.subtype_injective)
  exact ⟨hL.1.map_subtype hK, IsQuasisimple.of_mulEquiv e⟩

theorem isComponent_of_oddCore_eq_bot [Finite G] (hL : L.IsTwoComponent)
    (ho : pPrimeCore 2 G = ⊥) : IsComponent G L := by
  let := hL.2
  have hLo := hL.1.subnormal.pPrimeCore_eq_bot ho
  exact ⟨hL.1.subnormal, IsQuasisimple.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hLo).trans QuotientGroup.quotientBot)⟩

end IsTwoComponent

/-- Prime-complement cores are monotone along subnormal inclusions. -/
theorem IsSubnormal.pPrimeCore_map_le [Finite G] {p : ℕ} [Fact p.Prime]
    {L : Subgroup G} (hL : L.IsSubnormal) :
    (pPrimeCore p L).map L.subtype ≤ pPrimeCore p G := by
  induction hL with
  | top =>
    exact (pPrimeCore_map_iso p topEquiv).le
  | step L K hLK _ hn ih =>
    let := hn
    have hm := pPrimeCore_map_subtype_le_pPrimeCore_of_normal p (L.subgroupOf K)
    have he : (pPrimeCore p (L.subgroupOf K)).map
        ((K.subtype).comp (L.subgroupOf K).subtype) =
        (pPrimeCore p L).map L.subtype := by
      have hf : K.subtype.comp (L.subgroupOf K).subtype =
          L.subtype.comp (subgroupOfEquivOfLe hLK).toMonoidHom := rfl
      rw [hf, ← map_map, pPrimeCore_map_iso]
    have hh := (map_mono (f := K.subtype) hm).trans ih
    rwa [map_map, he] at hh

namespace IsTwoComponent
variable [Finite G] {L : Subgroup G}

theorem isComponent_of_centralizes_oddCore (hL : L.IsTwoComponent)
    (hc : L ≤ centralizer (pPrimeCore 2 G : Set G)) : IsComponent G L := by
  let := hL.1.perfect
  let := hL.2
  have hcentral : pPrimeCore 2 L ≤ center L := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hc y.property) (x : G)
      (hL.1.subnormal.pPrimeCore_map_le (mem_map_of_mem L.subtype hx))).symm
  let f : PerfectCentralCovering.Cover L (L ⧸ pPrimeCore 2 L) := {
    toMonoidHom := QuotientGroup.mk' (pPrimeCore 2 L)
    surjective := QuotientGroup.mk'_surjective _
    isPerfect := inferInstance
    ker_le_center := by simpa only [QuotientGroup.ker_mk'] using hcentral }
  exact ⟨hL.1.subnormal, f.isQuasisimple⟩

end IsTwoComponent
end Subgroup

namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem IsComponent.isTwoComponent_of_solvable_oddCore {L : Subgroup G}
    (hL : IsComponent G L) [Group.IsSolvable (pPrimeCore 2 L)] :
    L.IsTwoComponent := by
  let := hL.2
  have ho : pPrimeCore 2 L ≠ ⊤ := by
    intro he
    let : Group.IsSolvable (⊤ : Subgroup L) := he ▸ inferInstanceAs
      (Group.IsSolvable (pPrimeCore 2 L))
    let : Group.IsSolvable L := Group.isSolvable_of_surjective
      (f := (topEquiv : (⊤ : Subgroup L) ≃* L).toMonoidHom) topEquiv.surjective
    exact hL.isCComponent.not_isSolvable inferInstance
  let : Nontrivial (L ⧸ pPrimeCore 2 L) := QuotientGroup.nontrivial_iff.mpr ho
  exact ⟨hL.isCComponent, IsQuasisimple.of_surjective
    (QuotientGroup.mk' (pPrimeCore 2 L)) (QuotientGroup.mk'_surjective _)⟩

end Theory.GroupTheory

namespace Subgroup
variable {G : Type*} [Group G]

/-- The source two-layer, generated by all two-components. -/
def twoComponentLayer (G : Type*) [Group G] : Subgroup G :=
  sSup {L : Subgroup G | L.IsTwoComponent}

/-- The subgroup O_{2',E}(G) in the source convention. -/
def oddELayer (G : Type*) [Group G] : Subgroup G :=
  pPrimeCore 2 G ⊔ twoComponentLayer G

theorem IsTwoComponent.le_twoComponentLayer {L : Subgroup G} (hL : L.IsTwoComponent) :
    L ≤ twoComponentLayer G := le_sSup hL

instance twoComponentLayer_characteristic : (twoComponentLayer G).Characteristic := by
  apply characteristic_iff_map_le.mpr
  intro e
  apply map_le_iff_le_comap.mpr
  exact sSup_le fun L hL => map_le_iff_le_comap.mp
    (hL.map_equiv e).le_twoComponentLayer

instance oddELayer_characteristic : (oddELayer G).Characteristic :=
  inferInstanceAs (pPrimeCore 2 G ⊔ twoComponentLayer G).Characteristic

/-- The two-layer is perfect, even though adjoining the odd core need not be. -/
theorem twoComponentLayer_isPerfect : Group.IsPerfect (twoComponentLayer G) := by
  rw [isPerfect_iff]
  apply le_antisymm (twoComponentLayer G).commutator_le_self
  refine sSup_le fun L hL => ?_
  exact (isPerfect_iff.mp hL.1.perfect).symm.le.trans
    (commutator_mono hL.le_twoComponentLayer hL.le_twoComponentLayer)

end Subgroup
