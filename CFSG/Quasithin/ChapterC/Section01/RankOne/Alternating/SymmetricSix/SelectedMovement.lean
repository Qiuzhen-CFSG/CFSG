module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.SelectedGroup
public import Theory.SpecificGroups.SymmetricSix.TranspositionCubic.Movement
public import Stellmacher.ElementaryAbelianMaxJMap
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.CubicLocalClass

/-!
# The genuine local class on the selected cubic preimage

Restrict the original normal module and its coordinate map to the selected
preimage. The transposition in the actual Thompson image moves the cubic
translate of an original omega-center vector. Thus the selected Sylow of
index three moves its canonical omega-center span. The proved cubic local
class theorem now constructs the exact inclusion of its Baumann subgroup
in the residual join; no local-class or module-recognition certificate is
assumed.

Source: Aschbacher–Smith C.1.21(4) and C.1.24(c), printed pp.129–131.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.TranspositionCubic
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem selected_omega_movement (R V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hVR : V ≤ R) (M : Subgroup (G ⧸ pCore 2 G))
    (q : G →* Sym) (r c : Sym)
    (hR : R.map q ≤ zpowers r) (hrJ : r ∈ (elementaryAbelianMaxJ R).map q)
    (hcH : c ∈ (selectedGroup R M).map q)
    (e : V ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (g : G) (v : V), (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (q g) (e v).toAdd)
    (hc : c^3=1) (hi : r*c*r⁻¹=c⁻¹)
    (hm : ¬fixedSpace (BinaryPermutation.naturalRepresentation (Fin 6)) (zpowers r) ≤
      fixedSpace (BinaryPermutation.naturalRepresentation (Fin 6)) (zpowers c)) :
    ¬ elementaryAbelianMaxJ (R.subgroupOf (selectedGroup R M)) ≤
      centralizer (normalClosure (omegaOneCenterAmbient
        (R.subgroupOf (selectedGroup R M)) : Set (selectedGroup R M)) : Set (selectedGroup R M)) := by
  let H := selectedGroup R M
  let V' := V.subgroupOf H
  let eV : V' ≃* V := subgroupOfEquivOfLe (hVR.trans (le_selectedGroup R M))
  let : IsElementaryAbelian 2 V' := IsElementaryAbelian.subgroupOf (hVR.trans (le_selectedGroup R M))
  have he' : ∀ (g : H) (v : V'), ((eV.trans e) (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) ((q.comp H.subtype) g) ((eV.trans e) v).toAdd := by
    intro g v
    exact he g (eV v)
  have hR' : (R.subgroupOf H).map (q.comp H.subtype) ≤ zpowers r := by
    rw [←map_map,map_subgroupOf_eq_of_le (le_selectedGroup R M)]
    exact hR
  have hrJ' : r ∈ (elementaryAbelianMaxJ (R.subgroupOf H)).map (q.comp H.subtype) := by
    rw [←map_map,←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le (le_selectedGroup R M)]
    exact hrJ
  have hc' : c ∈ (q.comp H.subtype).range := by
    obtain ⟨x,hx,hxc⟩ := hcH
    exact ⟨⟨x,hx⟩,hxc⟩
  exact omega_span_moved V' (R.subgroupOf H) (elementaryAbelianMaxJ (R.subgroupOf H))
    (comap_mono hVR) (q.comp H.subtype) (eV.trans e) he' r c hR' hrJ' hc' hc hi hm

theorem selected_inLocalClass (R V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hVR : V ≤ R) (hpR : IsPGroup 2 R) (hQR : pCore 2 G ≤ R)
    (M : Subgroup (G ⧸ pCore 2 G)) (hM : Nat.card M=3)
    (hRq : Nat.card (R.map (QuotientGroup.mk' (pCore 2 G)))=2)
    (hn : R.map (QuotientGroup.mk' (pCore 2 G)) ≤ normalizer (M : Set (G ⧸ pCore 2 G)))
    (hf : generalizedFitting G = pCore 2 G)
    (q : G →* Sym) (r c : Sym)
    (hR : R.map q ≤ zpowers r) (hrJ : r ∈ (elementaryAbelianMaxJ R).map q)
    (hcH : c ∈ (selectedGroup R M).map q)
    (e : V ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (g : G) (v : V), (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (q g) (e v).toAdd)
    (hc : c^3=1) (hi : r*c*r⁻¹=c⁻¹)
    (hm : ¬fixedSpace (BinaryPermutation.naturalRepresentation (Fin 6)) (zpowers r) ≤
      fixedSpace (BinaryPermutation.naturalRepresentation (Fin 6)) (zpowers c)) :
    GlaubermanNiles.InLocalClass (inclusion
      (show ChapterB.baumann (R.subgroupOf (selectedGroup R M)) ≤
        pResidual 2 (selectedGroup R M) ⊔ ChapterB.baumann (R.subgroupOf (selectedGroup R M)) from le_sup_right)) := by
  obtain ⟨T,hT,hiT⟩ := selected_sylow R hpR hQR M hM hRq hn
  have hmove := selected_omega_movement R V hVR M q r c hR hrJ hcH e he hc hi hm
  rw [←hT] at hmove ⊢
  exact FiveBlockSource.cubic_omega_inLocalClass T hiT (selected_characteristic_two R M hf) hmove
end CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
