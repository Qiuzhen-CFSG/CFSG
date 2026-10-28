module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.ComponentData
public import CFSG.Quasithin.Chapter1.Section02.ComponentDichotomy.OddCore
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Ambient
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import Theory.Quasithin.Rank
public import CFSG.Quasithin.Chapter15.Section03.Constructions
/-!
# Odd core and component movement in Case I

The actual marked factor V₂ equals its commutator with the embedded
O²(C_M(Z₁)). Restricting A.1.26(1) to G₁=C_G(Z₁) makes V₂ centralize O(G₁).
The literal nontrivial Z⁺=Z∩(Z₁∨V₂) then centralizes that core, and the
15.1.18(6) involution hypothesis forces the core into M_c, where 1.1.5
shows its intersection is trivial.

Both the embedded residual and V₂ lie in O²(G₁), which normalizes every
C-component by 1.2.1(3). If V₂ centralized an outside component, the same
Z⁺ would put it in M_c, a contradiction. The printed normalizer-residual
version retains the marked-row containment O²(N_M(Z₁))≤C_G(Z₁), keeping
it distinct from the centralizer residual in the printed proof.

Source: Aschbacher--Smith 15.1.19(1),(7), printed p.1093. The preceding
15.1.16 row movement and Z⁺ facts are supplied by the marked-row owner;
the assembly owner supplies 15.1.18(6) on the actual centralizer Sylow.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03
variable {G : Type*} [Group G] [Finite G]
private theorem elementary_moved_centralizes_relative_oddCore
    (H A X : Subgroup G) (hsqt : IsStronglyQuasithin H)
    (hAH : A ≤ H) (hXH : X ≤ H)
    [IsElementaryAbelian 2 A] (hp : IsPPerfect 2 X) (hm : ⁅A,X⁆ = A) :
    A ≤ centralizer ((pPrimeCore 2 H).map H.subtype : Set G) := by
  let A' := A.subgroupOf H
  let X' := X.subgroupOf H
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.subgroupOf hAH
  let e := (subgroupOfEquivOfLe hXH).symm
  have hp' : IsPPerfect 2 X' := hp.of_surjective e.toMonoidHom e.surjective
  have hn : X ≤ normalizer (A : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr hm.le
  have hn' : X' ≤ normalizer (A' : Set H) := by
    apply le_normalizer_iff.mpr
    intro x hx a ha
    exact le_normalizer_iff.mp hn x hx a ha
  have hc := Chapter1.elementary_residual_centralizes_oddCore hsqt A' X' hp' hn'
  have he : ⁅A',X'⁆.map H.subtype = A := by
    rw [map_commutator,map_subgroupOf_eq_of_le hAH,map_subgroupOf_eq_of_le hXH,hm]
  intro a ha r hr
  obtain ⟨a',ha',rfl⟩ := mem_map.mp (he.symm ▸ ha)
  obtain ⟨r',hr',rfl⟩ := mem_map.mp hr
  exact congrArg Subtype.val (hc ha' r' hr')

/-- Original 15.1.19(1) on the literal centralizer, using the preceding
row movement and 15.1.18(6) hypotheses. No component has yet been chosen. -/
theorem source_caseI_oddCore_eq_bot
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (M Mc Z1 V2 : Subgroup G) (S : Sylow 2 (centralizer (Z1 : Set G)))
    [IsElementaryAbelian 2 V2]
    (hV2 : V2 ≤ centralizer (Z1 : Set G))
    (hmove : ⁅V2,(pResidual 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
      (M ⊓ centralizer (Z1 : Set G)).subtype⁆ = V2)
    (hplus : centralInvolutions T ⊓ (Z1 ⊔ V2) ≠ ⊥)
    (h115 : ∀ z ∈ centralInvolutions T, z ≠ 1 →
      Chapter1.Lemma115Hypotheses (centralizer (Z1 : Set G)) S Mc z) :
    pPrimeCore 2 (centralizer (Z1 : Set G)) = ⊥ := by
  obtain ⟨z,hz,hzne⟩ := (centralInvolutions T ⊓ (Z1 ⊔ V2)).bot_or_exists_ne_one.resolve_left hplus
  have hz115 := h115 z hz.1 hzne
  let H := centralizer (Z1 : Set G)
  let R := (pPrimeCore 2 H).map H.subtype
  have hV : V2 ≤ centralizer (R : Set G) :=
    elementary_moved_centralizes_relative_oddCore H V2 _
      (Chapter3.sqtk_of_mem_H hG hz115.mem_H).stronglyQuasithin
      hV2 ((map_subtype_le _).trans inf_le_right)
      (isPPerfect_embedded_pResidual 2 _) hmove
  have hZ : Z1 ≤ centralizer (R : Set G) :=
    le_centralizer_iff.mp (map_subtype_le (pPrimeCore 2 H))
  have hc : z ∈ centralizer (R : Set G) := (sup_le hZ hV) hz.2
  have hinside : pPrimeCore 2 H ≤ Mc.subgroupOf H := by
    intro r hr
    apply hz115.centralizer_le
    exact mem_centralizer_singleton_iff.mpr (hc r (mem_map_of_mem H.subtype hr))
  have hb := congrArg (Subgroup.map (Mc.subgroupOf H).subtype) hz115.oddCore_intersection_eq_bot
  rw [map_subgroupOf_eq_of_le hinside,Subgroup.map_bot] at hb
  exact hb

private theorem sqtk_twoCore_quotient {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H) :
    IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
  refine ⟨?_,hH.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 H) pCore_isPGroup).trans
    (hH.stronglyQuasithin p hp ho)

private theorem moved_normalizes_cComponent
    (H A X L : Subgroup G) (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hAH : A ≤ H) (hXH : X ≤ H) (hLH : L ≤ H)
    (hp : IsPPerfect 2 X) (hm : ⁅A,X⁆ = A)
    (hL : (L.subgroupOf H).IsCComponent) :
    X ⊔ A ≤ normalizer (L : Set G) := by
  let A' := A.subgroupOf H
  let X' := X.subgroupOf H
  let R := pResidual 2 H
  let e := (subgroupOfEquivOfLe hXH).symm
  have hp' : IsPPerfect 2 X' := hp.of_surjective e.toMonoidHom e.surjective
  have hXR : X' ≤ R := le_pResidual_of_isPPerfect X' hp'
  have hAR : A' ≤ R := by
    have he : ⁅A',X'⁆.map H.subtype = A'.map H.subtype := by
      rw [map_commutator,map_subgroupOf_eq_of_le hAH,map_subgroupOf_eq_of_le hXH,hm]
    have he' : ⁅A',X'⁆ = A' := (map_injective H.subtype_injective) he
    rw [←he']
    exact (commutator_mono le_rfl hXR).trans (commutator_le_right _ _)
  have hRN := Chapter1.Section02.twoPerfect_normalizes_cComponent_source
    (sqtk_twoCore_quotient hH) hL (isPPerfect_pResidual 2)
  have hXN := (map_mono (f := H.subtype) (hXR.trans hRN)).trans
    ((L.subgroupOf H).le_normalizer_map H.subtype)
  have hAN := (map_mono (f := H.subtype) (hAR.trans hRN)).trans
    ((L.subgroupOf H).le_normalizer_map H.subtype)
  rw [map_subgroupOf_eq_of_le hXH,map_subgroupOf_eq_of_le hLH] at hXN
  rw [map_subgroupOf_eq_of_le hAH,map_subgroupOf_eq_of_le hLH] at hAN
  exact sup_le hXN hAN

/-- The residual used in the proof of original 15.1.19(7), and the
actual marked factor, normalize and move every outside C-component. -/
theorem source_caseI_component_movement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (M Mc Z1 V2 L : Subgroup G) (S : Sylow 2 (centralizer (Z1 : Set G)))
    (hV2 : V2 ≤ centralizer (Z1 : Set G))
    (hmove : ⁅V2,(pResidual 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
      (M ⊓ centralizer (Z1 : Set G)).subtype⁆ = V2)
    (hplus : centralInvolutions T ⊓ (Z1 ⊔ V2) ≠ ⊥)
    (h115 : ∀ z ∈ centralInvolutions T, z ≠ 1 →
      Chapter1.Lemma115Hypotheses (centralizer (Z1 : Set G)) S Mc z)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (Z1 : Set G)))
    (hout : ¬ L ≤ centralizer (Z1 : Set G) ⊓ Mc) :
    (pResidual 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
        (M ⊓ centralizer (Z1 : Set G)).subtype ⊔ V2 ≤ normalizer (L : Set G) ∧
      ⁅L,V2⁆ ≠ ⊥ := by
  obtain ⟨z,hz,hzne⟩ := (centralInvolutions T ⊓ (Z1 ⊔ V2)).bot_or_exists_ne_one.resolve_left hplus
  have hz115 := h115 z hz.1 hzne
  refine ⟨moved_normalizes_cComponent _ V2 _ L
    (Chapter3.sqtk_of_mem_H hG hz115.mem_H) hV2
    ((map_subtype_le _).trans inf_le_right) hL.1
    (isPPerfect_embedded_pResidual 2 _) hmove hL.2,?_⟩
  intro he
  have hc : Z1 ⊔ V2 ≤ centralizer (L : Set G) := sup_le
    (le_centralizer_iff.mp hL.1)
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
  apply hout
  refine le_inf hL.1 ?_
  intro l hl
  apply hz115.centralizer_le
  exact mem_centralizer_singleton_iff.mpr (hc hz.2 l hl)

/-- The normalizer-residual form printed in 15.1.19(7). The marked source
row must identify its action on `Z₁` as a two-group; this is exactly the
containment `hnormalizer` below. -/
theorem source_caseI_component_normalizer_movement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (M Mc Z1 V2 L : Subgroup G) (S : Sylow 2 (centralizer (Z1 : Set G)))
    (hV2 : V2 ≤ centralizer (Z1 : Set G))
    (hmove : ⁅V2,(pResidual 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
      (M ⊓ centralizer (Z1 : Set G)).subtype⁆ = V2)
    (hplus : centralInvolutions T ⊓ (Z1 ⊔ V2) ≠ ⊥)
    (h115 : ∀ z ∈ centralInvolutions T, z ≠ 1 →
      Chapter1.Lemma115Hypotheses (centralizer (Z1 : Set G)) S Mc z)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (Z1 : Set G)))
    (hout : ¬ L ≤ centralizer (Z1 : Set G) ⊓ Mc)
    (hnormalizer : (pResidual 2 (M ⊓ normalizer (Z1 : Set G) : Subgroup G)).map
      (M ⊓ normalizer (Z1 : Set G)).subtype ≤ centralizer (Z1 : Set G)) :
    (pResidual 2 (M ⊓ normalizer (Z1 : Set G) : Subgroup G)).map
        (M ⊓ normalizer (Z1 : Set G)).subtype ⊔ V2 ≤ normalizer (L : Set G) ∧
      ⁅L,V2⁆ ≠ ⊥ := by
  have hm := source_caseI_component_movement hG T M Mc Z1 V2 L S
    hV2 hmove hplus h115 hL hout
  obtain ⟨z,hz,hzne⟩ := (centralInvolutions T ⊓ (Z1 ⊔ V2)).bot_or_exists_ne_one.resolve_left hplus
  let H := centralizer (Z1 : Set G)
  let X := (pResidual 2 (M ⊓ normalizer (Z1 : Set G) : Subgroup G)).map
    (M ⊓ normalizer (Z1 : Set G)).subtype
  let e := (subgroupOfEquivOfLe hnormalizer).symm
  have hp : IsPPerfect 2 (X.subgroupOf H) :=
    (isPPerfect_embedded_pResidual 2 _).of_surjective e.toMonoidHom e.surjective
  have hn := Chapter1.Section02.twoPerfect_normalizes_cComponent_source
    (sqtk_twoCore_quotient (Chapter3.sqtk_of_mem_H hG (h115 z hz.1 hzne).mem_H)) hL.2 hp
  have hmap := (map_mono (f := H.subtype) hn).trans
    ((L.subgroupOf H).le_normalizer_map H.subtype)
  rw [map_subgroupOf_eq_of_le hnormalizer,map_subgroupOf_eq_of_le hL.1] at hmap
  exact ⟨sup_le hmap (le_sup_right.trans hm.1),hm.2⟩


/-- Original 15.1.19(1) before choosing the outside component. The
prepared elementary module supplies the literal containment `V₂ ≤ G₁`;
15.1.18(6) supplies the involution hypotheses. -/
theorem PreparedChosenModule.caseI_oddCore_eq_bot
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) {T : Sylow 2 G}
    {M Mc V : Subgroup G} (h : PreparedChosenModule T M V)
    (Z1 V2 : Subgroup G) (hZ1 : Z1 ≤ thompsonFixed T V) (hV2 : V2 ≤ V)
    (S : Sylow 2 (centralizer (Z1 : Set G)))
    (hmove : ⁅V2,(pResidual 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
      (M ⊓ centralizer (Z1 : Set G)).subtype⁆ = V2)
    (hplus : centralInvolutions T ⊓ (Z1 ⊔ V2) ≠ ⊥)
    (h115 : ∀ z ∈ centralInvolutions T, z ≠ 1 →
      Chapter1.Lemma115Hypotheses (centralizer (Z1 : Set G)) S Mc z) :
    pPrimeCore 2 (centralizer (Z1 : Set G)) = ⊥ := by
  let := h.elementary
  let : IsElementaryAbelian 2 V2 := IsElementaryAbelian.of_le hV2
  have hV2G : V2 ≤ centralizer (Z1 : Set G) := hV2.trans
    (V.le_centralizer.trans (centralizer_le (hZ1.trans inf_le_left)))
  exact source_caseI_oddCore_eq_bot hG T M Mc Z1 V2 S hV2G hmove hplus h115

namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Apply original 15.1.19(1),(7) to the actual prepared module and the
outside component selected in `C_G(Z₁)`. Only the preceding source row
movement, `Z⁺`, and 15.1.18(6) remain as earlier-source inputs. -/
theorem oddCore_and_movement (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (V2 : Subgroup G) (hV2 : V2 ≤ V)
    (S : Sylow 2 d.G1)
    (hmove : ⁅V2,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆ = V2)
    (hplus : centralInvolutions T ⊓ (d.Z1 ⊔ V2) ≠ ⊥)
    (h115 : ∀ z ∈ centralInvolutions T, z ≠ 1 → Chapter1.Lemma115Hypotheses d.G1 S Mc z) :
    pPrimeCore 2 d.G1 = ⊥ ∧
      (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype ⊔ V2 ≤
        normalizer (d.L : Set G) ∧ ⁅d.L,V2⁆ ≠ ⊥ := by
  let := h.elementary
  let : IsElementaryAbelian 2 V2 := IsElementaryAbelian.of_le hV2
  have hV2G : V2 ≤ d.G1 := hV2.trans
    (V.le_centralizer.trans (centralizer_le (d.Z1_le_fixed.trans inf_le_left)))
  exact ⟨source_caseI_oddCore_eq_bot hG T M Mc d.Z1 V2 S hV2G hmove hplus h115,
    source_caseI_component_movement hG T M Mc d.Z1 V2 d.L S
      hV2G hmove hplus h115 d.L_component d.L_not_le_MZ⟩

/-- The printed normalizer-residual conclusion on the literal selected
component, retaining the precise marked-row action input. -/
theorem normalizer_residual_movement (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (V2 : Subgroup G) (hV2 : V2 ≤ V)
    (S : Sylow 2 d.G1)
    (hmove : ⁅V2,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆ = V2)
    (hplus : centralInvolutions T ⊓ (d.Z1 ⊔ V2) ≠ ⊥)
    (h115 : ∀ z ∈ centralInvolutions T, z ≠ 1 → Chapter1.Lemma115Hypotheses d.G1 S Mc z)
    (hnormalizer : (pResidual 2 (M ⊓ normalizer (d.Z1 : Set G) : Subgroup G)).map
      (M ⊓ normalizer (d.Z1 : Set G)).subtype ≤ d.G1) :
    (pResidual 2 (M ⊓ normalizer (d.Z1 : Set G) : Subgroup G)).map
        (M ⊓ normalizer (d.Z1 : Set G)).subtype ⊔ V2 ≤ normalizer (d.L : Set G) ∧
      ⁅d.L,V2⁆ ≠ ⊥ := by
  let := h.elementary
  have hV2G : V2 ≤ d.G1 := hV2.trans
    (V.le_centralizer.trans (centralizer_le (d.Z1_le_fixed.trans inf_le_left)))
  exact source_caseI_component_normalizer_movement hG T M Mc d.Z1 V2 d.L S
    hV2G hmove hplus h115 d.L_component d.L_not_le_MZ hnormalizer
end CaseIComponentData

end CFSG.Quasithin.Chapter15.Section01
