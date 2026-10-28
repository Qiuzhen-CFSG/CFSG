module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.CoveredCase.Displacement
public import Theory.GroupAction.TISylowDisplacement
/-!
# Ambient exclusion of the nontrivial Suzuki cover

For V = Ω₁(T_C)Ω₁(T_L), the actual normalizer image acts faithfully.
Tight embedding makes W = V ∩ C_G(L) a TI subgroup, and fusion provides
a disjoint nontrivial translate. The whole Sylow has all displacements
in Z(L), whereas its component image has order eight. The general TI
Sylow displacement bound now gives 8 ≤ |P| ≤ |Z(L)| ≤ 4.

`center_eq_bot` retains only the literal earlier cover reduction and
center-order bound as additional source inputs. The isomorphism with
C_{T_C}(R), actual Sylow upgrade, transport containment, Delta-zero omega
containment and faithfulness are all retained. No action-image, weak-closure,
kernel, displacement or numerical exclusion conclusion is a premise.
The center-free LocalAction and Bender/J1 assembly remain with the parent.

Source: Aschbacher–Smith, 16.5.1, printed pp.1193–1195; 16.1.2, p.1170;
I.2.2(4), p.409, combined manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup
open scoped Pointwise commutatorElement
open CFSG.Quasithin.Chapter16 CFSG.Quasithin.Chapter16.CoverAndSylowElimination
open CFSG.Quasithin.Chapter16.Intersections CFSG.Quasithin.Chapter16.Intersections.Bender
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.CoveredCase
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G} {z g : G} {R : Subgroup G}

omit [Finite G] in
private theorem map_normalizer_action {V W : Subgroup G} (hWV : W ≤ V)
    (a : normalizer (V : Set G)) :
    ((W.subgroupOf V).map (V.normalizerMonoidHom a).toMonoidHom).map V.subtype = W.conjBy (a:G) := by
  have hc : V.subtype.comp (V.normalizerMonoidHom a).toMonoidHom =
      (MulAut.conj (a:G)).toMonoidHom.comp V.subtype := by ext v; rfl
  rw [map_map, hc, ← map_map, map_subgroupOf_eq_of_le hWV]
  rfl

/-- Tight embedding gives the full normalizer-image TI condition on the actual W. -/
theorem commuting_omega_TI (h : StandardSetup T z L) (d : SuzukiCoverInput T L)
    (a : ActionImage (benderSpace T L)) :
    let W := (omegaOneAmbient (commutingSylow T L)).subgroupOf (benderSpace T L)
    W.map (a : MulAut (benderSpace T L)).toMonoidHom = W ∨
      Disjoint W (W.map (a : MulAut (benderSpace T L)).toMonoidHom) := by
  let V := benderSpace T L
  let W := omegaOneAmbient (commutingSylow T L)
  have hWV : W ≤ V := le_sup_left
  obtain ⟨n,hn⟩ := a.property
  have hm : ((W.subgroupOf V).map (a : MulAut V).toMonoidHom).map V.subtype = W.conjBy (n:G) := by
    rw [← hn]
    exact map_normalizer_action hWV n
  have hp : IsPGroup 2 V := T.isPGroup'.of_injective (inclusion (benderSpace_le_sylow T L))
    (inclusion_injective _)
  have hTI := tight_intersection_TI h.tight hp n.property
  rw [space_centralizer_intersection d] at hTI
  rcases hTI with he | hd
  · left
    apply map_injective V.subtype_injective
    rw [hm, he, map_subgroupOf_eq_of_le hWV]
  · right
    apply disjoint_def.mpr
    intro v hv hw
    apply Subtype.ext
    apply disjoint_def.mp hd hv
    rw [← hm]
    exact mem_map_of_mem V.subtype hw

/-- The Suzuki cover is impossible under the genuine ambient Delta-zero hypotheses. -/
theorem no_covered_configuration
    (h : IntersectionSetup T z L g R) (d : SuzukiCoverInput T L)
    (hcard : Nat.card (center L) ≤ 4)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (e : R ≃* ↥(commutingSylow T L ⊓ centralizer (R : Set G)))
    (htransport : (T : Subgroup G) ⊓ normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hdelta : omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L)
    (hfaith : Disjoint R (centralizer (L : Set G))) : False := by
  obtain ⟨hU,hV,hZ⟩ := omega_configuration h d hR htransport hdelta hfaith
  let := hV
  let V := benderSpace T L
  let W := omegaOneAmbient (commutingSylow T L)
  let Z := componentCenter L
  have hWV : W ≤ V := le_sup_left
  have hZV : Z ≤ V := hZ.trans hWV
  obtain ⟨P,hP⟩ := sylow_inducedActor V T (sylow_normalizes_factors h.toStandardSetup).1
  have hlower : 8 ≤ Nat.card P := by
    rw [← component_image_card h.toStandardSetup d]
    have hle : inducedActor V (componentSylow T L) ≤ (P : Subgroup (ActionImage V)) := by
      rw [hP]
      exact map_mono (comap_mono inf_le_left)
    exact Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
  have hconj := h.eq_conjugate_commutingSylow hR htransport
  obtain ⟨a,ha,hamove⟩ := covered_fusion_mover h d hconj hU
  let an : normalizer (V : Set G) := ⟨a,ha⟩
  let am : ActionImage V := V.normalizerMonoidHom.rangeRestrict an
  let ρ : ActionImage V →* MulAut V := (ActionImage V).subtype
  have hWne : W.subgroupOf V ≠ ⊥ := by
    intro he
    apply commuting_omega_nontrivial h.toStandardSetup
    have hh := congrArg (fun X : Subgroup V => X.map V.subtype) he
    rwa [map_subgroupOf_eq_of_le hWV, Subgroup.map_bot] at hh
  have hdisj : Disjoint (W.subgroupOf V) ((W.subgroupOf V).map (ρ am).toMonoidHom) := by
    have hm := map_normalizer_action hWV an
    change ((W.subgroupOf V).map (ρ am).toMonoidHom).map V.subtype = W.conjBy a at hm
    rw [hamove] at hm
    apply disjoint_def.mpr
    intro v hv hv'
    apply Subtype.ext
    apply disjoint_def.mp (disjoint_omegas (T:=T) hfaith) hv
    rw [← hm]
    exact mem_map_of_mem V.subtype hv'
  have hdisp : ∀ p ∈ (P : Subgroup (ActionImage V)), ∀ v : V,
      ρ p v * v⁻¹ ∈ Z.subgroupOf V := by
    intro p hp v
    rw [hP] at hp
    obtain ⟨n,hn,rfl⟩ := hp
    exact whole_sylow_displacement h d hR e htransport hU hfaith n hn v v.property
  have hupper := Theory.GroupAction.TISylowDisplacement.card_le_of_faithful_automorphisms
    ρ Subtype.val_injective P (W.subgroupOf V) (Z.subgroupOf V) hWne (comap_mono hZ)
    (commuting_omega_TI h.toStandardSetup d) hdisp am hdisj
  have hZcard : Nat.card (Z.subgroupOf V) = Nat.card (center L) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZV).toEquiv]
    exact card_map_of_injective L.subtype_injective
  rw [hZcard] at hupper
  omega

/-- Discharge the covered branch, retaining the precise earlier-source reduction. -/
theorem center_eq_bot
    (h : IntersectionSetup T z L g R)
    (hcover : center L ≠ ⊥ → SuzukiCoverInput T L ∧ Nat.card (center L) ≤ 4)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (e : R ≃* ↥(commutingSylow T L ⊓ centralizer (R : Set G)))
    (htransport : (T : Subgroup G) ⊓ normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hdelta : omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L)
    (hfaith : Disjoint R (centralizer (L : Set G))) : center L = ⊥ := by
  by_contra hc
  obtain ⟨d,hd⟩ := hcover hc
  exact no_covered_configuration h d hd hR e htransport hdelta hfaith

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.CoveredCase
