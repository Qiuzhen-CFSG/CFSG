module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SeedFactors
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.Radicals
public import Theory.Representation.SymplecticFourOrthogonalCover.SmallNormalFactor

/-!
# Marked preservation and saturation of the original star

The full original natural cover, extended across the complete fixed core,
forces every original-radical-normal factor of order at most q in U D to
centralize the component--radical intersection. The selected Sylow seed
splits into two such factors. Failure of marked preservation would move
one of their holomorph conjugates, while the original star inclusion puts
that factor in U D. This contradiction preserves the literal component
projection and supplies saturation in the same star overgroup.

No equality with a minimum characteristic replacement is asserted. This
proves the marked-star step at the opening of MS93 (3.7), printed p.872,
using the original star inclusion from (3.4), printed p.869.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open ChapterB.QuasisimpleSource MSCentralOrbit DistanceTwoRecognition
open Theory.SpecificGroups.SymplecticFour
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

/-- A small normalized subgroup of the original moving layer times its
full fixed core centralizes the literal component--radical intersection.
The symplectic marking is constructed from the original central-omega cover. -/
theorem original_small_normal_factor_centralizes
    (J : Subgroup H)
    (hJ : J ≤ ⁅omegaOrbit R,K⁆ ⊔ (pCore 2 H ⊓ centralizer (K : Set H)))
    (hnJ : R ≤ normalizer (J : Set H)) (hcJ : Nat.card J ≤ Nat.card F) :
    J ≤ centralizer (K ⊓ R : Set H) := by
  obtain ⟨d,_⟩ := h.characteristic_reduction
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := K.map q
  let : C.Normal := h.component_image_structure.2.1
  let hk := (QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _) hk) C
  obtain ⟨E,hE,e,he⟩ := h.centralOmega_initial_cover
  change ActionEquiv (s.action.comp C.subtype) (binaryNatural (K := E.Carrier)) at e
  let j := ElementaryMovedCover.embedding (omegaCenterIn (pCore 2 H)) K q
    (QuotientGroup.mk'_surjective _) hk
  have hj : j.range=⁅omegaOrbit R,K⁆ := by
    rw [ElementaryMovedCover.embedding_range,←h.initialCore_eq]
  have hlarge : 2<Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let eSp : L (K := E.Carrier) ≃* Sp E.Carrier :=
    (MulEquiv.subgroupCongr (OneCohomology.SymplecticFour.LargeField.commutator_eq_top hlarge)).trans
      Subgroup.topEquiv
  let h' : Input K R n E.Carrier := {
    nonbinary := h.nonbinary
    field_card := E.card_eq.trans (congrArg (2^·) hE)
    sqtk := h.sqtk
    fitting := h.fitting
    component := h.component
    product := h.product
    radical := h.radical
    characteristic := h.characteristic
    quotientEquiv := (cComponentTwoCoreQuotientEquiv h.component).trans (e.groupEquiv.trans eSp) }
  let β : (K ⊓ R : Subgroup H) →* L (K := E.Carrier) :=
    e.groupEquiv.toMonoidHom.comp ((q.subgroupMap K).comp (inclusion inf_le_left))
  have hβeq : ((commutator (Sp E.Carrier)).subtype.comp β).range=
      (R.subgroupOf K).map (componentProjection h') := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨⟨t,t.property.1⟩,t.property.2,rfl⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,⟨t.property,ht⟩⟩,rfl⟩
  have hβ : ((commutator (Sp E.Carrier)).subtype.comp β).range.IsPRadical 2 := by
    rw [hβeq]
    exact original_marked_radical_isPRadical h' d
  let D := pCore 2 H ⊓ centralizer (K : Set H)
  have hjX : j.range ≤ omegaCenterIn (pCore 2 H) := by
    rw [ElementaryMovedCover.embedding_range]
    exact commutator_le_left _ _
  have hjQ : j.range ≤ pCore 2 H := hjX.trans (map_subtype_le _)
  have hDU : D ≤ centralizer (j.range : Set H) := by
    apply le_centralizer_iff.mpr
    intro x hx
    exact (centralizer_le inf_le_left) ((mem_omegaCenterIn_iff _ _).mp (hjX hx)).2.1
  apply small_normal_factor_centralizes (E.card_eq.trans (congrArg (2^·) hE)) h.nonbinary
    (MovedSection.coverProjection s e) he j D (K ⊓ R) J hDU
    (inf_le_right.trans (centralizer_le inf_le_left)) ?_ β hβ ?_
    (by rw [hj]; exact hJ) (inf_le_right.trans hnJ)
    (by rwa [E.card_eq,hE,←h.field_card])
  · intro w
    exact (ElementaryMovedCover.cover_kernel_iff _ _ _ _ _ e w).trans
      ⟨fun hc => ⟨hjQ ⟨_,rfl⟩,hc⟩,fun hd => hd.2⟩
  · intro t w
    exact ElementaryMovedCover.cover_action_conjugate _ _ _ _ _ e
      (inclusion inf_le_left t) w

/-- The same small-factor theorem on the original graph, with the literal
component--radical intersection as actor. -/
theorem original_graph_small_normal_factor_centralizes
    (J : Subgroup (FreeAmalgam R))
    (hJ : J ≤ U R (alpha R) ⊔ fixedCore R (alpha R))
    (hnJ : Q R (beta R) ≤ normalizer (J : Set (FreeAmalgam R)))
    (hcJ : Nat.card J ≤ Nat.card F) :
    J ≤ centralizer (Ltilde R (alpha R) ⊓ Q R (beta R) : Set (FreeAmalgam R)) := by
  let i := embedM R
  let J₀ := J.comap i
  have hU : U R (alpha R)=(⁅omegaOrbit R,K⁆).map i := by
    rw [U,Z_alpha_eq_omegaOrbit,Ltilde_alpha,h.residual_eq,map_commutator]
  have hD : fixedCore R (alpha R)=
      (pCore 2 H ⊓ centralizer (K : Set H)).map i := by
    change Q R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R))=_
    rw [Q_alpha R h.radical.isPGroup h.radical.twoCore_le,Ltilde_alpha,h.residual_eq]
    exact map_inf_centralizer_of_injective i (embedM_injective R) _ _
  have hJ' : J ≤ (⁅omegaOrbit R,K⁆ ⊔ (pCore 2 H ⊓ centralizer (K : Set H))).map i := by
    rw [Subgroup.map_sup,←hU,←hD]
    exact hJ
  have hJr : J ≤ i.range := hJ'.trans (map_le_range _ _)
  have hm : J₀.map i=J := map_comap_eq_self hJr
  have hJ₀ : J₀ ≤ ⁅omegaOrbit R,K⁆ ⊔ (pCore 2 H ⊓ centralizer (K : Set H)) := by
    exact (map_le_map_iff_of_injective (embedM_injective R)).mp (hm ▸ hJ')
  have hn₀ : R ≤ normalizer (J₀ : Set H) := by
    intro r hr
    apply mem_normalizer_iff.mpr
    intro x
    have hh := mem_normalizer_iff.mp (hnJ (show i r ∈ Q R (beta R) by
      rw [Q_beta]; exact mem_map_of_mem i hr)) (i x)
    simpa only [J₀,mem_comap,map_mul,map_inv] using hh
  have hc₀ : Nat.card J₀ ≤ Nat.card F := by
    rw [Nat.card_congr (J₀.equivMapOfInjective i (embedM_injective R)).toEquiv,hm]
    exact hcJ
  have hcentral := original_small_normal_factor_centralizes h J₀ hJ₀ hn₀ hc₀
  have hh := (map_mono (f := i) hcentral).trans (map_centralizer_le_centralizer_image _ i)
  change J₀.map i ≤ centralizer (((K ⊓ R).map i : Subgroup (FreeAmalgam R)) :
    Set (FreeAmalgam R)) at hh
  rw [hm] at hh
  have hactor : Ltilde R (alpha R) ⊓ Q R (beta R)=(K ⊓ R).map i := by
    rw [map_inf _ _ _ (embedM_injective R),Ltilde_alpha,h.residual_eq,Q_beta]
  rw [←hactor] at hh
  exact hh

/-- The original source seed preserves its marked radical image and its
literal star radical is saturated. No replacement-radical equality or
odd-index witness for a replacement is assumed. -/
theorem exists_source_star_marked_saturation :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R,
      Y.map (embedS R)=componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      (((starCentralizer R Y).map R.subtype).subgroupOf K).map
        (componentProjection h)=(R.subgroupOf K).map (componentProjection h) ∧
      (let Tstar := (starCentralizer R Y).map R.subtype
        let Mstar := K ⊔ Tstar
        Tstar.subgroupOf Mstar=R.subgroupOf Mstar ∧
          (normalizer (Tstar.subgroupOf Mstar : Set Mstar)).pCoreIn 2=
            Tstar.subgroupOf Mstar) := by
  obtain ⟨P,Y,hY,hnY,hs | ⟨δ,Pδ,J,_,_,hJB,hBs,_,hnJ,hcJ,hmJ,_⟩⟩ :=
    exists_source_star_saturation_or_moved_small_factor h
  · refine ⟨P,Y,hY,hnY,?_,hs⟩
    congr 1
    ext x
    have hh := SetLike.ext_iff.mp hs.1
      (⟨x,mem_sup_left x.property⟩ : ↥(K ⊔ (starCentralizer R Y).map R.subtype))
    exact hh
  · obtain ⟨geometry,hpos,_⟩ := h.positive_even_geometry
    have hj : J ≤ U R (alpha R) ⊔ fixedCore R (alpha R) :=
      hJB.trans (hBs.trans (h.original_starSpan_le_moving_fixed geometry hpos Y P hY hnY))
    exact False.elim (hmJ (commutator_eq_bot_iff_le_centralizer.mpr
      (original_graph_small_normal_factor_centralizes h J hj hnJ hcJ)))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
