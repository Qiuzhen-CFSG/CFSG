module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.TriangleQuotientSplitting
public import Theory.SpecificGroups.MinusExtraspecial.PointComplementRetention

/-!
# A complement retaining the actual point-centralizer subgroup

The literal central quotient acts faithfully on its full minus-extraspecial
core, with the complete inner automorphism kernel and the actual A₅ point
action. The order-twelve point section supplied by the original field
embedding can therefore be retained in a complement. Its full inverse image
contains the original A₄ × C₂ subgroup and preserves the original quotient
map and central kernel.

This is the first marked complement in Baumeister Lemma 2.6, p.496. Retaining
the original pair subgroup simultaneously remains a separate step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
open MinusExtraspecial.AlternatingAction
open MinusExtraspecial.FixedFourCalculation.Outside

variable {G : Type*} [Group G] [Finite G]

set_option maxHeartbeats 800000 in
/-- A genuine complement retaining the original point section, with its
literal full central preimage and original quotient map. -/
theorem literal_triangle_point_complement
    {D : Seed G} (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane) (j : SingerField.Model →* G)
    (hj : PlaneTransport.FieldEmbedding A C a j) :
    let f := j SingerField.fieldElement
    let H := Janko23.involutionCentralizer f
    let Q := Janko23.localCore f
    let X := (j.range ⊓ H).subgroupOf H
    let q := QuotientGroup.mk' (center H)
    (center H).map H.subtype = zpowers f ∧
      ∃ K : Subgroup (H ⧸ center H), (Q.map q).IsComplement' K ∧ X.map q ≤ K ∧
        ∃ R : Subgroup H, R = K.comap q ∧ center H ≤ R ∧ X ≤ R ∧
          Q ⊓ R = center H ∧ Q ⊔ R = ⊤ ∧ Nat.card R = 120 ∧
          ∃ r : R →* H ⧸ Q, Function.Surjective r ∧
            r.ker = (center H).subgroupOf R ∧
            ∀ x : R, r x = QuotientGroup.mk' Q (x : H) := by
  let f := j SingerField.fieldElement
  let H := Janko23.involutionCentralizer f
  let Q := Janko23.localCore f
  let X := (j.range ⊓ H).subgroupOf H
  let q := QuotientGroup.mk' (center H)
  have hf : orderOf f = 2 := image_involution_order j hj.1
  obtain ⟨⟨eQ⟩,_,⟨eA⟩⟩ := literal_involution_core_and_quotient (D := D) hc f hf
  obtain ⟨hZmap,hZ,_hV,hU,hd,_hi,K,hK,_hpre⟩ :=
    literal_triangle_quotient_splitting P hc A C a j hj
  have hself : centralizer (Q : Set H) ≤ Q := centralizer_generalizedFitting_le H
  have hZQ : center H ≤ Q := Janko23.HTypeAt.center_le_core
  obtain ⟨d,hdmark⟩ := exists_quotient_marking Q eQ hself eA
  let F : H →* alternatingGroup (Fin 5) := d.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hFker : F.ker = Q := by
    rw [MonoidHom.ker_comp_of_injective _ _ d.injective,QuotientGroup.ker_mk']
  let p : (H ⧸ center H) →* alternatingGroup (Fin 5) :=
    QuotientGroup.lift (center H) F (hFker.symm ▸ hZQ)
  have hp : Function.Surjective p := by
    intro z
    obtain ⟨h,hh⟩ := (d.surjective.comp (QuotientGroup.mk'_surjective Q)) z
    exact ⟨q h,hh⟩
  have hpker : p.ker = Q.map q := by
    ext w
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (center H) w
    change F h = 1 ↔ q h ∈ Q.map q
    change h ∈ F.ker ↔ h ∈ (Q.map q).comap q
    rw [hFker,comap_map_eq_self (by simpa only [q,QuotientGroup.ker_mk'] using hZQ)]
  let e := centralQuotientEquiv Q eQ hself eA
  let ρ : (H ⧸ center H) →* MulAut MinusExtraspecial.Model :=
    evenAutomorphisms.subtype.comp e.toMonoidHom
  have hρ : Function.Injective ρ := evenAutomorphisms.subtype_injective.comp e.injective
  have hρmk (h : H) : ρ (q h) = coreAction Q eQ h := rfl
  have hmark (w : H ⧸ center H) : fivePointAction (ρ w) = (p w).val := by
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (center H) w
    rw [hρmk]
    exact (hdmark h).symm
  have hinner (n : MinusExtraspecial.Model) : ∃ w ∈ p.ker, ρ w = MulAut.conj n := by
    refine ⟨q (eQ.symm n : H),?_,?_⟩
    · rw [hpker]
      exact mem_map_of_mem q (eQ.symm n).property
    · rw [hρmk,coreAction_subtype,eQ.apply_symm_apply]
  obtain ⟨L,hL,hXL⟩ := MinusExtraspecial.PointComplementRetention.exists_complement_containing_twelve
    p hp ρ hρ hmark hinner K (X.map q) (hpker.symm ▸ hK) (hpker.symm ▸ hd) hU
  have hL' : (Q.map q).IsComplement' L := hpker ▸ hL
  obtain ⟨R,hR,hZR,hQR,hgen,r,hr,hker,hrep⟩ :=
    exists_preimage_of_quotient_complement Q (center H) hZQ L hL'
  have hXR : X ≤ R := by
    rw [hR]
    exact fun x hx => hXL (mem_map_of_mem q hx)
  have hRcard : Nat.card R = 120 := by
    have hk : Nat.card r.ker = 2 := by
      rw [hker,Nat.card_congr (subgroupOfEquivOfLe hZR).toEquiv,hZ]
    have hh := r.ker.index_mul_card
    rw [index_ker,MonoidHom.range_eq_top.mpr hr,
      Nat.card_congr (topEquiv (G := H ⧸ Q)).toEquiv,
      Nat.card_congr eA.toEquiv,nat_card_alternatingGroup,hk] at hh
    norm_num at hh
    exact hh.symm
  exact ⟨hZmap,L,hL',hXL,R,hR,hZR,hXR,hQR,hgen,hRcard,r,hr,hker,hrep⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
