module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SevenMarking
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SeedNormalizerRank
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.NormalizerTheta
public import Theory.Representation.BinaryPermutation.SevenTriangle
/-!
# The original seven-letter seed plane and covered local quotient

The full marked action carries the original V₂ point to a pair vector.
The two-perfect point residual is transitive on the three nonzero vectors
of V₃/V₁. They therefore all have weight two and form the triangle plane.
Its alternating stabilizer has three-rank two. The literal component
quotient transfers that rank to N_K(V₃), and 13.7.5(4) gives the covered
local quotient and exact theta subgroup.

Source: Aschbacher–Smith, 13.7.6(3b), printed p.939, contained-L₁ branch.
-/
@[expose] public section
open Subgroup Representation BinaryPermutation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionParabolic.Marking
open SevenParabolic
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
include d

private theorem seed_weights_two
    (hL₁H : sourceOne L T V₁ ≤ H)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (f : Section08.Source.Hstar H →* Equiv.Perm (Fin 7))
    (eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 7))
    (he : ∀ a w, eV (ρ a w) = coreRepresentation (Fin 7) (f a) (eV w))
    (v : V₂) (i j : Fin 7) (hij : i ≠ j)
    (hv : (eV (seedVector H V₃ V₁ ⟨v,d.plane_le_seed v.property⟩)).val =
      Pi.single i 1 + Pi.single j 1) :
    ∀ w ∈ (sectionImage H V₃ V₁ V₃).map eV.toLinearMap,
      w ≠ 0 → weight w = 2 := by
  let u := seedVector H V₃ V₁ ⟨v,d.plane_le_seed v.property⟩
  have hp : eV u = SevenTriangle.pair i j := Subtype.ext hv
  have hwt : weight (eV u) = 2 := hp ▸ SevenTriangle.pair_weight i j hij
  have hu : u ≠ 0 := by
    intro hz
    rw [hz,map_zero] at hwt
    have hw0 : weight (0 : Space) = 0 := by decide
    omega
  have hum : u ∈ sectionImage H V₃ V₁ V₃ :=
    ⟨⟨v,le_conjugateSpanBy V₃ H (d.plane_le_seed v.property)⟩,d.plane_le_seed v.property,rfl⟩
  rintro _ ⟨w,hw,rfl⟩ hw0
  obtain ⟨l,hl⟩ := seed_section_nonzero_orbit d hL₁H ρ hρ u hum hu w hw
    (fun h => hw0 (h ▸ map_zero eV))
  change weight (eV w) = 2
  rw [←hl,he,weight_permute]
  exact hwt

/-- The actual source seed has the seven-letter triangle geometry and rank-two normalizer. -/
theorem seven_seed_geometry_of_one_le
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hcentral : primeRank 3 (centralizer (V₂ : Set G)) ≤ 1)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (alternatingNaturalRepresentation (Fin 7)) eK) :
    (H : Set G) = (K : Set G) * (T : Set G) ∧
    primeRank 3 (K ⊓ normalizer (V₃ : Set G) : Subgroup G) = 2 ∧
    ∃ (f : Section08.Source.Hstar H →* Equiv.Perm (Fin 7))
      (eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 7))
      (i j k : Fin 7),
      Function.Injective f ∧
      (∀ t : Section08.Source.starImage H K, f t = (componentModelEquiv hKH hK eK t).val) ∧
      (∀ a w, eV (ρ a w) = coreRepresentation (Fin 7) (f a) (eV w)) ∧
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (sectionImage H V₃ V₁ V₃).map eV.toLinearMap =
        Submodule.span (ZMod 2) {SevenTriangle.pair i j,SevenTriangle.pair i k} ∧
      ∃ (v : V₂) (a b : Fin 7), a ≠ b ∧
        (eV (seedVector H V₃ V₁ ⟨v,d.plane_le_seed v.property⟩)).val =
          Pi.single a 1 + Pi.single b 1 := by
  obtain ⟨hprod,f,eV,v,i,j,hf,hfK,he,hij,hv⟩ :=
    seven_marked_full_action_of_one_le d hH hF9 hKH hK hL₁K ρ hρ hcentral eK hs
  let U := (sectionImage H V₃ V₁ V₃).map eV.toLinearMap
  have hw : ∀ w ∈ U, w ≠ 0 → weight w = 2 :=
    seed_weights_two d (hL₁K.trans hKH) ρ hρ f eV he v i j hij hv
  have hd : Module.finrank (ZMod 2) U = 2 :=
    (eV.finrank_map_eq _).trans
      (sectionImage_seed_finrank (d.line_le_plane.trans d.plane_le_seed) d.line_card d.seed_card)
  have heK : ∀ k : K, ∀ w,
      eV (ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) w) =
        alternatingCoreRepresentation (Fin 7) (eK (QuotientGroup.mk' (pCore 2 K) k)) (eV w) := by
    intro k w
    have hc : f (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) =
        (eK (QuotientGroup.mk' (pCore 2 K) k)).val := by
      have hi : inclusion hKH k = ⟨k,hKH k.property⟩ := Subtype.ext rfl
      rw [hi]
      simpa only [componentModelEquiv,MulEquiv.trans_apply,MulEquiv.symm_apply_apply,
        Section08.Components.componentStarEquiv_mk] using
          hfK (Section08.Components.componentStarEquiv H K hKH hK (QuotientGroup.mk' (pCore 2 K) k))
    rw [he,hc]
    rfl
  have hmap : (subspaceStabilizer (alternatingCoreRepresentation (Fin 7)) U).map
      (alternatingGroup (Fin 7)).subtype =
      subspaceStabilizer action U ⊓ alternatingGroup (Fin 7) := by
    ext g
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨ha,a.property⟩
    · intro hg
      exact ⟨⟨g,hg.2⟩,hg.1,rfl⟩
  have hr : primeRank 3 (K ⊓ normalizer (V₃ : Set G) : Subgroup G) = 2 := by
    rw [seed_normalizer_rank_of_model (d.line_le_plane.trans d.plane_le_seed)
      hKH ρ hρ (alternatingCoreRepresentation (Fin 7)) eK eV heK]
    change primeRank 3 (subspaceStabilizer (alternatingCoreRepresentation (Fin 7)) U) = 2
    rw [primeRank_congr 3 ((subspaceStabilizer (alternatingCoreRepresentation (Fin 7)) U).equivMapOfInjective
      (alternatingGroup (Fin 7)).subtype Subtype.val_injective),hmap]
    exact SevenTriangle.plane_stabilizer_rank U hd hw
  obtain ⟨a,b,c,hab,hac,hbc,hU⟩ := SevenTriangle.plane_basis U hd hw
  exact ⟨hprod,hr,f,eV,a,b,c,hf,hfK,he,hab,hac,hbc,hU,v,i,j,hij,hv⟩

/-- The original seven-letter natural component forces the covered local quotient. -/
theorem seven_covered_of_one_le
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hrank : primeRank 3 (centralizer (V₂ : Set G)) ≤ 1)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (alternatingNaturalRepresentation (Fin 7)) eK) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      closure {x : G | x ∈ K ⊓ normalizer (V₃ : Set G) ∧ orderOf x = 3} =
        sourceOne L T V₁ :=
  covered_and_theta_of_one_le_rank_two d h hH hF9 hcentral hKH hK hL₁K
    (seven_seed_geometry_of_one_le d hH hF9 hKH hK hL₁K ρ hρ hrank eK hs).2.1
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
