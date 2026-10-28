module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalPlanes
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.Structure
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The original cover seed and fifteen-point permutation quotient

In the five-dimensional branch of the ordinary A₆ endgame, two-perfectness
lifts the constant line through the central kernel V₁. Thus the actual
U₁ = C_{U_H}(K) is its full preimage. The weight-four seed misses this line,
so V∩U₁=V₁, |U₁|=4 and |U_H:V₃U₁|=4. Normalization also gives
[L₁T,U₁]≤V₁ and LT-normalization of U₀=⟨U₁^L⟩.

The original natural L-action generates V from V₁ and constructs the
faithful actor LT/C_LT(V) with its literal L₁T stabilizer. Its fifteen
cosets therefore give an equivariant surjection onto the actual U₀/V.
Reindexing along the constructed coset equivalence gives the standard
fifteen-pair permutation map, preserving the original actor marking.
Relative normality, elementary abelianness, kernel bounds and all maps
are constructed. The cover's constant line is retained throughout.

The final application obtains the cover coordinates and abelianness from
OriginalPlanes on the full-denominator critical pair. It proves V<U₀ and
surjectivity of the constructed six-letter actor onto S₆. The equality
U₀=U_L, the subsequent module comparison, the 13.4.1 application and
strict denominators still belong to qt-d-138-a6-endgame-source. Earlier
ordinary inputs remain with qt-d-138-six-g2-source. No full 13.8.33
conclusion is asserted here.

Source: Aschbacher--Smith, 13.8.6(5) and the proof of 13.8.33,
printed pp.948,966--968, combined manuscript of 1 March 2004.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FiveSeed
open TransvectionQuotients.FourLocalFactors TransvectionParabolic
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

private theorem original_component_marking
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hTH : (T : Subgroup G) ≤ H)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6)) :
    ∃ eK : Source.starImage H K ≃* alternatingGroup (Fin 6),
      ∀ k : Source.starImage H K, e k = (eK k).val := by
  have hKH : K ≤ H := by
    intro k hk
    change k ∈ (H : Set G)
    rw [hprod]
    exact ⟨k,hk,1,(T : Subgroup G).one_mem,mul_one k⟩
  let _ := hK.perfect
  have hp : IsPPerfect 2 (K.subgroupOf H) := by
    intro N hN hq
    let _ := hN
    have hs : Subsingleton ((K.subgroupOf H) ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent ((K.subgroupOf H) ⧸ N) hq.isNilpotent
    apply eq_top_iff.mpr
    intro k _
    exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)
  have hr : pResidual 2 H = K.subgroupOf H :=
    pResidual_eq_of_subnormal_product (K.subgroupOf H) ((T : Subgroup G).subgroupOf H)
      hK.subnormal hp T.isPGroup'.comap_subtype (by
        intro x
        have hx : (x : G) ∈ (K : Set G) * (T : Set G) := hprod ▸ x.property
        obtain ⟨k,hk,t,ht,he⟩ := hx
        exact ⟨⟨k,hKH hk⟩,hk,⟨t,hTH ht⟩,ht,Subtype.ext he⟩)
  have hi : (Source.starImage H K).map e.toMonoidHom = alternatingGroup (Fin 6) := by
    change ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).map e.toMonoidHom = _
    rw [← hr,map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _),
      map_pResidual_of_surjective 2 _ e.surjective,Equiv.Perm.twoResidual_eq_alternating]
  refine ⟨(e.subgroupMap _).trans (MulEquiv.subgroupCongr hi),fun _ => rfl⟩

private theorem component_perfect (K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) : IsPPerfect 2 K := by
  let _ := hK.perfect
  let _ : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).surjective
  intro N hN hp
  let _ := hN
  have hs : Subsingleton (K ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro k _
  exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)

/-- The centralizer seed is the full inverse image of the constant line. -/
theorem original_cover_seed
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6))
    (hF : ∀ g v, F (tildeRepresentation H _ V₁ a g v) =
      BinaryPermutation.coreRepresentation (Fin 6) (e g) (F v))
    (hp : (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap =
      Representation.SixLetterRadicalDisplacement.W) :
    (∀ u : Source.UH H V₃, (u : G) ∈ Source.U1 H K V₃ ↔
      F (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)) = 0 ∨
      F (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)) = oneVector) ∧
    V.relIndex (Source.U1 H K V₃) = 2 ∧
    ⁅sourceOne L T V₁ ⊔ (T : Subgroup G),Source.U1 H K V₃⁆ ≤ V₁ ∧
    L ⊔ (T : Subgroup G) ≤ normalizer (Source.U0 L H K V₃ : Set G) ∧
    V ⊓ Source.U1 H K V₃ = V₁ := by
  have hKH : K ≤ H := by
    intro k hk
    change k ∈ (H : Set G)
    rw [hprod]
    exact ⟨k,hk,1,(T : Subgroup G).one_mem,mul_one k⟩
  let _ := SectionStructure.component_normal_of_product H K T hKH h.T_le_H hK T.isPGroup'
    (by
      intro x
      have hx : (x : G) ∈ (K : Set G) * (T : Set G) := hprod ▸ x.property
      exact hx)
  have hHK : H ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKH).mp inferInstance
  have hL : sourceOne L T V₁ ⊔ (T : Subgroup G) ≤ H := hHz.1.2
  have hline := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)
  let _ : IsElementaryAbelian 2 V₁ := IsElementaryAbelian.of_le (d.line_le_uh H)
  have hc : V₁ ≤ centralizer (K : Set G) := le_centralizer_iff.mpr (hKH.trans h.H_centralizes)
  let q := coverProjection H V₃ V₁ F
  obtain ⟨eK,heK⟩ := original_component_marking K hK h.T_le_H hprod e
  let α := eK.toMonoidHom.comp (starProjection H K hKH)
  have hα : Function.Surjective α := eK.surjective.comp (starProjection_surjective H K hKH)
  have hKU : K ≤ normalizer (Source.UH H V₃ : Set G) := hKH.trans (le_normalizer_conjugateSpanBy _ _)
  have heq : ∀ (k : K) (u : Source.UH H V₃),
      (q ⟨(k : G) * u * (k : G)⁻¹,(mem_normalizer_iff.mp (hKU k.property) u).mp u.property⟩).toAdd =
        BinaryPermutation.alternatingCoreRepresentation (Fin 6) (α k) (q u).toAdd := by
    intro k u
    have hh := hF (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k))
      (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u))
    change F (Additive.ofMul (a.action (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k))
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u))) = _ at hh
    rw [a.conjugation] at hh
    rw [show e (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) = (α k).val from
      heK (starProjection H K hKH k)] at hh
    exact hh
  have hfixed := centralizer_iff_coordinates (Source.UH H V₃) V₁ K (component_perfect K hKH hK)
    hc hKU q (coverProjection_kernel H V₃ V₁ F) α hα heq
  have hweight : ∀ u : Source.UH H V₃, (u : G) ∈ V₃ →
      (q u).toAdd = 0 ∨ Fintype.card {i : Fin 6 // (q u).toAdd.val i ≠ 0} = 4 := by
    intro u hu
    have hw : (q u).toAdd ∈ Representation.SixLetterRadicalDisplacement.W := by
      rw [← hp]
      exact ⟨_,⟨u,hu,rfl⟩,rfl⟩
    simpa only [Fintype.card_subtype, BinaryPermutation.wordWeight] using
      Representation.SixLetterRadicalDisplacement.seed_weight _ hw
  refine ⟨?_, centralizer_seed_index _ V₁ K (component_perfect K hKH hK) hc hKU q
      (coverProjection_kernel H V₃ V₁ F) α hα heq V V₃ (coverProjection_surjective H V₃ V₁ F)
      (seed_intersection d h c hDH hDg) hline hweight,
    centralizer_commutator_le _ V₁ K (component_perfect K hKH hK) hc hKU q
      (coverProjection_kernel H V₃ V₁ F) α hα heq _
      (hL.trans (le_normalizer_conjugateSpanBy _ _))
      (hL.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))
      (centralizer_normalized K _ (hL.trans hHK)),
    U0_normalized L H K T V₃ h.T_le_H (h.T_le_H.trans hHK) d.normalizes_L, ?_⟩
  · intro u
    exact (and_iff_right u.property).trans (hfixed u)
  · apply le_antisymm _ (le_inf hline (le_inf (d.line_le_uh H) hc))
    intro u hu
    have hv3 : u ∈ V₃ := (seed_intersection d h c hDH hDg) ▸ ⟨hu.1,hu.2.1⟩
    have hf := (hfixed ⟨u,hu.2.1⟩).mp hu.2.2
    have hz := hf.resolve_right (constant_not_weight_four _ (hweight ⟨u,hu.2.1⟩ hv3))
    exact (coverProjection_kernel H V₃ V₁ F _).mp hz


/-- The actual fifteen-point permutation quotient, retaining its centralizer
actor kernel, conjugation formula and literal stabilizer cosets. -/
structure CoverPermutationData (L H K T L₁ V₃ V : Subgroup G) where
  contains : V ≤ Source.U0 L H K V₃
  normalizes : L ⊔ T ≤ normalizer (Source.U0 L H K V₃ : Set G)
  normal : (V.subgroupOf (Source.U0 L H K V₃)).Normal
  elementary : let _ := normal; IsElementaryAbelian 2 (Source.U0section L H K V₃ V)
  actor_normal : (actorKernel (L ⊔ T) V).Normal
  permutation : let _ := actor_normal;
    ((L ⊔ T : Subgroup G) ⧸ actorKernel (L ⊔ T) V) →* Equiv.Perm (Fin 6)
  faithful : let _ := actor_normal; Function.Injective permutation
  alternating : let _ := actor_normal;
    ∀ g : alternatingGroup (Fin 6), ∃ x, permutation x = g.val
  pair : BinaryPermutation.SixPairsQuadratic.Pair
  stabilizer : let _ := actor_normal;
    ∀ x, x ∈ ((L₁ ⊔ T).subgroupOf (L ⊔ T)).map (QuotientGroup.mk' (actorKernel (L ⊔ T) V)) ↔
      BinaryPermutation.SixPairsQuadratic.pairPerm (permutation x) pair = pair
  action : let _ := normal; let _ := elementary; let _ := actor_normal;
    Representation (ZMod 2) ((L ⊔ T : Subgroup G) ⧸ actorKernel (L ⊔ T) V)
      (Additive (Source.U0section L H K V₃ V))
  conjugation : let _ := normal; let _ := elementary; let _ := actor_normal;
    SectionConjugationAlong (L ⊔ T) (Source.U0 L H K V₃) V
      (QuotientGroup.mk' (actorKernel (L ⊔ T) V)) normalizes action
  cosets : let _ := actor_normal;
    (((L ⊔ T : Subgroup G) ⧸ actorKernel (L ⊔ T) V) ⧸
      ((L₁ ⊔ T).subgroupOf (L ⊔ T)).map (QuotientGroup.mk' (actorKernel (L ⊔ T) V))) ≃
        BinaryPermutation.SixPairsQuadratic.Pair
  equivariant : let _ := actor_normal;
    ∀ x y, cosets (x • y) = BinaryPermutation.SixPairsQuadratic.pairPerm (permutation x) (cosets y)
  quotient : let _ := normal; let _ := elementary; let _ := actor_normal;
    let A := ((L ⊔ T : Subgroup G) ⧸ actorKernel (L ⊔ T) V)
    let P := ((L₁ ⊔ T).subgroupOf (L ⊔ T)).map (QuotientGroup.mk' (actorKernel (L ⊔ T) V))
    let _ : Fintype (A ⧸ P) := Fintype.ofFinite _
    Nonempty {q : Representation.IntertwiningMap
      ((BinaryPermutation.representation (A ⧸ P)).comp
        (MulAction.toPermHom A (A ⧸ P))) action // Function.Surjective q}

/-- The cover seed constructs the source permutation quotient, without
assuming any spanning vector, coset marking or permutation map. -/
theorem original_cover_permutation
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6))
    (hF : ∀ g v, F (tildeRepresentation H _ V₁ a g v) =
      BinaryPermutation.coreRepresentation (Fin 6) (e g) (F v))
    (hp : (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap =
      Representation.SixLetterRadicalDisplacement.W) :
    Nonempty (CoverPermutationData L H K (T : Subgroup G) (sourceOne L T V₁) V₃ V) := by
  classical
  obtain ⟨_,hi,hcomm,hn,_⟩ := original_cover_seed d h c hDH hDg hHz K hK hprod a e F hF hp
  let _ := local_elementary d
  let _ := d.abelian_span
  let _ := SectionStructure.VH_commutative_of_global_span G₁ H V hHz.2.1
  let nc : BarMarking.NaturalCoordinates L V (le_sup_left.trans d.normalizes_V) := {
    action := d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' _)
    surjective := d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _)
    equiv := d.coordinate.toAdditiveLeft.toLinearEquiv (ZMod.map_smul _)
    conjugation := d.conjugation }
  have hline := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)
  have hgen : V = conjugateSpanBy V₁ L := V_generated_by_flag L V V₁
    (le_sup_left.trans d.normalizes_V) hline
    (by intro he; have hh := d.line_card; rw [he,card_bot] at hh; contradiction)
    nc.action nc.surjective nc.equiv nc.conjugation
  have hKH : K ≤ H := by
    intro k hk
    change k ∈ (H : Set G)
    rw [hprod]
    exact ⟨k,hk,1,(T : Subgroup G).one_mem,mul_one k⟩
  have hc : V₁ ≤ centralizer (K : Set G) := le_centralizer_iff.mpr (hKH.trans h.H_centralizes)
  have hUL := (Section07.span_UH_L_le_core (localNaturalSetup d) h
    (show IsMulCommutative (Source.UH H V₃) from inferInstance)).trans (pCoreIn_le 2 _)
  have hres : sourceOne L T V₁ = EarlierCore.localResidual L V₁ :=
    EarlierCore.residual_relative_normalizer_eq L T V₁ T.isPGroup' d.normalizes_L d.line_stable
  let hN := actorKernel_normal (L ⊔ (T : Subgroup G)) V d.normalizes_V
  let _ := hN
  obtain ⟨hCT,f,hfi,hfa,_,_,s,hs,_⟩ := BarMarking.barred_marking_of_natural_coordinates
    L V V₁ (sourceOne L T V₁) T d.normalizes_L d.normalizes_V hline d.line_card d.line_stable
    hres nc eL
  let hZ := U0_relative_normal L H K T V₃ V hUL d.normalizes_V
  let _ := hZ
  let hE := U0_section_elementary L H K T (sourceOne L T V₁) V₃ V V₁
    d.seed_le hUL d.normalizes_V hCT hline hcomm
  let _ := hE
  let _ : Fintype (((L ⊔ (T : Subgroup G) : Subgroup G) ⧸ actorKernel (L ⊔ (T : Subgroup G)) V) ⧸
      ((sourceOne L T V₁ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
        (QuotientGroup.mk' (actorKernel (L ⊔ (T : Subgroup G)) V))) := Fintype.ofFinite _
  obtain ⟨hv,_,ρ,hρ,E,hE',_,q,hq⟩ := U0_permutation_surjection_of_local_data
    L H K T (sourceOne L T V₁) V₃ V V₁ (actorKernel (L ⊔ (T : Subgroup G)) V)
    hgen (d.line_le_uh H) hc hn d.normalizes_V
    (U0_kernel_commutator L H K T (sourceOne L T V₁) V₃ V V₁ hUL d.normalizes_V hCT hline hcomm)
    hi hcomm f hfa s hs
  exact ⟨⟨hv,hn,hZ,hE,hN,f,hfi,hfa,s,hs,ρ,hρ,E,hE',⟨⟨q,hq⟩⟩⟩⟩

/-- Orders of the actual fixed seed and its join with V₃. The remaining
local section U_H/(V₃U₁) is a four-group. -/
theorem original_cover_seed_orders
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6))
    (hF : ∀ g v, F (tildeRepresentation H _ V₁ a g v) =
      BinaryPermutation.coreRepresentation (Fin 6) (e g) (F v))
    (hp : (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap =
      Representation.SixLetterRadicalDisplacement.W) :
    Nat.card (Source.U1 H K V₃) = 4 ∧
    Nat.card (V₃ ⊔ Source.U1 H K V₃ : Subgroup G) = 16 ∧
    (V₃ ⊔ Source.U1 H K V₃).relIndex (Source.UH H V₃) = 4 := by
  obtain ⟨_,hi,_,_,hv⟩ := original_cover_seed d h c hDH hDg hHz K hK hprod a e F hF hp
  have hm := relIndex_mul_card_of_le (show V ⊓ Source.U1 H K V₃ ≤ Source.U1 H K V₃ from inf_le_right)
  rw [inf_relIndex_right,hi,hv,d.line_card] at hm
  have hu : Nat.card (Source.U1 H K V₃) = 4 := hm.symm
  have h₁ : V₁ ≤ Source.U1 H K V₃ := hv.ge.trans inf_le_right
  have hinter : V₃ ⊓ Source.U1 H K V₃ = V₁ := le_antisymm
    ((inf_le_inf d.seed_le le_rfl).trans hv.le)
    (le_inf (d.line_le_plane.trans d.plane_le_seed) h₁)
  have hn : Source.U1 H K V₃ ≤ normalizer (V₃ : Set G) :=
    (((show Source.U1 H K V₃ ≤ Source.UH H V₃ from inf_le_left).trans
      (le_centralizer (Source.UH H V₃))).trans
      (centralizer_le (le_conjugateSpanBy V₃ H))).trans (Subgroup.centralizer_le_normalizer _)
  have hpord := card_mul_eq_card_inf_mul_card_sup_of_normalizes V₃ (Source.U1 H K V₃) hn
  rw [d.seed_card,hu,hinter,d.line_card] at hpord
  have hs : Nat.card (V₃ ⊔ Source.U1 H K V₃ : Subgroup G) = 16 := by omega
  have hq : Nat.card (Source.Utilde H V₃ V₁) = 32 := by
    change Nat.card (Additive (Source.Utilde H V₃ V₁)) = 32
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,F.finrank_eq,
      BinaryPermutation.finrank_core]
    rfl
  have hUH := relIndex_mul_card_of_le (d.line_le_uh H)
  change Nat.card (Source.Utilde H V₃ V₁) * Nat.card V₁ = Nat.card (Source.UH H V₃) at hUH
  rw [hq,d.line_card] at hUH
  have hi' := relIndex_mul_card_of_le (sup_le (le_conjugateSpanBy V₃ H)
    (show Source.U1 H K V₃ ≤ Source.UH H V₃ from inf_le_left))
  change (V₃ ⊔ Source.U1 H K V₃).relIndex (Source.UH H V₃) *
    Nat.card (V₃ ⊔ Source.U1 H K V₃ : Subgroup G) = Nat.card (Source.UH H V₃) at hi'
  rw [hs,← hUH] at hi'
  exact ⟨hu,hs,by omega⟩

private def pairReindex {Ω Ψ : Type*} (c : Ω ≃ Ψ) :
    (Ψ → ZMod 2) ≃ₗ[ZMod 2] (Ω → ZMod 2) where
  toFun v x := v (c x)
  invFun v x := v (c.symm x)
  left_inv v := by ext x; simp
  right_inv v := by ext x; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The literal coset quotient is a quotient of the standard fifteen-pair
module, with its original actor marking unchanged. -/
theorem CoverPermutationData.pair_surjection
    {L H K T L₁ V₃ V : Subgroup G} (p : CoverPermutationData L H K T L₁ V₃ V) :
    let _ := p.normal; let _ := p.elementary; let _ := p.actor_normal;
    ∃ q : Representation.IntertwiningMap
      (BinaryPermutation.SixPairsQuadratic.action.comp p.permutation) p.action,
      Function.Surjective q := by
  classical
  let _ := p.normal
  let _ := p.elementary
  let _ := p.actor_normal
  let A := ((L ⊔ T : Subgroup G) ⧸ actorKernel (L ⊔ T) V)
  let P := ((L₁ ⊔ T).subgroupOf (L ⊔ T)).map (QuotientGroup.mk' (actorKernel (L ⊔ T) V))
  let _ : Fintype (A ⧸ P) := Fintype.ofFinite _
  obtain ⟨q,hq⟩ := p.quotient
  let E := pairReindex p.cosets
  have hE (a : A) (v : BinaryPermutation.Full BinaryPermutation.SixPairsQuadratic.Pair) :
      E (BinaryPermutation.SixPairsQuadratic.action (p.permutation a) v) =
        BinaryPermutation.representation (A ⧸ P) (MulAction.toPermHom A (A ⧸ P) a) (E v) := by
    ext x
    change v ((BinaryPermutation.SixPairsQuadratic.pairHom (p.permutation a)).symm (p.cosets x)) =
      v (p.cosets ((MulAction.toPermHom A (A ⧸ P) a).symm x))
    have hh := p.equivariant a⁻¹ x
    change p.cosets ((MulAction.toPermHom A (A ⧸ P)) a⁻¹ x) =
      (BinaryPermutation.SixPairsQuadratic.pairHom.comp p.permutation) a⁻¹ (p.cosets x) at hh
    simpa only [map_inv,Equiv.Perm.inv_def,MonoidHom.comp_apply] using congrArg v hh.symm
  let f : Representation.IntertwiningMap
      (BinaryPermutation.SixPairsQuadratic.action.comp p.permutation) p.action := {
    toLinearMap := q.toLinearMap.comp E.toLinearMap
    isIntertwining' := by
      intro a
      apply LinearMap.ext
      intro v
      change q (E (BinaryPermutation.SixPairsQuadratic.action (p.permutation a) v)) =
        p.action a (q (E v))
      rw [hE]
      exact Representation.IntertwiningMap.isIntertwining _ _ q a (E v) }
  exact ⟨f,hq.comp E.surjective⟩

/-- The constructed quotient has dimension at most fifteen. -/
theorem CoverPermutationData.finrank_le_fifteen
    {L H K T L₁ V₃ V : Subgroup G} (p : CoverPermutationData L H K T L₁ V₃ V) :
    let _ := p.normal; let _ := p.elementary;
    Module.finrank (ZMod 2) (Additive (Source.U0section L H K V₃ V)) ≤ 15 := by
  classical
  let _ := p.normal
  let _ := p.elementary
  let _ := p.actor_normal
  let A := ((L ⊔ T : Subgroup G) ⧸ actorKernel (L ⊔ T) V)
  let P := ((L₁ ⊔ T).subgroupOf (L ⊔ T)).map (QuotientGroup.mk' (actorKernel (L ⊔ T) V))
  let _ : Fintype (A ⧸ P) := Fintype.ofFinite _
  obtain ⟨q,hq⟩ := p.quotient
  have hc : Fintype.card (A ⧸ P) = 15 := (Fintype.card_congr p.cosets).trans pair_card
  have hd := LinearMap.finrank_le_finrank_of_surjective (f := q.toLinearMap) hq
  rw [Module.finrank_pi,hc] at hd
  exact hd

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- In the original full-denominator branch the constructed six-letter
marking covers S₆ itself, not merely its alternating subgroup. -/
theorem original_cover_permutation_surjective
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    {K : Subgroup G}
    (p : CoverPermutationData L H K (T : Subgroup G) (sourceOne L T V₁) V₃ V) :
    let _ := p.actor_normal; Function.Surjective p.permutation := by
  let _ := p.actor_normal
  obtain ⟨eb⟩ := exists_full_denominators_bar_equiv d h c hDH hDg
  let _ := barKernel_normal (L ⊔ (T : Subgroup G)) V d.normalizes_V
  have hc : Nat.card ((L ⊔ (T : Subgroup G) : Subgroup G) ⧸ actorKernel (L ⊔ (T : Subgroup G)) V) =
      Nat.card (Equiv.Perm (Fin 6)) :=
    Nat.card_congr ((barEquivImage (L ⊔ (T : Subgroup G)) V d.normalizes_V).trans eb).toEquiv
  exact ((Nat.bijective_iff_injective_and_card p.permutation).mpr ⟨p.faithful,hc⟩).2

/-- Application to the actual full-denominator source branch. The earlier
local-plane argument supplies abelianness and the cover coordinates; this
construction supplies the constant seed, its four-group residual section,
and the actual fifteen-point permutation quotient. -/
theorem full_denominators_cover_permutation
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hH : H = G₁)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (earlier1354 : EarlierCore.Earlier1354 T L V)
    (earlier1376 : Marking.NaturalSection.Earlier1376 L (EarlierCore.localResidual L V₁)
      T (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁) :
    IsMulCommutative (Source.UL L H V₃) ∧
    ∃ p : CoverPermutationData L H K (T : Subgroup G) (sourceOne L T V₁) V₃ V,
      V < Source.U0 L H K V₃ ∧
      V ⊓ Source.U1 H K V₃ = V₁ ∧
      Nat.card (Source.U1 H K V₃) = 4 ∧
      Nat.card (V₃ ⊔ Source.U1 H K V₃ : Subgroup G) = 16 ∧
      (V₃ ⊔ Source.U1 H K V₃).relIndex (Source.UH H V₃) = 4 ∧
      (let _ := p.normal; let _ := p.elementary;
        Module.finrank (ZMod 2) (Additive (Source.U0section L H K V₃ V)) ≤ 15) ∧
      (let _ := p.actor_normal; Function.Surjective p.permutation) ∧
      (let _ := p.normal; let _ := p.elementary; let _ := p.actor_normal;
        ∃ q : Representation.IntertwiningMap
          (BinaryPermutation.SixPairsQuadratic.action.comp p.permutation) p.action,
          Function.Surjective q) := by
  obtain ⟨hab,F,hF,hp⟩ := full_denominators_abelian_cover d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
  obtain ⟨p⟩ := original_cover_permutation d h c hDH hDg hHz K hK hprod eL a e F hF hp
  obtain ⟨_,hi,_,_,hv⟩ := original_cover_seed d h c hDH hDg hHz K hK hprod a e F hF hp
  obtain ⟨hu,hs,hr⟩ := original_cover_seed_orders d h c hDH hDg hHz K hK hprod a e F hF hp
  have hlt : V < Source.U0 L H K V₃ := lt_of_le_of_ne p.contains (by
    intro he
    have huV : Source.U1 H K V₃ ≤ V := (le_conjugateSpanBy _ _).trans he.ge
    have hh := relIndex_eq_one.mpr huV
    rw [hi] at hh
    contradiction)
  exact ⟨hab,p,hlt,hv,hu,hs,hr,p.finrank_le_fifteen,
    original_cover_permutation_surjective d h c hDH hDg p,p.pair_surjection⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
