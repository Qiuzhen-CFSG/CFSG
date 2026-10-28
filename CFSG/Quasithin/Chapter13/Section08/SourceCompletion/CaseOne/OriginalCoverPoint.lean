module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalCoverOrbit
public import Theory.Representation.SixLetterCoverPoint

/-!
# The original point section in the proper cover quotient

In the five-dimensional branch of 13.8.33, the original point parabolic
has the full syntheme-stabilizer image in H/O₂(H). The weight-four seed
forces containment, and its Sylow two-subgroup and odd quotient force
equality. The actual V₃U₁ maps to the pair space, with the constant line
retained. Cycling the three pairs proves that no normalized subgroup lies
strictly between V₃U₁ and U_H.

If U₀<U_L, normalization therefore gives U_H∩U₀=V₃U₁ and an image of
order four. The K₂-orbit B=⟨V₃^{K₂}⟩ generates U_H under L₁T, so U₂
cannot lie in U₀. Its seed orbit consequently has image of order two.
The final application constructs the literal U_L/U₀ and both subgroup
images, including relative normality and elementary abelianness.

The second local plane, its Steinberg quotient, U₀=U_L, whole-module
permutation comparison, 13.4.1 application and strict-denominator assembly
remain with qt-d-138-a6-endgame-source. The genuine earlier ordinary setup
remains with qt-d-138-six-g2-source; the earlier 13.5.4 and 13.7.6 inputs
remain explicit. The proper-quotient hypothesis is a branch assumption,
not an established source conclusion. This module does not finish 13.8.33.

Source: Aschbacher--Smith, proof of 13.8.33, printed p.967, combined
manuscript of 1 March 2004, using 13.8.6(5) and B.3.4.
-/

public section
open Subgroup Representation BinaryPermutation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

omit [Finite G] in
private theorem star_seed_stabilizer
    (P : Subgroup G) (hPN : P ≤ normalizer (V₃ : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6))
    (hF : ∀ g v, F (tildeRepresentation H _ V₁ a g v) =
      coreRepresentation (Fin 6) (e g) (F v))
    (hp : (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap = Representation.SixLetterRadicalDisplacement.W) :
    (Source.starImage H P).map e.toMonoidHom ≤ H2 := by
  rintro b ⟨g,⟨x,hx,rfl⟩,rfl⟩
  apply Representation.SixLetterCoverPoint.weight_plane_stabilizer
  intro w hw
  rw [← hp] at hw ⊢
  obtain ⟨z,hz,rfl⟩ := hw
  obtain ⟨u,hu,rfl⟩ := hz
  change coreRepresentation (Fin 6) (e (QuotientGroup.mk' (pCore 2 H) x))
    (F (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u))) ∈ _
  rw [← hF]
  refine ⟨_,?_,rfl⟩
  change a.action (QuotientGroup.mk' (pCore 2 H) x)
    (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) ∈
      SolvableExclusion.tildeImage (Source.UH H V₃) V₁ V₃
  rw [a.conjugation]
  exact mem_map_of_mem _ ((mem_normalizer_iff.mp (hPN hx) u.val).mp hu)

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
private theorem original_point_not_two
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hpar : ((((L ⊔ (T : Subgroup G)) ⊓ H).subgroupOf (L ⊔ (T : Subgroup G))).map
      (Section07.NaturalAction.permutation (localNaturalSetup d))) = H1) :
    ¬ IsPGroup 2 ((L ⊔ (T : Subgroup G)) ⊓ H : Subgroup G) := by
  intro ht
  have hb : IsPGroup 2 ((((L ⊔ (T : Subgroup G)) ⊓ H).subgroupOf
      (L ⊔ (T : Subgroup G)))) := ht.comap_subtype
  have hi := hb.map (Section07.NaturalAction.permutation (localNaturalSetup d))
  rw [hpar] at hi
  have hc : Nat.card H1 = 48 := by
    let g : Equiv.Perm (Fin 6) := Equiv.swap 0 4 * Equiv.swap 1 5
    have he : pair 4 5 = g • pair 0 1 := by decide
    exact (Nat.card_congr (MulAction.stabilizerEquivStabilizer he).toEquiv).symm.trans
      duadStabilizer_order
  obtain ⟨n,hn⟩ := hi.exists_card_eq
  rw [hc] at hn
  have hd : 3 ∣ 2 ^ n := hn ▸ (by decide : 3 ∣ 48)
  exact (by decide : ¬ 3 ∣ 2) ((by decide : Nat.Prime 3).dvd_of_dvd_pow hd)

private theorem star_parabolic_of_seed
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hpar : ((((L ⊔ (T : Subgroup G)) ⊓ H).subgroupOf (L ⊔ (T : Subgroup G))).map
      (Section07.NaturalAction.permutation (localNaturalSetup d))) = H1)
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6))
    (hF : ∀ g v, F (tildeRepresentation H _ V₁ a g v) =
      coreRepresentation (Fin 6) (e g) (F v))
    (hp : (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap = Representation.SixLetterRadicalDisplacement.W) :
    (Source.starImage H ((L ⊔ (T : Subgroup G)) ⊓ H)).map e.toMonoidHom = H2 := by
  let P := (L ⊔ (T : Subgroup G)) ⊓ H
  let q : H →* Equiv.Perm (Fin 6) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let B := (P.subgroupOf H).map q
  have hB : (Source.starImage H P).map e.toMonoidHom = B := map_map _ _ _
  have hPN : P ≤ normalizer (V₃ : Set G) := by
    change (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).LT ⊓
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).H ≤ _
    rw [h.LT_inf_H_eq]
    exact h.local_normalizes
  have hle : B ≤ H2 := hB ▸ star_seed_stabilizer P hPN a e F hF hp
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hTH : (T : Subgroup G) ≤ H := h.T_le_H
  let S := (T.subtype hTH).mapSurjective hq
  have hS : (S : Subgroup (Equiv.Perm (Fin 6))) ≤ B := by
    dsimp only [S]
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype]
    apply map_mono
    intro x hx
    exact ⟨mem_sup_right hx,hTH hx⟩
  have hSc : Nat.card S = 16 :=
    (Nat.card_congr (S.equiv borelSylow).toEquiv).trans borel_order
  have hd : 16 ∣ Nat.card B := hSc ▸ card_dvd_of_le hS
  have hu : Nat.card B ∣ 48 := by
    exact synthemeStabilizer_order ▸ card_dvd_of_le hle
  have hn : ¬ IsPGroup 2 B := by
    intro ht
    have hk : q.ker = pCore 2 H := by
      ext x
      change e (QuotientGroup.mk' (pCore 2 H) x) = 1 ↔ x ∈ pCore 2 H
      rw [map_eq_one_iff e e.injective]
      exact QuotientGroup.eq_one_iff x
    have hp2 := (ht.comap_of_ker_isPGroup q (hk ▸ pCore_isPGroup)).to_le
      (le_comap_map q (P.subgroupOf H))
    exact original_point_not_two d hpar
      (hp2.of_equiv (subgroupOfEquivOfLe (show P ≤ H from inf_le_right)))
  apply hB.trans
  apply eq_of_le_of_card_ge hle
  change Nat.card synthemeStabilizer ≤ Nat.card B
  rw [synthemeStabilizer_order]
  obtain ⟨k,hk⟩ := hd
  have hk3 : k ∣ 3 := by
    apply (Nat.mul_dvd_mul_iff_left (by decide : 0 < 16)).mp
    simpa only [hk] using hu
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hk3 with he | he
  · have hc : Nat.card B = 2 ^ 4 := by rw [hk,he]; decide
    exact (hn (IsPGroup.of_card hc)).elim
  · rw [hk,he]

/-- The actual point parabolic has the full syntheme-stabilizer star image. -/
theorem original_cover_star_parabolic
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hH : H = G₁)
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6))
    (hF : ∀ g v, F (tildeRepresentation H _ V₁ a g v) =
      BinaryPermutation.coreRepresentation (Fin 6) (e g) (F v))
    (hp : (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap =
      Representation.SixLetterRadicalDisplacement.W) :
    (Source.starImage H (sourceOne L T V₁ ⊔ (T : Subgroup G))).map e.toMonoidHom = H2 := by
  obtain ⟨eb⟩ := exists_full_denominators_bar_equiv d h c hDH hDg
  obtain ⟨d',hp₁,_⟩ := exists_original_parabolic_coordinates d hH eb
    (TransvectionQuotients.FourLocalFactors.BarQuotients.sourceResidual L (T : Subgroup G) V₂) rfl
  rw [original_point_parabolic_eq d' hH]
  exact star_parabolic_of_seed d' h hp₁ a e F hF hp


open TransvectionQuotients.FiveSeed

omit [Finite G] in
private theorem cover_coordinate_mem_iff
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6))
    (N : Subgroup G) (hN : V₁ ≤ N) (u : Source.UH H V₃) :
    F (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)) ∈
      (quotientSpace (Source.UH H V₃) V₁ N).map F.toLinearMap ↔ (u : G) ∈ N := by
  constructor
  · rintro ⟨z,⟨v,hv,rfl⟩,hz⟩
    have hq := F.injective hz
    have hq' : QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u =
        QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) v := hq.symm
    have hh : u / v ∈ V₁.subgroupOf (Source.UH H V₃) :=
      QuotientGroup.eq_iff_div_mem.mp hq'
    have hm := N.mul_mem (hN hh) hv
    change (u : G) / (v : G) * (v : G) ∈ N at hm
    simpa only [div_mul_cancel] using hm
  · intro hu
    exact ⟨_,⟨u,hu,rfl⟩,rfl⟩

omit [Finite G] in
/-- The original join V₃U₁ maps to the pair space, including its constant line. -/
theorem cover_seed_pair_space
    (K : Subgroup G)
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6))
    (hseed : ∀ u : Source.UH H V₃, (u : G) ∈ Source.U1 H K V₃ ↔
      F (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)) = 0 ∨
      F (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)) = oneVector)
    (hp : (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap =
      Representation.SixLetterRadicalDisplacement.W) :
    (quotientSpace (Source.UH H V₃) V₁ (V₃ ⊔ Source.U1 H K V₃)).map F.toLinearMap =
      Representation.SixLetterRadicalDisplacement.F ⊔ Representation.SixLetterRadicalDisplacement.W := by
  have hfix : (quotientSpace (Source.UH H V₃) V₁ (Source.U1 H K V₃)).map F.toLinearMap =
      Representation.SixLetterRadicalDisplacement.F := by
    rw [Representation.SixLetterRadicalDisplacement.F_eq_constantLine]
    apply le_antisymm
    · rintro z ⟨v,⟨u,hu,rfl⟩,rfl⟩
      change F (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)) ∈ _
      rcases (hseed u).mp hu with he | he
      · rw [he]; exact Submodule.zero_mem _
      · rw [he]; exact Submodule.subset_span rfl
    · apply Submodule.span_le.mpr
      rintro z rfl
      obtain ⟨v,hv⟩ := F.surjective Representation.SixLetterRadicalDisplacement.constant
      obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
      have he : F (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)) =
          oneVector := by rw [hu]; exact hv
      exact ⟨_,⟨u,(hseed u).mpr (Or.inr he),rfl⟩,he⟩
  rw [quotientSpace_sup (Source.UH H V₃) V₁ V₃ (Source.U1 H K V₃)
    (le_conjugateSpanBy _ _) inf_le_left,
    Submodule.map_sup,hp,hfix,sup_comm]

omit [Finite G] in
/-- Irreducibility of the literal first local section, expressed as the
absence of an intermediate normalized subgroup above V₃U₁. -/
theorem cover_point_dichotomy
    (K R N : Subgroup G) (h13 : V₁ ≤ V₃)
    (hRN : R ≤ normalizer (N : Set G))
    (hCN : V₃ ⊔ Source.U1 H K V₃ ≤ N)
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6))
    (hF : ∀ g v, F (tildeRepresentation H _ V₁ a g v) =
      coreRepresentation (Fin 6) (e g) (F v))
    (hpar : (Source.starImage H R).map e.toMonoidHom = H2)
    (hseed : ∀ u : Source.UH H V₃, (u : G) ∈ Source.U1 H K V₃ ↔
      F (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)) = 0 ∨
      F (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)) = oneVector)
    (hp : (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap =
      Representation.SixLetterRadicalDisplacement.W) :
    Source.UH H V₃ ⊓ N = V₃ ⊔ Source.U1 H K V₃ ∨ Source.UH H V₃ ≤ N := by
  let C := V₃ ⊔ Source.U1 H K V₃
  let S := (quotientSpace (Source.UH H V₃) V₁ N).map F.toLinearMap
  have hline : V₁ ≤ C := h13.trans le_sup_left
  have hNline := hline.trans hCN
  have hc := cover_seed_pair_space K F hseed hp
  have hCS : Representation.SixLetterRadicalDisplacement.F ⊔
      Representation.SixLetterRadicalDisplacement.W ≤ S := by
    rw [← hc]
    rintro z ⟨v,⟨u,hu,rfl⟩,rfl⟩
    exact ⟨_,⟨u,hCN hu,rfl⟩,rfl⟩
  have hstable : ∀ v ∈ S, coreRepresentation (Fin 6)
      Representation.SixLetterCoverPoint.pairCycle v ∈ S := by
    rintro z ⟨v,⟨u,hu,rfl⟩,rfl⟩
    have hg : Representation.SixLetterCoverPoint.pairCycle ∈ (Source.starImage H R).map
        e.toMonoidHom := hpar.symm ▸ Representation.SixLetterCoverPoint.pairCycle_mem
    obtain ⟨g,⟨x,hx,rfl⟩,hg⟩ := hg
    rw [← hg]
    change coreRepresentation (Fin 6) (e (QuotientGroup.mk' (pCore 2 H) x))
      (F (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u))) ∈ S
    rw [← hF]
    refine ⟨_,?_,rfl⟩
    change a.action (QuotientGroup.mk' (pCore 2 H) x)
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) ∈
        SolvableExclusion.tildeImage (Source.UH H V₃) V₁ N
    rw [a.conjugation]
    exact mem_map_of_mem _ ((mem_normalizer_iff.mp (hRN hx) u.val).mp hu)
  rcases Representation.SixLetterCoverPoint.invariant_dichotomy S hCS hstable with he | he
  · left
    apply le_antisymm
    · intro u hu
      apply (cover_coordinate_mem_iff F C hline ⟨u,hu.1⟩).mp
      rw [hc,← he]
      exact (cover_coordinate_mem_iff F N hNline ⟨u,hu.1⟩).mpr hu.2
    · exact le_inf (sup_le (le_conjugateSpanBy _ _) inf_le_left) hCN
  · right
    intro u hu
    apply (cover_coordinate_mem_iff F N hNline ⟨u,hu⟩).mp
    change _ ∈ S
    rw [he]
    trivial


open TransvectionQuotients TransvectionQuotients.FourLocalFactors TransvectionParabolic
/-- The proper-quotient branch of 13.8.33: the first local image is a
four-group, the seed orbit generates U_H, and the second local subgroup
survives. All statements concern the original subgroups and denominator. -/
theorem original_cover_proper_point
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hH : H = G₁)
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
      Representation.SixLetterRadicalDisplacement.W)
    (earlier1354 : EarlierCore.Earlier1354 T L V)
    (earlier1376 : Marking.NaturalSection.Earlier1376 L (EarlierCore.localResidual L V₁)
      T (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (hproper : Source.U0 L H K V₃ < Source.UL L H V₃) :
    Source.UH H V₃ ⊓ Source.U0 L H K V₃ = V₃ ⊔ Source.U1 H K V₃ ∧
    (Source.U0 L H K V₃).relIndex (Source.UH H V₃) = 4 ∧
    Source.UH H V₃ = conjugateSpanBy (conjugateSpanBy V₃ (Source.K2 H V₂))
      (sourceOne L T V₁ ⊔ (T : Subgroup G)) ∧
    ¬ Source.U2 H V V₂ ≤ Source.U0 L H K V₃ ∧
    (conjugateSpanBy V₃ (Source.K2 H V₂)) ⊓ Source.U0 L H K V₃ =
      V₃ ⊔ Source.U1 H K V₃ ∧
    (Source.U0 L H K V₃).relIndex (conjugateSpanBy V₃ (Source.K2 H V₂)) = 2 := by
  obtain ⟨hseed,_,_,_,_⟩ := original_cover_seed d h c hDH hDg hHz K hK hprod a e F hF hp
  have hpar := original_cover_star_parabolic d h c hDH hDg hH a e F hF hp
  obtain ⟨p⟩ := original_cover_permutation d h c hDH hDg hHz K hK hprod eL a e F hF hp
  obtain ⟨hf,hB,_,_,_,_,_⟩ := original_cover_orbit d h c hDH hDg hHz K hK hprod
    eL a e F hF hp earlier1354 earlier1376
  obtain ⟨_,hC,hindex⟩ := original_cover_seed_orders d h c hDH hDg hHz K hK hprod a e F hF hp
  let R := sourceOne L T V₁ ⊔ (T : Subgroup G)
  let B := conjugateSpanBy V₃ (Source.K2 H V₂)
  let C := V₃ ⊔ Source.U1 H K V₃
  let N := Source.U0 L H K V₃
  have hRL : R ≤ L ⊔ (T : Subgroup G) := (original_point_parabolic_eq d hH).le.trans inf_le_left
  have hCN : C ≤ N := sup_le (d.seed_le.trans p.contains) (le_conjugateSpanBy _ _)
  have hCB : C ≤ B := sup_le (le_conjugateSpanBy _ _) hf
  have hBU : B ≤ Source.UH H V₃ := conjugateSpanBy_mono le_rfl (Source.K2_le H V₂)
  have hRU : R ≤ normalizer (Source.UH H V₃ : Set G) :=
    hHz.1.2.trans (le_normalizer_conjugateSpanBy _ _)
  have hspan : Source.UH H V₃ = conjugateSpanBy B R := by
    have hle := conjugateSpanBy_le hBU hRU
    apply le_antisymm _ hle
    rcases cover_point_dichotomy K R (conjugateSpanBy B R)
      (d.line_le_plane.trans d.plane_le_seed) (le_normalizer_conjugateSpanBy _ _)
      (hCB.trans (le_conjugateSpanBy _ _)) a e F hF hpar hseed hp with hh | hh
    · have hBC : B ≤ C := (le_inf hBU (le_conjugateSpanBy _ _)).trans hh.le
      have hc := Nat.card_le_card_of_injective (inclusion hBC) (inclusion_injective hBC)
      change Nat.card B ≤ Nat.card C at hc
      change Nat.card B = 32 at hB
      change Nat.card C = 16 at hC
      omega
    · exact hh
  have hnot : ¬ Source.UH H V₃ ≤ N := by
    intro hh
    exact (not_le_of_gt hproper) (conjugateSpanBy_le hh (le_sup_left.trans p.normalizes))
  have hinter := (cover_point_dichotomy K R N (d.line_le_plane.trans d.plane_le_seed)
    (hRL.trans p.normalizes) hCN a e F hF hpar hseed hp).resolve_right hnot
  have hidx : N.relIndex (Source.UH H V₃) = 4 := by
    rw [← inf_relIndex_left,hinter]
    exact hindex
  have hU₂not : ¬ Source.U2 H V V₂ ≤ N := by
    intro hh
    apply hnot
    rw [hspan]
    exact conjugateSpanBy_le ((conjugateSpanBy_mono d.seed_le le_rfl).trans hh)
      (hRL.trans p.normalizes)
  obtain ⟨hBint,hBi⟩ := (original_cover_orbit_dichotomy d h c hDH hDg hHz K hK hprod
    eL a e F hF hp earlier1354 earlier1376).resolve_left hU₂not
  exact ⟨hinter,hidx,hspan,hU₂not,hBint,hBi⟩

/-- Application to the actual full-denominator critical pair, constructing
the augmentation cover before the proper-quotient calculation. -/
theorem full_denominators_proper_point
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
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁)
    (hproper : Source.U0 L H K V₃ < Source.UL L H V₃) :
    Source.UH H V₃ ⊓ Source.U0 L H K V₃ = V₃ ⊔ Source.U1 H K V₃ ∧
    (Source.U0 L H K V₃).relIndex (Source.UH H V₃) = 4 ∧
    Source.UH H V₃ = conjugateSpanBy (conjugateSpanBy V₃ (Source.K2 H V₂))
      (sourceOne L T V₁ ⊔ (T : Subgroup G)) ∧
    ¬ Source.U2 H V V₂ ≤ Source.U0 L H K V₃ ∧
    (conjugateSpanBy V₃ (Source.K2 H V₂)) ⊓ Source.U0 L H K V₃ =
      V₃ ⊔ Source.U1 H K V₃ ∧
    (Source.U0 L H K V₃).relIndex (conjugateSpanBy V₃ (Source.K2 H V₂)) = 2 := by
  obtain ⟨_,F,hF,hp⟩ := full_denominators_abelian_cover d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
  exact original_cover_proper_point d h c hDH hDg hH hHz K hK hprod eL a e F hF hp
    earlier1354 earlier1376 hproper

/-- The calculated four-group and surviving seed line in the literal
quotient U_L/U₀. Its elementary structure comes from the proved abelian
span and elementary conjugate generators. -/
theorem full_denominators_proper_point_images
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
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁)
    (hproper : Source.U0 L H K V₃ < Source.UL L H V₃) :
    ∃ hn : ((Source.U0 L H K V₃).subgroupOf (Source.UL L H V₃)).Normal,
      let _ := hn
      IsElementaryAbelian 2 ((Source.UL L H V₃) ⧸
        (Source.U0 L H K V₃).subgroupOf (Source.UL L H V₃)) ∧
      Nat.card (((Source.UH H V₃).subgroupOf (Source.UL L H V₃)).map
        (QuotientGroup.mk' ((Source.U0 L H K V₃).subgroupOf (Source.UL L H V₃)))) = 4 ∧
      Nat.card (((conjugateSpanBy V₃ (Source.K2 H V₂)).subgroupOf (Source.UL L H V₃)).map
        (QuotientGroup.mk' ((Source.U0 L H K V₃).subgroupOf (Source.UL L H V₃)))) = 2 := by
  obtain ⟨hab,F,hF,hp⟩ := full_denominators_abelian_cover d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
  let _ := hab
  let _ : IsMulCommutative (conjugateSpanBy (Source.UH H V₃) L) := hab
  let _ : IsElementaryAbelian 2 (Source.UL L H V₃) :=
    RankDoubling.elementary_conjugateSpan (Source.UH H V₃) L
  let hn : ((Source.U0 L H K V₃).subgroupOf (Source.UL L H V₃)).Normal := inferInstance
  let _ := hn
  obtain ⟨_,hi,_,_,_,hBi⟩ := original_cover_proper_point d h c hDH hDg hH hHz K hK hprod
    eL a e F hF hp earlier1354 earlier1376 hproper
  refine ⟨hn,inferInstance,?_,?_⟩
  · rw [← relIndex_ker,QuotientGroup.ker_mk',
      relIndex_subgroupOf (show Source.UH H V₃ ≤ Source.UL L H V₃ from le_conjugateSpanBy _ _)]
    exact hi
  · have hB : conjugateSpanBy V₃ (Source.K2 H V₂) ≤ Source.UL L H V₃ :=
      (conjugateSpanBy_mono le_rfl (Source.K2_le H V₂)).trans
        (le_conjugateSpanBy (Source.UH H V₃) L)
    rw [← relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf hB]
    exact hBi

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
