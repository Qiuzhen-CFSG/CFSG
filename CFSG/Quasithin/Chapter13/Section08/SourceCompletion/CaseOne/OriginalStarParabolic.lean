module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalParabolics
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.Cover

/-!
# The H-side parabolic from the original natural seed

The literal star image of LT ∩ H preserves the marked seed plane. It
contains a Sylow two-subgroup of S₆. Its preimage has an H1 quotient in
the original natural action, so it is not a two-group; the star kernel
is a two-group as well. The seed stabilizer has order 48, forcing the
image to be all of H2. This identifies the exact H-side marking used
in the nonabelian-span Steinberg comparison.

No star-parabolic marking is an input. The nonabelian assumption selects
the already proved natural seed model without dropping the cover branch.
OriginalComparison applies this result. The local planes and subsequent
abelian-span endgame remain with qt-d-138-a6-endgame-source, with the
earlier ordinary setup owned by qt-d-138-six-g2-source.
Source: Aschbacher--Smith, 13.8.33, printed pp.966--967.
-/

public section
open Subgroup Representation BinaryPermutation
open scoped IsMulCommutative
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
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6))
    (hF : ∀ g v, F (tildeRepresentation H _ V₁ a g v) =
      naturalRepresentation (Fin 6) (e g) (F v))
    (hp : (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap = canonicalPlane) :
    (Source.starImage H P).map e.toMonoidHom ≤ H2 := by
  rintro b ⟨g,⟨x,hx,rfl⟩,rfl⟩
  apply (canonicalPlane_stabilizer _).mp
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨w,hw,rfl⟩
    rw [← hp] at hw ⊢
    obtain ⟨z,hz,rfl⟩ := hw
    obtain ⟨u,hu,rfl⟩ := hz
    change naturalRepresentation (Fin 6) (e (QuotientGroup.mk' (pCore 2 H) x))
      (F (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u))) ∈ _
    rw [← hF]
    refine ⟨_,?_,rfl⟩
    change a.action (QuotientGroup.mk' (pCore 2 H) x)
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) ∈
        SolvableExclusion.tildeImage (Source.UH H V₃) V₁ V₃
    rw [a.conjugation]
    exact mem_map_of_mem _ ((mem_normalizer_iff.mp (hPN hx) u.val).mp hu)
  · exact (LinearEquiv.ofBijective _
      ((naturalRepresentation (Fin 6)).apply_bijective _)).finrank_map_eq _

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
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6))
    (hF : ∀ g v, F (tildeRepresentation H _ V₁ a g v) =
      naturalRepresentation (Fin 6) (e g) (F v))
    (hp : (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap = canonicalPlane) :
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

/-- The H-side parabolic marking is forced by the actual natural seed,
Sylow containment, and the original point-parabolic quotient. -/
theorem nonabelian_star_parabolic
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (hn : ¬ IsMulCommutative (Source.UL L H V₃)) :
    (Source.starImage H ((L ⊔ (T : Subgroup G)) ⊓ H)).map e.toMonoidHom = H2 := by
  obtain ⟨F,hF,hp⟩ := natural_model_of_nonabelian d h c hDH hDg hcentral a e model hn
  obtain ⟨eb⟩ := exists_full_denominators_bar_equiv d h c hDH hDg
  obtain ⟨d',hp₁,_⟩ := exists_original_parabolic_coordinates d hH eb
    (TransvectionQuotients.FourLocalFactors.BarQuotients.sourceResidual L (T : Subgroup G) V₂) rfl
  exact star_parabolic_of_seed d' h hp₁ a e F hF hp

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
