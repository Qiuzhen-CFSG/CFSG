module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.LinearThreeCovers
public import CFSG.Quasithin.ChapterD.Section02.QuadraticCentralCovers
public import Theory.Representation.BinaryOffender.Homogeneous.LinearThreeInertia

/-!
# Quadratic actors on the original natural central covers

Select a minimum-ratio subgroup of the original placed quadratic actor.
If it centralizes the chosen exchanged component, conjugate it by the
original Sylow exchanger. This retains its Sylow placement, its action
ratio and quadraticity while making it detect the chosen component.

Natural recognition applies to the faithful central quotient of every
homogeneous seed. The central-cover form of D.2.5 then makes the selected
actor stabilize the whole seed, including a possible fixed kernel. Its
literal faithful image with the component on the full normalizer orbit
span has quadratic ratio at most two. Its component automorphisms are inner. The preimage in the original
ambient group normalizes the literal coordinate support inside [U,K].
The final application constructs all these data at H=Mc on the original
U/Z. No split-cover or faithful individual-component actor is assumed.

The remaining cover exclusion must use the paired ambient action: the
intrinsic four-dimensional cover itself has quadratic ratio one. Full
support exhaustion, FF elimination and suitable-vector assembly remain
with qt-e-suitable-component-supports. Original14.6.18 is the explicit
hsolv input whose final discharge remains with qt-e-14625-source.

Source: Aschbacher--Smith D.2.5, F.9.18(3--5), I.1.6 and14.6.22,
printed pp.179,325--326,408,1038.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
section Selection
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open RepresentationReduction.SourceRestrictions.Cases.Exchanged
variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) {K K₀ T B C A : Subgroup D}

omit [Finite D] [FiniteDimensional (ZMod 2) V] in
private theorem quadratic_conjugate {A : Subgroup D} (hq : IsQuadratic ρ A) (g : D) :
    IsQuadratic ρ (A.conjBy g) := by
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
  change ρ (g*a*g⁻¹) (ρ (g*b*g⁻¹) v-v) = ρ (g*b*g⁻¹) v-v
  have hh := congrArg (ρ g) (hq a ha b hb (ρ g⁻¹ v))
  simpa only [map_mul,Module.End.mul_apply,map_sub,ρ.inv_self_apply,
    ρ.self_inv_apply] using hh

omit [Finite D] in
private theorem preserving_conjugate_mem_normalizer
    (geo : ExchangedGeometry K K₀ T B C) {t c : D}
    (ht : t ∈ T) (hc : c ∈ T) (hn : c ∈ normalizer (K : Set D)) :
    t*c*t⁻¹ ∈ normalizer (K : Set D) := by
  let N := normalizer (K : Set D)
  have hsq {s : D} (hs : s ∈ T) : s^2 ∈ N := by
    by_cases hn : s ∈ N
    · exact N.pow_mem hn 2
    · have hret := (geo.pair s hs hn).2.2.2.1
      have he := congrArg (fun U : Subgroup D => U.conjBy s) hret
      rw [conjBy_conjBy,conjBy_conjBy,mul_inv_cancel,conjBy_one] at he
      apply mem_normalizer_iff_map_conj_eq.mpr
      simpa only [pow_two,conjBy,MulEquiv.toMonoidHom_eq_coe] using he
  have he : (t*c)^2*c⁻¹*(t^2)⁻¹ = t*c*t⁻¹ := by simp [pow_two,mul_assoc]
  rw [← he]
  exact N.mul_mem (N.mul_mem (hsq (T.mul_mem ht hc)) (N.inv_mem hn)) (N.inv_mem (hsq ht))

/-- A placed quadratic actor supplies a minimum-ratio quadratic subgroup
which preserves and acts nontrivially on the specified component. -/
private theorem exists_placed_minimal_actor
    (geo : ExchangedGeometry K K₀ T B C) (hAT : A ≤ T)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hd : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K₀ : Set D) = ⊥)
    (hp : A ≤ normalizer (K : Set D)) :
    ∃ J, J ≤ T ∧ J ≤ normalizer (K : Set D) ∧ ¬J ≤ centralizer (K : Set D) ∧
      J ∈ ChapterD.RPlusBound ρ 2 ∧ IsQuadratic ρ J := by
  obtain ⟨J,hJA,hJ⟩ := ChapterD.exists_RPlusBound_subgroup ρ hA
    ((actionRatio_le_nat_iff ρ hA 2).mpr hd)
  have hqJ : IsQuadratic ρ J := fun a ha b hb v => hq a (hJA ha) b (hJA hb) v
  have hn0 : ¬J ≤ centralizer (K₀ : Set D) := by
    intro hj
    apply hJ.1.1.1
    exact le_bot_iff.mp ((le_inf hJA hj).trans_eq hAC)
  by_cases hn : J ≤ centralizer (K : Set D)
  · obtain ⟨t,ht,hout⟩ := geo.moved
    have hpair := (geo.pair t ht hout).1
    refine ⟨J.conjBy t,?_,?_,?_,ChapterD.RPlusBound.map_conj ρ hJ t,quadratic_conjugate ρ hqJ t⟩
    · rintro _ ⟨j,hj,rfl⟩
      exact T.mul_mem (T.mul_mem ht (hAT (hJA hj))) (T.inv_mem ht)
    · rintro _ ⟨j,hj,rfl⟩
      exact preserving_conjugate_mem_normalizer geo ht (hAT (hJA hj)) (hp (hJA hj))
    · intro hj
      apply hn0
      apply le_centralizer_iff.mpr
      rw [← hpair]
      refine sup_le (le_centralizer_iff.mp hn) ?_
      apply le_centralizer_iff.mp
      intro j hjJ l hl
      obtain ⟨k,hk,rfl⟩ := hl
      have hh := hj (mem_map_of_mem (MulAut.conj t).toMonoidHom hjJ) k hk
      have he := congrArg (MulAut.conj t⁻¹) hh
      simpa only [map_mul,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,mul_assoc,
        inv_mul_cancel_left,mul_inv_cancel_left,inv_mul_cancel,mul_inv_cancel,mul_one,one_mul] using he
  · exact ⟨J,hJA.trans hAT,hJA.trans hp,hn,hJ,hqJ⟩


private theorem natural_cover_minimal_actor_data
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ K T I)
    (hAT : A ≤ T) (hA : A ∈ ChapterD.RPlusBound ρ 2) (hq : IsQuadratic ρ A)
    (hn : ¬ A ≤ centralizer (K : Set D))
    (j : K ≃* BinaryLinearThree.Group)
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.isIrrPlus.choose k v) =
      BinaryLinearThree.W (j k) (l v)) :
    ∃ hD : K ⊔ A ≤ subspaceStabilizer ρ I,
      quadraticRatio (imageRepresentation (invariantSubspace ρ (K ⊔ A) I hD).toRepresentation) ≤ 2 ∧
      ∃ hO : K ⊔ A ≤ subspaceStabilizer ρ (orbitSpan ρ T I),
        quadraticRatio (imageRepresentation
          (invariantSubspace ρ (K ⊔ A) (orbitSpan ρ T I) hO).toRepresentation) ≤ 2 ∧
        ∀ a : A, ∃ k : K,
          K.normalizerMonoidHom ⟨a,hI.normalizes (hAT a.property)⟩ = MulAut.conj k := by
  have hf : Function.Injective (centralQuotientRepresentation ρ K I hI.isIrrPlus.choose) := by
    intro x y hxy
    apply j.injective
    apply specialLinearNatural_injective 3
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := l.surjective v
    exact (he x w).symm.trans ((congrArg (fun f => l (f w)) hxy).trans (he y w))
  have hd : 2 < Module.finrank (ZMod 2) (centralQuotient ρ K I) := by
    rw [l.finrank_eq]
    change 2 < Module.finrank (ZMod 2) (Fin 3 → ZMod 2)
    rw [Module.finrank_fin_fun]
    decide
  obtain ⟨hD,hbound⟩ := ChapterD.stable_central_cover_image_bound ρ hI hAT hA hq hf hd hn
  obtain ⟨hO,hOratio⟩ := ChapterD.central_cover_orbit_image_bound ρ hI hAT hA hq hf hn
  refine ⟨hD,hbound,hO,hOratio,?_⟩
  intro a
  exact hI.inner_of_natural_map_eq ρ ⟨a,hAT a.property⟩ j l he
    ((subspace_map_eq_iff ρ I a.val).mpr (hD ((le_sup_right : A ≤ K ⊔ A) a.property)))

end Selection

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Chapter13.Section08.CriticalGeometry.Reorientation
open Chapter13.Section08.Components.SourceModels
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv


private theorem source_nonnormal_placed_minimal_actor
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (A : Subgroup (H ⧸ pCore 2 H))
    (hAT : A ≤ actorImage H T) (hA : QuadraticMember a.representation A)
    (hfaith : A ⊓ centralizer (actorImage H (conjugateSpanBy K (T : Subgroup G)) :
      Set (H ⧸ pCore 2 H)) = ⊥) :
    ∃ (C : Subgroup (H ⧸ pCore 2 H)),
      C ≤ actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H)) ∧
      ¬ C ≤ centralizer (actorImage H K : Set (H ⧸ pCore 2 H)) ∧
      C ∈ ChapterD.RPlusBound a.representation 2 ∧ IsQuadratic a.representation C := by
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H))) := Module.Finite.of_finite
  obtain ⟨_,geo⟩ := source_nonnormal_quotient_geometry
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn
  have hfaith' : A ⊓ centralizer
      (componentOrbit (actorImage H K) (actorImage H T) : Set (H ⧸ pCore 2 H)) = ⊥ := by
    rw [show componentOrbit (actorImage H K) (actorImage H T) =
      actorImage H (conjugateSpanBy K (T : Subgroup G)) from
        quotient_componentOrbit H K T hKH hH.1.2]
    exact hfaith
  obtain ⟨C,hCT,hCN,hCn,hC,hqC⟩ := exists_placed_minimal_actor a.representation
    geo hAT hA.1 hA.2.1 hA.2.2 hfaith'
    (source_nonnormal_quadratic_actor_normalizes
      hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn a A hAT hA hfaith)
  exact ⟨C,le_inf hCT hCN,hCn,hC,hqC⟩

/-- A source homogeneous seed admits a detecting minimum-ratio actor on
the full central cover, with its original support normalized and its
component automorphisms inner. -/
theorem source_nonnormal_seed_minimal_actor
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (A : Subgroup (H ⧸ pCore 2 H))
    (hAT : A ≤ actorImage H T) (hA : QuadraticMember a.representation A)
    (hfaith : A ⊓ centralizer (actorImage H (conjugateSpanBy K (T : Subgroup G)) :
      Set (H ⧸ pCore 2 H)) = ⊥)
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H)))}
    (hI : IsIrrPlusWith a.representation (actorImage H K)
      (actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) I) :
    ∃ (C : Subgroup (H ⧸ pCore 2 H))
      (hCT : C ≤ actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))),
      ¬ C ≤ centralizer (actorImage H K : Set (H ⧸ pCore 2 H)) ∧
      C ∈ ChapterD.RPlusBound a.representation 2 ∧ IsQuadratic a.representation C ∧
      actorImage H K ⊔ C ≤ subspaceStabilizer a.representation I ∧
        ∃ hO : actorImage H K ⊔ C ≤ subspaceStabilizer a.representation
          (orbitSpan a.representation
            (actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) I),
          quadraticRatio (imageRepresentation
            (invariantSubspace a.representation (actorImage H K ⊔ C)
              (orbitSpan a.representation
                (actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) I)
              hO).toRepresentation) ≤ 2 ∧
        (C.comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype ≤
          normalizer ((originalSection a).subspacePreimage I : Set G) ∧
        ∀ c : C, ∃ k : actorImage H K,
          (actorImage H K).normalizerMonoidHom ⟨c,(hCT c.property).2⟩ = MulAut.conj k := by
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H))) := Module.Finite.of_finite
  obtain ⟨C,hCTN,hCn,hC,hqC⟩ := source_nonnormal_placed_minimal_actor
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn a A hAT hA hfaith
  obtain ⟨⟨b⟩,_⟩ := source_nonnormal_irrPlus_cover
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn a A hAT hA hfaith hI.isIrrPlus
  obtain ⟨hD,_,hO,hOratio,hinner⟩ := natural_cover_minimal_actor_data a.representation
    hI hCTN hC hqC hCn b.groupEquiv b.linearEquiv b.intertwines
  refine ⟨C,hCTN,hCn,hC,hqC,hD,hO,hOratio,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    apply ((originalSection a).mem_normalizer_subspacePreimage_iff I x).mpr
    exact (subspace_map_eq_iff a.representation I _).mpr
      (hD ((le_sup_right : C ≤ actorImage H K ⊔ C) hx))
  · exact hinner

/-- At H=Mc, both the homogeneous cover and a detecting quadratic actor
are constructed on the original U/Z. The actor stabilizes the cover and
induces inner component automorphisms; its actual image retains the small
quadratic-ratio bound. -/
theorem terminal_nonnormal_stable_central_cover
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc),
      let _ := hU
      ∃ a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T),
      ∃ (I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
        (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))))
        (hI : IsIrrPlusWith a.representation (actorImage Mc K)
          (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I),
      Nonempty (ChapterB.QuasisimpleSource.ActionEquiv
        (centralQuotientRepresentation a.representation (actorImage Mc K) I hI.isIrrPlus.choose)
        (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3)) ∧
      ∃ (C : Subgroup (Mc ⧸ pCore 2 Mc))
        (hCT : C ≤ actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))),
        ¬ C ≤ centralizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc)) ∧
        C ∈ ChapterD.RPlusBound a.representation 2 ∧ IsQuadratic a.representation C ∧
        actorImage Mc K ⊔ C ≤ subspaceStabilizer a.representation I ∧
          ∃ hO : actorImage Mc K ⊔ C ≤ subspaceStabilizer a.representation
          (orbitSpan a.representation
            (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I),
          quadraticRatio (imageRepresentation
            (invariantSubspace a.representation (actorImage Mc K ⊔ C)
              (orbitSpan a.representation
                (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I)
              hO).toRepresentation) ≤ 2 ∧
          (C.comap (QuotientGroup.mk' (pCore 2 Mc))).map Mc.subtype ≤
            normalizer ((originalSection a).subspacePreimage I : Set G) ∧
          ∀ c : C, ∃ k : actorImage Mc K,
            (actorImage Mc K).normalizerMonoidHom ⟨c,(hCT c.property).2⟩ = MulAut.conj k := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  obtain ⟨hU,a,B,_,hB,_,_,hA,hfaith,_⟩ := terminal_nonnormal_component_span_inputs
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  let := hU
  have hD := source_quotient_component
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK
  let : IsQuasisimple (actorImage Mc K) := hD.2
  let S : Subgroup (Mc ⧸ pCore 2 Mc) := actorImage Mc T ⊓ normalizer
    (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))
  have hp : IsPGroup 2 S := (quotientSylow Mc T hout.1.2).isPGroup'.of_injective
    (inclusion (show S ≤ (quotientSylow Mc T hout.1.2 : Subgroup (Mc ⧸ pCore 2 Mc)) from inf_le_left))
    (inclusion_injective _)
  obtain ⟨I,hI⟩ := exists_isIrrPlusWith_of_faithful a.representation a.faithful
    (actorImage Mc K) S hD.isCComponent.ne_bot inf_le_right hp
  have hAT := source_internal_actor_le_sylow T hout.1.2 B hB
  have hmark := (source_nonnormal_irrPlus_cover hG T hempty hM hunique hmany hcard e hab hsolv
    Mc hout K hKM hK hn a (B.map (QuotientGroup.mk' (pCore 2 Mc)))
    hAT hA hfaith hI.isIrrPlus).1
  exact ⟨hU,a,I,hI,hmark,source_nonnormal_seed_minimal_actor
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK hn a
    (B.map (QuotientGroup.mk' (pCore 2 Mc))) hAT hA hfaith hI⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
