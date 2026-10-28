module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.FiveRankTwoStar
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals.GeometricFlags
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalOvergroups
public import Theory.Representation.BinaryRadicalFlag.Normalizer

/-!
# The actual endpoint parabolic in the degree-five star group

The original degree-five residual retains its L4(2) quotient and hence
a factor five. It normalizes the nontrivial radical intersection supplied
by the proved C.2.7 large-component placement. In the remaining SL5(2)
model, the intrinsic radical filtration identifies its normalizer with
a proper partial-flag stabilizer. A factor five forces a single endpoint,
so this is a line or hyperplane parabolic.

C.2.7 places that normalizer inside the proper original star intersection.
Maximality of the endpoint parabolic makes the two groups equal. Thus the
literal star intersection contains a full component Sylow subgroup. This
is derived from its geometry and is not an ambient Sylow assumption.

`FiveEndpointStarSource` applies both conclusions to the original
nonsingular centralizer and degree-five closure assembly. The full point
action must still exclude this degree-five row; the degree-four fixed-space
argument, ordinary J4 exclusion and retained fusion/closure obligations
remain with qt-d-double-natural-centralizers and its existing producers.
Source: Aschbacher--Smith 12.1.1, printed pp.788--789, and C.2.7,
pp.145--147. Imported intrinsic model results retain their attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective

private theorem five_radical_normalizer_endpoint (U : Subgroup (LinearGroup 5))
    (hU : U.IsPRadical 2) (h5 : 5 ∣ Nat.card (normalizer (U : Set (LinearGroup 5)))) :
    ∃ (b : FiveBasis) (i : Fin 4), (i = 0 ∨ i = 3) ∧
      normalizer (U : Set (LinearGroup 5)) = flagStabilizer b {i} := by
  let ρ : Representation (ZMod 2) (LinearGroup 5) (Space 5) := {
    toFun g := g.toLinearMap
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hρ : Function.Injective ρ := by
    intro x y he
    exact LinearEquiv.ext (fun v => LinearMap.congr_fun he v)
  obtain ⟨k,W,hk,_,hm,hp,he⟩ := Representation.BinaryRadical.exists_partialFlag_normalizer ρ hρ U hU
  have he' : normalizer (U : Set (LinearGroup 5)) = ⨅ i, parabolic (W i) := he
  rw [he'] at h5 ⊢
  exact GeometricFlags.exists_endpoint_coordinates hk W hm.monotone
    (fun i => (hp i).1) (fun i => (hp i).2) h5
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource ChapterC.C27Source Chapter1
open RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual degree-five star intersection is an endpoint parabolic. -/
theorem doubleNatural_five_adapted_C27_endpoint
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, B.pointResidual w ≤ K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        ∀ e : starImage K Q K ≃* LinearGroup 5,
        ∃ (b : FiveBasis) (i : Fin 4), (i = 0 ∨ i = 3) ∧
          ((starM K Q (B.localPointCentralizer w)).subgroupOf (starImage K Q K)).map
            e.toMonoidHom = flagStabilizer b {i} := by
  let := D.doubledOrbit_elementary h
  intro S w hw Q K hRK hi e
  let R := B.pointResidual w
  let C := starImage K Q K
  let A := starImage K Q R
  let U := (starImage K Q Q).subgroupOf C
  let P := (starM K Q (B.localPointCentralizer w)).subgroupOf C
  have hcard : Nat.card (LinearGroup 5) = 9999360 := by
    rw [← Nat.card_congr (matrixEquivLinear 5).toEquiv,Matrix.card_GL_field]
    decide
  obtain ⟨hU,hNP⟩ := star_intersection_placement_from_source_of_large_order hi
    (by rw [Nat.card_congr e.toEquiv,hcard]; decide)
  have hAC : A ≤ C := map_mono (comap_mono hRK)
  have hRQ : R ≤ normalizer (Q : Set G) :=
    ((B.pointResidual_le w).trans inf_le_left).trans
      (le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _
          (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)))))
  have hn : A.subgroupOf C ≤ normalizer (U : Set C) := by
    intro x hx
    have hxQ : (x : StarQuotient K Q) ∈ normalizer (starImage K Q Q : Set _) := by
      obtain ⟨r,hr,he⟩ := hx
      change (QuotientGroup.mk' (starKernel K Q)) r = (x : StarQuotient K Q) at he
      rw [←he]
      apply (Q.subgroupOf (K ⊔ Q)).le_normalizer_map (QuotientGroup.mk' (starKernel K Q))
      apply mem_map_of_mem
      rw [←subgroupOf_normalizer_eq (show Q ≤ K ⊔ Q from le_sup_right)]
      exact hRQ hr
    exact fun z => hxQ z
  have h5A : 5 ∣ Nat.card A := by
    obtain ⟨_,⟨a⟩⟩ := D.doubleNatural_adapted_C27_residual_marking h B S w hw K hRK hi
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 A))
    rw [Nat.card_congr (a.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8).toEquiv,
      nat_card_alternatingGroup,Nat.card_fin]
    norm_num [Nat.factorial]
  have h5 : 5 ∣ Nat.card (normalizer (U.map e.toMonoidHom : Set (LinearGroup 5))) := by
    rw [←map_equiv_normalizer_eq U e,card_map_of_injective e.injective]
    apply dvd_trans _ (card_dvd_of_le hn)
    rwa [Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv]
  obtain ⟨b,i,hiend,he⟩ := Nonsingular.five_radical_normalizer_endpoint
    (U.map e.toMonoidHom) (hU.map_equiv e) h5
  have hnmap : normalizer (U.map e.toMonoidHom : Set (LinearGroup 5)) ≤ P.map e.toMonoidHom := by
    rw [←map_equiv_normalizer_eq U e]
    exact map_mono hNP
  have hPn : P.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    exact starM_subgroupOf_ne_top hi
      (map_injective e.injective (ht.trans (map_top_of_surjective _ e.surjective).symm))
  refine ⟨b,i,hiend,?_⟩
  have hle : flagStabilizer b {i} ≤ P.map e.toMonoidHom := he ▸ hnmap
  by_contra hne
  exact hPn ((MaximalOvergroups.singleton_flag_isCoatom b i).2 _
    (lt_of_le_of_ne hle (Ne.symm hne)))


/-- In degree five, parabolic geometry supplies a Sylow in the literal star intersection. -/
theorem doubleNatural_five_adapted_C27_star_sylow
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, B.pointResidual w ≤ K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        ∃ P : Sylow 2 (starImage K Q K), (P : Subgroup (starImage K Q K)) ≤
          (starM K Q (B.localPointCentralizer w)).subgroupOf (starImage K Q K) := by
  let := D.doubledOrbit_elementary h
  intro S w hw Q K hRK hi
  obtain ⟨e₀⟩ := D.doubleNatural_five_adapted_C27_star_linearFive h B S w hw K hRK hi
  let e := e₀.trans (slEquivLinear 5)
  obtain ⟨b,i,_,he⟩ := D.doubleNatural_five_adapted_C27_endpoint h B S w hw K hRK hi e
  let P := MaximalOvergroups.flagSylow b
  have hP : (P : Subgroup (LinearGroup 5)) ≤
      ((starM K Q (B.localPointCentralizer w)).subgroupOf (starImage K Q K)).map
        e.toMonoidHom := by
    rw [he,MaximalOvergroups.flagSylow_coe]
    exact flagStabilizer_antitone b (Set.subset_univ _)
  refine ⟨P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective,?_⟩
  change (P : Subgroup (LinearGroup 5)).map e.symm.toMonoidHom ≤ _
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨y,hy,he⟩ := hP hx
  change e y = x at he
  change e.symm x ∈ (starM K Q (B.localPointCentralizer w)).subgroupOf (starImage K Q K)
  rw [←he,e.symm_apply_apply]
  exact hy


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
