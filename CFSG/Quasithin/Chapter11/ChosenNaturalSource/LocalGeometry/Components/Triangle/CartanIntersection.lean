module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.CommonNormal
public import Theory.SpecificGroups.PSL3.CartanActions.FullTorusFixer
public import Theory.GroupTheory.PResidual.NormalizedSupplement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Statements
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstKernel
public import Theory.GroupTheory.QuotientIntersection
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.ProjectiveIndices

/-!
# The actual Cartan intersection in the field-four triangle

In PSL₃(4), the Borel lies in both parabolic residuals: every diagonal
entry is a cube root of unity and can be removed by a scalar. An odd
subgroup normalizing the Sylow intersection with either canonical residual
therefore lies in both residual lifts. The original two-kernel normalizes
these lifts, so the containment lifts through that same quotient map.

For the actual KX/O₂(KX) ≃ PGL₃(4), the PSL₃(4) component has index three.
The Cartan has order nine, hence X ∩ K has order three. The original Cartan
normalizes T ∩ L₁, giving the source equalities X ∩ K = X ∩ L₁ = X ∩ K₀.
The common-normal component theorem now uses this cubic directly, without
an additional Cartan-intersection witness.

If C_V(L) is nontrivial, it supplies a common normal subgroup directly:
it lies in the full first flag term, is centralized by K₀ and L₂, and is
T-invariant. This constructs I = ⟨K₀,L₂⟩ as a relatively normal component
of IT, with L(G,T), He and residual identities. The faithful fixed-layer
branch still needs the F.1.12 amalgam contradiction. Recognition of I,
SL₃(4) exclusion, maximality, faithfulness and both orientations remain
with qt-d-1222-natural-relative-components. The preceding flag/Cartan
inputs retain qt-d-1222-natural-flag-cartan as producer and
qt-d-1222-natural-local-geometry as final discharge owner.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.762--763, especially the displayed Cartan intersection
and the common-normal construction preceding it. No completion of the
full source theorem is asserted.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open CFSG.Quasithin.ChapterA.Section03
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section
variable {F : Type*} [Field F] [Finite F]

private theorem borel_le_rootLocal (hF : Nat.card F = 4) (b : Bool) :
    borel F ≤ rootLocal F b := by
  cases b
  · rw [rootLocal_false]
    intro g hg
    obtain ⟨⟨a,b⟩,u,hu,he⟩ := BorelQuotient.borel_factorization F g hg
    have hb : b^3 = 1 := by
      simpa [Nat.card_units,hF] using pow_card_eq_one' (x := b)
    have ht : torusMap F (a,b) = torusMap F (a*b⁻¹,1) := by
      apply (ResidualParameters.projective_parameters_eq_iff _ _).mpr
      constructor
      · simp
      · simpa using hb
    rw [he,ht]
    apply (lineLocal F).mul_mem (unipotent_le_lineLocal F hu)
    apply mem_map_of_mem (projection F)
    rw [mem_lineLocalSL_iff,torusSL_val]
    simp
  · rw [rootLocal_true]
    exact FullTorusFixer.borel_le_pointLocal_of_card_four hF

variable {A : Type*} [Group A] [Finite A]

private theorem odd_le_of_map_le_rootLift (hF : Nat.card F = 4)
    (r : A →* PSL(3,F)) (hr : Function.Surjective r) (hk : IsPGroup 2 r.ker)
    (U : Subgroup A) (ho : Odd (Nat.card U)) (b : Bool)
    (hU : U.map r ≤ rootLocal F b) : U ≤ rootLift r b := by
  have hpU : IsPPerfect 2 U := by
    intro N hn htwo
    let := hn
    apply index_eq_one.mp
    change Nat.card (U ⧸ N) = 1
    exact htwo.card_eq_or_dvd.resolve_right
      (fun hd => ho.not_two_dvd_nat (hd.trans N.card_quotient_dvd_card))
  apply le_of_isPPerfect_of_le_sup_of_normalizes U (rootLift r b) r.ker hpU hk
  · exact ker_normalizes_rootLift r b
  · have hh : U ≤ ((rootLift r b).map r).comap r := by
      rw [rootLift_map hF r hr]
      exact map_le_iff_le_comap.mp hU
    simpa only [comap_map_eq] using hh

/-- Odd elements normalizing the Sylow intersection with either residual
belong to both canonical residual lifts. -/
theorem odd_le_rootLift_of_normalizes_intersection [CharP F 2]
    (hF : Nat.card F = 4) (r : A →* PSL(3,F)) (hr : Function.Surjective r)
    (hk : IsPGroup 2 r.ker) (P U : Subgroup A)
    (hP : P.map r = unipotent F) (hkP : r.ker ≤ P)
    (ho : Odd (Nat.card U)) (b d : Bool)
    (hn : U ≤ normalizer ((P ⊓ rootLift r b : Subgroup A) : Set A)) :
    U ≤ rootLift r d := by
  have hi : (P ⊓ rootLift r b).map r = unipotent F := by
    rw [inf_comm P, map_inf_of_ker_le r (rootLift r b) P hkP,hP,rootLift_map hF r hr]
    exact inf_eq_right.mpr (unipotent_le_rootLocal F b)
  apply odd_le_of_map_le_rootLift hF r hr hk U ho d
  have hh := (map_mono (f := r) hn).trans (le_normalizer_map r)
  rw [hi,normalizer_unipotent F (by decide : 0 < 2) (by simpa using hF)] at hh
  exact hh.trans (borel_le_rootLocal hF d)

variable {G : Type*} [Group G] [Finite G]

/-- In a PSL₃(4) cover an odd subgroup normalizing the Sylow intersection
with one proper local component lies in every proper local component. -/
theorem odd_intersection_le_local (T : Sylow 2 G) {K B C U : Subgroup G}
    (hK : (⊤ : Subgroup K).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hB : B ∈ localCComponents (T : Subgroup G)) (hBK : B < K)
    (hC : C ∈ localCComponents (T : Subgroup G)) (hCK : C < K)
    (hUK : U ≤ K) (ho : Odd (Nat.card U))
    (hn : U ≤ normalizer (((T : Subgroup G) ⊓ B : Subgroup G) : Set G))
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) : U ≤ C := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
    (show Nat.card F = 2^2 by simpa using hF)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) (P.mapSurjective hq)
    (unipotentSylow F (by decide : 0 < 2) (by simpa using hF))
  let a := MulAut.conj g
  let r := a.toMonoidHom.comp q
  have hr : Function.Surjective r := a.surjective.comp hq
  have hrker : r.ker = pCore 2 K := by
    ext x
    change a (e (QuotientGroup.mk' (pCore 2 K) x)) = 1 ↔ _
    rw [a.map_eq_one_iff,e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let : Group.IsNilpotent r.ker := by rw [hrker]; exact pCore_isNilpotent
  have hrP : (P : Subgroup K).map r = unipotent F := by
    rw [←map_map]
    exact congrArg Sylow.toSubgroup hg
  have hkP : r.ker ≤ (P : Subgroup K) := by
    rw [hrker]
    exact pCore_isPGroup.le_sylow_of_normal P
  have hBP : B.subgroupOf K ∈ localCComponents (P : Subgroup K) :=
    hP.symm ▸ SourceEmbeddings.local_restrict hB hBK.le
  have hCP : C.subgroupOf K ∈ localCComponents (P : Subgroup K) :=
    hP.symm ▸ SourceEmbeddings.local_restrict hC hCK.le
  obtain ⟨b,hb⟩ := local_eq_rootLift hF r hr P hrP hkP hK hBP
    (fun he => hBK.not_ge (subgroupOf_eq_top.mp he))
  obtain ⟨d,hd⟩ := local_eq_rootLift hF r hr P hrP hkP hK hCP
    (fun he => hCK.not_ge (subgroupOf_eq_top.mp he))
  have hU : U.subgroupOf K ≤ rootLift r d := by
    apply odd_le_rootLift_of_normalizes_intersection hF r hr
      (by rw [hrker]; exact pCore_isPGroup) P (U.subgroupOf K) hrP hkP
      (by rwa [Nat.card_congr (subgroupOfEquivOfLe hUK).toEquiv]) b d
    rw [←hb,hP]
    change U.subgroupOf K ≤ normalizer (((T : Subgroup G) ⊓ B).comap K.subtype : Set K)
    exact (comap_mono hn).trans (le_normalizer_comap K.subtype)
  have hh := map_mono (f := K.subtype) (hd ▸ hU)
  simpa only [map_subgroupOf_eq_of_le hUK,map_subgroupOf_eq_of_le hCK.le] using hh

/-- The original order-nine Cartan meets the PSL₃(4) component in a cubic;
the quotient comparison retains the entire KX and its intrinsic two-core. -/
theorem card_inf_component_of_projective (K X : Subgroup G) [K.Normal]
    (hK : K.IsCComponent) (hX : Nat.card X = 9) (hgen : K ⊔ X = ⊤)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour (G ⧸ pCore 2 G)) : Nat.card (X ⊓ K : Subgroup G) = 3 := by
  have hX3 : IsPGroup 3 X := IsPGroup.of_card (n := 2) (by simpa using hX)
  have hq3 := isPGroup_quotient_of_sup_eq_top K X hX3 hgen
  have hcore : pCore 2 G ≤ K := by
    let q := QuotientGroup.mk' K
    have h2 : IsPGroup 2 ((pCore 2 G).map q) := pCore_isPGroup.map q
    have h3 : IsPGroup 3 ((pCore 2 G).map q) := hq3.to_subgroup _
    have hz : (pCore 2 G).map q = ⊥ :=
      disjoint_self.mp (h2.disjoint_of_coprime h3 (by decide : Nat.Coprime 2 3))
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  have hB : ClassicalGroup.IsPSL B 3 4 := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact ⟨F,inferInstance,inferInstance,hF,⟨(cComponentTwoCoreQuotientEquiv hK).symm.trans e⟩⟩
  have hc : Nat.card (G ⧸ pCore 2 G) = 3 * Nat.card B :=
    OddPrime.SourceModels.card_pgl_sign_eq_three_mul_psl_sign false 4 hB hp
      (by norm_num [OddPrime.SourceModels.SignedCongruence])
  have hi : B.index = 3 := by
    have hh := B.card_mul_index
    rw [hc] at hh
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hh.trans (Nat.mul_comm _ _))
  have hiK : K.index = 3 := by
    rw [← K.index_map_eq (QuotientGroup.mk'_surjective (pCore 2 G))
      (by simpa only [QuotientGroup.ker_mk'] using hcore)]
    exact hi
  have hiX : (K.subgroupOf X).index = 3 := by
    change K.relIndex X = 3
    rw [←relIndex_sup_left, hgen,relIndex_top_right,hiK]
  have hci : Nat.card (K.subgroupOf X) = 3 := by
    have hh := (K.subgroupOf X).card_mul_index
    rw [hiX,hX] at hh
    omega
  rw [Nat.card_congr ((K.subgroupOf X).equivMapOfInjective X.subtype
    X.subtype_injective).toEquiv,subgroupOf_map_subtype] at hci
  simpa only [inf_comm] using hci

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle

open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
public noncomputable section
open Closure
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The Cartan cubic in the exceptional configuration belongs to both
original residuals, with no chosen intersection witness. -/
theorem first_triangle_cartan_intersections
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G))) :
    Nat.card (X ⊓ K : Subgroup G) = 3 ∧ X ⊓ K = X ⊓ f.Li 0 ∧ X ⊓ K = X ⊓ K₀ := by
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (f.invariant 0).trans ((normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2)
  have hXN : X ≤ normalizer (f.Li 0 : Set G) := by
    have hx : X ≤ L ⊓ normalizer (f.Vi 0 : Set G) :=
      le_inf (hX.1.trans inf_le_left) (f.cartan_normalizes hu hX 0)
    exact (hx.trans (L ⊓ normalizer (f.Vi 0 : Set G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have hXi : X ≤ normalizer (((T : Subgroup G) ⊓ f.Li 0 : Subgroup G) : Set G) := by
    have he : (T : Subgroup G) ⊓ f.Li 0 = ((T : Subgroup G) ⊓ L) ⊓ f.Li 0 := by
      apply le_antisymm
      · exact le_inf (le_inf inf_le_left (inf_le_right.trans ((localResidual_le _).trans inf_le_left))) inf_le_right
      · exact inf_le_inf inf_le_left le_rfl
    rw [he]
    exact (le_inf (hX.1.trans cartanNormalizer_normalizes_intersection) hXN).trans
      inf_normalizer_le_normalizer_inf
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.1.2.subgroupOf_of_le le_rfl hK.1.1
  have ho : Odd (Nat.card (X ⊓ K : Subgroup G)) :=
    hX.odd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hUB := Triangle.odd_intersection_le_local T htop hTK
    (flag_mem_local_of_model D S f 0 hm).1 hLK
    (flag_mem_local_of_model D S f 0 hm).1 hLK
    inf_le_right ho (inf_le_left.trans hXi) hk
  have hUK := Triangle.odd_intersection_le_local T htop hTK
    (flag_mem_local_of_model D S f 0 hm).1 hLK hK₀.1 hK₀K
    inf_le_right ho (inf_le_left.trans hXi) hk
  refine ⟨?_,le_antisymm (le_inf inf_le_left hUB) (inf_le_inf_left X hLK.le),
    le_antisymm (le_inf inf_le_left hUK) (inf_le_inf_left X hK₀K.le)⟩
  let J := K ⊔ X
  let B := K.subgroupOf J
  let Y := X.subgroupOf J
  have hKJ : K ≤ J := le_sup_left
  have hXJ : X ≤ J := le_sup_right
  have hJH : J ≤ normalizer (f.Vi 0 : Set G) :=
    sup_le hK.1.1 (f.cartan_normalizes hu hX 0)
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (hJH.trans ((normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2))
  let k := subgroupOfEquivOfLe hKJ
  have hmB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 4 := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hk
    exact ⟨F,inferInstance,inferInstance,hF,
      ⟨(QuotientGroup.congr _ _ k (pCore_map_iso 2 k)).trans e⟩⟩
  have hc := Triangle.card_inf_component_of_projective B Y
    (hK.1.2.subgroupOf_of_le hKJ hJH)
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hXJ).toEquiv,c.cartan_card hX,hfour]; norm_num)
    (by rw [←subgroupOf_sup hKJ hXJ]; exact subgroupOf_self J) hmB hp
  have hle : X ⊓ K ≤ J := inf_le_left.trans hXJ
  change Nat.card ((X ⊓ K).subgroupOf J) = 3 at hc
  rwa [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at hc

/-- The source common-normal branch now uses the actual Cartan intersection
X ∩ K. Its nontriviality and both residual containments are discharged from
the PSL₃/PGL₃ models; only common-normal existence remains in this step. -/
theorem triangle_join_component_of_common_normal_projective
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    Source.NormalComponentIn ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)) (K₀ ⊔ f.Li 1) ∧
      (K₀ ⊔ f.Li 1) ∈ Chapter1.L G T ∧ (K₀ ⊔ f.Li 1) ∈ Chapter1.He G ∧
      (solvableResidual ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G) : Subgroup G)).map
        ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)).subtype = K₀ ⊔ f.Li 1 ∧
      (pResidual 2 ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G) : Subgroup G)).map
        ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)).subtype = K₀ ⊔ f.Li 1 := by
  obtain ⟨hc,hB,hC⟩ := first_triangle_cartan_intersections D S f hu hm₁ hfour
    hX hK hLK hK₀ hK₀K hk hp
  have hn : (X ⊓ K : Subgroup G) ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hc
    contradiction
  exact triangle_join_component_of_common_normal D S f hu hm₂ hfix hX hK₀ hTK₀
    hn inf_le_left (hB.le.trans inf_le_right) (hC.le.trans inf_le_right) hcard hmove
    hQ hQT hTQ hKQ hLQ

/-- A nontrivial retained fixed layer supplies the source common normal
subgroup directly. Only the faithful-layer branch needs the amalgam argument. -/
theorem triangle_join_component_of_nontrivial_fixed_layer
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    Source.NormalComponentIn ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)) (K₀ ⊔ f.Li 1) ∧
      (K₀ ⊔ f.Li 1) ∈ Chapter1.L G T ∧ (K₀ ⊔ f.Li 1) ∈ Chapter1.He G ∧
      (solvableResidual ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G) : Subgroup G)).map
        ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)).subtype = K₀ ⊔ f.Li 1 ∧
      (pResidual 2 ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G) : Subgroup G)).map
        ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)).subtype = K₀ ⊔ f.Li 1 := by
  let Q := V ⊓ centralizer (L : Set G)
  have hQVi : Q ≤ f.Vi 0 := f.centralizer_le_Vi 0
  have hQe : Q = f.Vi 0 ⊓ centralizer (L : Set G) := by
    apply le_antisymm (le_inf hQVi inf_le_right)
    exact inf_le_inf_right _ (D.centralQuotientPreimage_le _)
  have hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G) := by
    rw [hQe]
    exact (le_inf (f.invariant 0)
      (D.sylow_normalizes_component.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  have hKfix : K ≤ centralizer (f.Vi 0 : Set G) :=
    subspace_containing_component_centralizes D S f (f.Vi 0) le_rfl hm₁ hfix hK.1 hLK.le
  have hLQ : f.Li 1 ≤ centralizer (Q : Set G) :=
    le_centralizer_iff.mp (inf_le_right.trans (centralizer_le
      ((localResidual_le _).trans inf_le_left)))
  exact triangle_join_component_of_common_normal_projective D S f hu hm₁ hm₂ hfour
    hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove hfixed
    (inf_le_left.trans D.le_sylow) hTQ
    ((hK₀K.le.trans (hKfix.trans (centralizer_le hQVi))).trans (Subgroup.centralizer_le_normalizer _))
    (hLQ.trans (Subgroup.centralizer_le_normalizer _))

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
