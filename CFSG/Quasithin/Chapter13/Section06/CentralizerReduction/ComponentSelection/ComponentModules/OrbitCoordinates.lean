module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.JoinKernel
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.ConjugatePairInternalLift

/-!
# Multiplication coordinates on the actual plus-component pair

The plus map on K T_v has two-group kernel. The solvable-kernel
C-component correspondence therefore keeps the two moving components
distinct. Their plus images are ordinary components and hence commute.
The intrinsic simple quotient makes the first image centerless, so the
images are disjoint. Multiplication gives product coordinates on the
literal image of K₋, with both original factor inclusions retained.

These are group coordinates for the cubic-diagonal and paired natural
module steps of 13.6.14. No representation decomposition is asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.14, printed p.929, using the component correspondence A.3.3.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- The original plus map commutes with conjugation by elements of its actor. -/
theorem plusImage_conjBy_source (K L T D : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hD : D ≤ plusActor K L T v) (a : plusActor K L T v) :
    plusImage K L T z v hL hz (D.conjBy (a : G)) =
      (plusImage K L T z v hL hz D).conjBy (plusMk K L T z v hL hz a) := by
  have hDa : D.conjBy (a : G) ≤ plusActor K L T v := by
    rintro x ⟨d, hd, rfl⟩
    exact (plusActor K L T v).mul_mem
      ((plusActor K L T v).mul_mem a.property (hD hd))
      ((plusActor K L T v).inv_mem a.property)
  have he : (D.conjBy (a : G)).subgroupOf (plusActor K L T v) =
      (D.subgroupOf (plusActor K L T v)).conjBy a := by
    apply map_injective (plusActor K L T v).subtype_injective
    rw [map_subgroupOf_eq_of_le hDa, map_conjBy_hom,
      map_subgroupOf_eq_of_le hD]
    rfl
  rw [plusImage, he, map_conjBy_hom]
  rfl

private theorem ccomponent_eq_of_map_eq {H Q : Type*} [Group H] [Finite H] [Group Q]
    {B C : Subgroup H} (hB : B.IsCComponent) (hC : C.IsCComponent)
    (f : H →* Q) [Group.IsSolvable f.ker] (he : B.map f = C.map f) : B = C := by
  have hs : B ⊔ f.ker = C ⊔ f.ker := by
    simpa only [comap_map_eq] using congrArg (Subgroup.comap f) he
  rw [← hB.solvableResidual_sup_eq f.ker (by rw [normalizer_eq_top]; exact le_top),
    ← hC.solvableResidual_sup_eq f.ker (by rw [normalizer_eq_top]; exact le_top), hs]

omit [Finite G] in
private theorem joinPlusMap_subgroup (K L T D : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hD : D ≤ K ⊔ Tv T v) :
    (D.subgroupOf (K ⊔ Tv T v)).map (joinPlusMap K L T z v hL hz) =
      plusImage K L T z v hL hz D := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨inclusion (sup_le (K_le_plusActor K L T v) le_sup_right) a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, hD ha⟩, ha, rfl⟩

/-- A moving T_v-element still exchanges distinct components after taking
the actual plus quotient. -/
theorem plusImage_pair_ne_source (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G))
    (t : G) (ht : t ∈ Tv T v) (htN : t ∉ normalizer (K : Set G)) :
    plusImage K L T z v hL hz K ≠ plusImage K L T z v hL hz (K.conjBy t) := by
  let H := K ⊔ Tv T v
  let tH : H := ⟨t, (show Tv T v ≤ H from le_sup_right) ht⟩
  let B := K.subgroupOf H
  have hB : B.IsCComponent := hK.1.2.1
  have hBK : B.map H.subtype = K := map_subgroupOf_eq_of_le le_sup_left
  have hC : (B.conjBy tH).IsCComponent := hB.map_equiv (MulAut.conj tH)
  have hCK : (B.conjBy tH).map H.subtype = K.conjBy t := by
    rw [map_conjBy_hom, hBK]
    rfl
  have hCt : K.conjBy t ≤ H := by
    rw [← hCK]
    exact map_subtype_le _
  have hCB : (K.conjBy t).subgroupOf H = B.conjBy tH := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hCt, hCK]
  let f := joinPlusMap K L T z v hL hz
  let : Group.IsNilpotent f.ker :=
    (joinPlusMap_ker_isTwoGroup_source K L T z v hlocal hL hz hK hn).isNilpotent
  intro he
  have hm : B.map f = (B.conjBy tH).map f := by
    change (K.subgroupOf H).map f = _
    rw [← hCB, joinPlusMap_subgroup K L T K z v hL hz le_sup_left,
      joinPlusMap_subgroup K L T (K.conjBy t) z v hL hz hCt]
    exact he
  have hBC := ccomponent_eq_of_map_eq hB hC f hm
  exact htN (mem_normalizer_iff_map_conj_eq.mpr
    (hCK.symm.trans (hBC ▸ hBK)))

/-- Multiplication identifies the two original plus images with the
literal K₋ image, retaining both subgroup embeddings. -/
theorem exists_plus_pair_coordinates_source (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G)) :
    ∃ t ∈ Tv T v, t ∉ normalizer (K : Set G) ∧
      Kminus K T v = K ⊔ K.conjBy t ∧
      Disjoint (plusImage K L T z v hL hz K)
        (plusImage K L T z v hL hz (K.conjBy t)) ∧
      ∃ e : (plusImage K L T z v hL hz K ×
        plusImage K L T z v hL hz (K.conjBy t)) ≃*
          plusImage K L T z v hL hz (Kminus K T v),
        ∀ a b, (e (a,b) : Gplus K L T z v hL hz) =
          (a : Gplus K L T z v hL hz) * (b : Gplus K L T z v hL hz) := by
  obtain ⟨_, _, t, ht, htN, hp⟩ :=
    noninvariant_component_pair_source K L T z v hlocal hK hn
  let A := plusImage K L T z v hL hz K
  let B := plusImage K L T z v hL hz (K.conjBy t)
  let tA : plusActor K L T v := ⟨t, (show Tv T v ≤ plusActor K L T v from le_sup_right) ht⟩
  have hAB : B = A.conjBy (plusMk K L T z v hL hz tA) :=
    plusImage_conjBy_source K L T K z v hL hz (K_le_plusActor K L T v) tA
  have hA : IsComponent (Gplus K L T z v hL hz) A :=
    ⟨plusImage_K_subnormal K L T z v hL hz hK,
      plusImage_K_quasisimple_source K L T z v hL hz hK hSylow⟩
  have hB : IsComponent (Gplus K L T z v hL hz) B :=
    hAB.symm ▸ hA.map_conj (plusMk K L T z v hL hz tA)
  have hne : A ≠ B := plusImage_pair_ne_source K L T z v hlocal hL hz hK hn t ht htN
  have hc : ⁅A,B⁆ = ⊥ := hA.commutator_eq_bot_of_ne hB hne
  let : IsSimpleGroup (K ⧸ pCore 2 K) :=
    noninvariant_component_core_simple_source K L T z v hlocal hK hn
  let : IsSimpleGroup A :=
    (componentCoreEquivPlus K L T z v hlocal hL hz hSylow hK hn).symm.isSimpleGroup
  let := hA.2
  have hZ : center A = ⊥ := by
    rcases (inferInstance : (center A).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp h)).elim
  have hd : Disjoint A B := by
    apply Subgroup.disjoint_def.mpr
    intro x hxA hxB
    have hx : (⟨x,hxA⟩ : A) ∈ center A := by
      apply mem_center_iff.mpr
      intro a
      exact Subtype.ext (((commutator_eq_bot_iff_le_centralizer.mp hc a.property) x hxB).symm)
    have hx1 : (⟨x,hxA⟩ : A) = 1 := by simpa only [hZ, mem_bot] using hx
    exact congrArg (fun a : A => (a : Gplus K L T z v hL hz)) hx1
  have hKt : K.conjBy t ≤ plusActor K L T v :=
    (le_sup_right.trans hp.ge).trans
      (show Kminus K T v ≤ plusActor K L T v from le_sup_left.trans le_sup_left)
  have heq : A ⊔ B = plusImage K L T z v hL hz (Kminus K T v) := by
    rw [hp, plusImage, subgroupOf_sup (K_le_plusActor K L T v) hKt, Subgroup.map_sup]
    rfl
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd
    (commutator_eq_bot_iff_le_centralizer.mp hc)
  exact ⟨t,ht,htN,hp,hd,e.trans (MulEquiv.subgroupCongr heq),he⟩

open A5Module ComponentReduction InitialSieve
variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- The product coordinates on the original marked source configuration. -/
theorem exists_plus_pair_coordinates_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : ¬ Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G)) :
    let v := markedV d.flag.module
    let z := markedZ d.flag.module
    ∃ t ∈ Tv (T : Subgroup G) v, t ∉ normalizer (K : Set G) ∧
      Kminus K (T : Subgroup G) v = K ⊔ K.conjBy t ∧
      Disjoint (plusImage K L (T : Subgroup G) z v hL hz K)
        (plusImage K L (T : Subgroup G) z v hL hz (K.conjBy t)) ∧
      ∃ e : (plusImage K L (T : Subgroup G) z v hL hz K ×
        plusImage K L (T : Subgroup G) z v hL hz (K.conjBy t)) ≃*
          plusImage K L (T : Subgroup G) z v hL hz (Kminus K (T : Subgroup G) v),
        ∀ a b, (e (a,b) : Gplus K L (T : Subgroup G) z v hL hz) =
          (a : Gplus K L (T : Subgroup G) z v hL hz) *
            (b : Gplus K L (T : Subgroup G) z v hL hz) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  exact exists_plus_pair_coordinates_source K L (T : Subgroup G) _ _
    (hG.involution_centralizer_sqtk (marked_orders d.flag.module).2) hL hz
    ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩ hK hn

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
