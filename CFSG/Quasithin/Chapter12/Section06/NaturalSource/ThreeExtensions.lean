module
public import Theory.Representation.BinaryPermutation.EightThreeExtensions
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.WeakClosureZero

/-!
# The three extensions for the original normalizer action

The intrinsic S8 calculation proves the A₂ clause of12.6.28. Pull back
its three subgroups through the actual normalizer permutation map and
then through the original actor inclusion. Each preimage retains the
action kernel, so all relative indices and strict fixed-space inclusions
are statements about the original group and the full original V.

Source: Aschbacher--Smith,12.6.28(2,4), printed pp.833--835.
-/
public section
open Subgroup BinaryPermutation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
/-- The intrinsic three-extension clause of source 12.6.28(2), on the
actual E.3.8 family. -/
theorem natural_fixedSpaceFamily_two_three_extensions
    (A : Subgroup (Equiv.Perm (Fin 8)))
    (hA : A ∈ ChapterE.fixedSpaceFamily (naturalRepresentation (Fin 8)) 2) :
    EightThreeExtensions.ThreeExtensions A := by
  let : IsElementaryAbelian 2 A := hA.2.1.2
  exact EightThreeExtensions.three_extensions_of_rigid A hA.2.1.1 hA.2.2

/-- The rank clause of source12.6.28(2) uses the same intrinsic actor. -/
theorem natural_fixedSpaceFamily_two_rank_lower
    (A : Subgroup (Equiv.Perm (Fin 8)))
    (hA : A ∈ ChapterE.fixedSpaceFamily (naturalRepresentation (Fin 8)) 2) :
    3 ≤ Representation.BinaryOffender.rank A :=
  (natural_fixedSpaceFamily_two_three_extensions A hA).rank_lower

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Pull back the actual three-extension configuration along the original
normalizer permutation action. The kernel is retained in D and all three
extensions, so all relative indices are literal indices in the original actor. -/
theorem SourceHypothesis.original_three_extensions
    (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (A : Subgroup G) (hAN : A ≤ normalizer (V : Set G)) [IsElementaryAbelian 2 A]
    (hnon : ¬ A ≤ centralizer (V : Set G))
    (hr : LocalAlternatives.CentralizerRigidity V A 2) :
    ∃ D₀ ≤ A, ChapterE.subgroupCorank A D₀ = 3 ∧
      ∃ E₀ : Fin 3 → Subgroup G, Function.Injective E₀ ∧
        ∀ i, D₀ ≤ E₀ i ∧ E₀ i ≤ A ∧ ChapterE.subgroupCorank (E₀ i) D₀ = 1 ∧
          V ⊓ centralizer (A : Set G) < V ⊓ centralizer (E₀ i : Set G) := by
  classical
  obtain ⟨f,_,hf⟩ := S.original_normalizer_permutation_action D hZ hTV
  let e := D.fullLinearCoordinates hZ
  let fA := f.comp (inclusion hAN)
  let B := fA.range
  let ρ := naturalRepresentation (Fin 8)
  have he (a : A) (v : Additive V) : e (seedRepresentation A V hAN a v) =
      ρ (fA a) (e v) := hf ⟨a.val,hAN a.property⟩ v.toMul
  let : IsElementaryAbelian 2 B :=
    IsElementaryAbelian.of_surjective fA.rangeRestrict fA.rangeRestrict_surjective
  let lift (C : Subgroup (Equiv.Perm (Fin 8))) : Subgroup G := (C.comap fA).map A.subtype
  have lift_le (C) : lift C ≤ A := by
    rintro _ ⟨a,ha,rfl⟩
    exact a.property
  have lift_mono {C F : Subgroup (Equiv.Perm (Fin 8))} (hCF : C ≤ F) : lift C ≤ lift F :=
    map_mono (comap_mono hCF)
  have lift_B : lift B = A := by
    apply le_antisymm (lift_le B)
    intro a ha
    exact mem_map.mpr ⟨⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩,rfl⟩
  have image (C) (hC : C ≤ B) : (C.comap fA).map fA = C := by
    rw [map_comap_eq,inf_eq_right.mpr hC]
  have lift_inj {C F : Subgroup (Equiv.Perm (Fin 8))} (hC : C ≤ B) (hF : F ≤ B)
      (h : lift C = lift F) : C = F := by
    have hh := Subgroup.map_injective A.subtype_injective h
    have hm := congrArg (fun U : Subgroup A => U.map fA) hh
    simpa only [image C hC,image F hF] using hm
  have index (C F) (hF : F ≤ B) : (lift C).relIndex (lift F) = C.relIndex F := by
    rw [relIndex_map_map_of_injective _ _ A.subtype_injective,relIndex_comap,image F hF]
  have fixed_iff (C : Subgroup (Equiv.Perm (Fin 8))) (hC : C ≤ B) (v : V) :
      (v : G) ∈ centralizer (lift C : Set G) ↔ e (Additive.ofMul v) ∈ fixedSpace ρ C := by
    constructor
    · intro hc c
      obtain ⟨a,ha⟩ := hC c.property
      have ham : a.val ∈ lift C := mem_map.mpr ⟨a,by
        change fA a ∈ C
        rw [ha]
        exact c.property,rfl⟩
      have hv : conjugation A V hAN a v = v := by
        apply Subtype.ext
        change a.val * v.val * a.val⁻¹ = v.val
        rw [hc a.val ham,mul_inv_cancel_right]
      change ρ c.val (e (Additive.ofMul v)) = e (Additive.ofMul v)
      rw [←ha,←he]
      exact congrArg e (congrArg Additive.ofMul hv)
    · intro hc a ha
      obtain ⟨b,hb,rfl⟩ := ha
      have hh := he b (Additive.ofMul v)
      have hfix : ρ (fA b) (e (Additive.ofMul v)) = e (Additive.ofMul v) := hc ⟨fA b,hb⟩
      rw [hfix] at hh
      have hh' := congrArg (fun w : Additive V => (w.toMul : G)) (e.injective hh)
      change b.val * v.val * b.val⁻¹ = v.val at hh'
      exact mul_inv_eq_iff_eq_mul.mp hh'
  have hne : B ≠ ⊥ := by
    intro hb
    apply hnon
    apply le_centralizer_iff.mp
    intro v hv
    have hh := (fixed_iff B le_rfl ⟨v,hv⟩).mpr (by
      rw [hb,fixedSpace_bot]
      trivial)
    simpa only [lift_B] using hh
  have hrigid (C : Subgroup (Equiv.Perm (Fin 8))) (hC : C ≤ B)
      (hcor : Nat.log 2 (C.relIndex B) < 2) : fixedSpace ρ B = fixedSpace ρ C := by
    have hidx : (lift C).relIndex A = C.relIndex B := by rw [←lift_B]; exact index C B le_rfl
    have hg := hr (lift C) (lift_le C) (by change Nat.log 2 _ < 2; rw [hidx]; exact hcor)
    ext w
    obtain ⟨v,rfl⟩ := e.surjective w
    change e (Additive.ofMul v.toMul) ∈ fixedSpace ρ B ↔
      e (Additive.ofMul v.toMul) ∈ fixedSpace ρ C
    rw [←fixed_iff B le_rfl v.toMul,←fixed_iff C hC v.toMul,lift_B]
    have hm := congrArg (fun U : Subgroup G => (v.toMul : G) ∈ U) hg
    simpa only [mem_inf,v.toMul.property,true_and] using (Iff.of_eq hm).symm
  obtain ⟨D₁,hD₁,hidx,E₁,hE₁,hEs⟩ := EightThreeExtensions.three_extensions_of_rigid B hne hrigid
  refine ⟨lift D₁,lift_le D₁,?_,fun i => lift (E₁ i),?_,?_⟩
  · change Nat.log 2 ((lift D₁).relIndex A) = 3
    rw [←lift_B,index D₁ B le_rfl,hidx]
    decide
  · intro i j hij
    exact hE₁ (lift_inj (hEs i).2.1 (hEs j).2.1 hij)
  · intro i
    obtain ⟨hDE,hEB,hED,hgrow⟩ := hEs i
    refine ⟨lift_mono hDE,lift_le _,?_,?_⟩
    · change Nat.log 2 ((lift D₁).relIndex (lift (E₁ i))) = 1
      rw [index D₁ (E₁ i) hEB,hED]
      decide
    · apply lt_of_le_of_ne
      · exact inf_le_inf_left V (Subgroup.centralizer_le (lift_le _))
      · intro hh
        apply ne_of_lt hgrow
        ext w
        obtain ⟨v,rfl⟩ := e.surjective w
        change e (Additive.ofMul v.toMul) ∈ fixedSpace ρ B ↔
          e (Additive.ofMul v.toMul) ∈ fixedSpace ρ (E₁ i)
        rw [←fixed_iff B le_rfl v.toMul,←fixed_iff (E₁ i) hEB v.toMul,lift_B]
        have hm := congrArg (fun U : Subgroup G => (v.toMul : G) ∈ U) hh
        simpa only [mem_inf,v.toMul.property,true_and] using Iff.of_eq hm
end CFSG.Quasithin.Chapter12.Section06
