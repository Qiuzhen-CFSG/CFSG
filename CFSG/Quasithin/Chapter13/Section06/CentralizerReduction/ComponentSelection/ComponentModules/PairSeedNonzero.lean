module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.JoinCoverage
public import Theory.Representation.SL2NaturalOffenders.NaturalPair
/-!
The marked seed has nonzero natural coordinates. A zero coordinate defines a kernel subgroup invariant under the actual orbit actor. Since the seed generates W_K under that actor and L_v has plus image in the pair, surjectivity rules out either zero coordinate.

Source: Aschbacher--Smith 13.6.14, printed pp.929--930.
-/
public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
variable {G : Type*} [Group G]

theorem seed_projection_ne_zero_source
    (K L T : Subgroup G) (z v : G)
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hLv : plusImage K L T z v hL hz (Lv L v) ≤
      plusImage K L T z v hL hz (Kminus K T v))
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Nontrivial U]
    (σ : Representation (ZMod 2) (plusImage K L T z v hL hz (Kminus K T v)) U)
    (f : Additive (WK K L T z v) →ₗ[ZMod 2] U) (hf : Function.Surjective f)
    (he : ∀ (g : plusImage K L T z v hL hz (Kminus K T v)) w,
      f (wkRepresentation K L T z v hL hz g w) = σ g (f w))
    (hzW : z ∈ WK K L T z v) : f (Additive.ofMul ⟨z,hzW⟩) ≠ 0 := by
  intro hzero
  let W := WK K L T z v
  let A := plusActor K L T v
  let C := plusImage K L T z v hL hz (Kminus K T v)
  let N := f.ker.toAddSubgroup.toSubgroup'.map W.subtype
  have hzN : z ∈ N := mem_map.mpr ⟨⟨z,hzW⟩,hzero,rfl⟩
  have hN : Kminus K T v ⊔ Lv L v ≤ normalizer (N : Set G) := by
    apply le_normalizer_iff.mpr
    intro a ha x hx
    obtain ⟨w,hw,rfl⟩ := hx
    let aA : A := ⟨a,(show Kminus K T v ⊔ Lv L v ≤ A from le_sup_left) ha⟩
    have haC : plusMk K L T z v hL hz aA ∈ C := by
      have hm : plusImage K L T z v hL hz (Kminus K T v ⊔ Lv L v) ≤ C := by
        rw [plusImage,subgroupOf_sup
          (show Kminus K T v ≤ A from le_sup_left.trans le_sup_left)
          (show Lv L v ≤ A from le_sup_right.trans le_sup_left),Subgroup.map_sup]
        exact sup_le le_rfl hLv
      exact hm (mem_map.mpr ⟨aA,ha,rfl⟩)
    let c : C := ⟨plusMk K L T z v hL hz aA,haC⟩
    let w' := wkRepresentation K L T z v hL hz (c : Gplus K L T z v hL hz)
      (Additive.ofMul w)
    refine mem_map.mpr ⟨w'.toMul,?_,?_⟩
    · change f w' = 0
      change f (wkRepresentation K L T z v hL hz c (Additive.ofMul w)) = 0
      rw [he,show f (Additive.ofMul w) = 0 from hw,map_zero]
    · exact wkRepresentation_apply K L T z v hL hz aA (Additive.ofMul w)
  have hWN : W ≤ N := conjugateSpanBy_le (zpowers_le.mpr hzN) hN
  have hfzero : ∀ w, f w = 0 := by
    intro w
    obtain ⟨a,ha,heq⟩ := hWN w.toMul.property
    have haw : a = w.toMul := Subtype.ext heq
    change f (Additive.ofMul a) = 0 at ha
    simpa only [haw, ofMul_toMul] using ha
  obtain ⟨u,hu⟩ := exists_ne (0 : U)
  obtain ⟨w,rfl⟩ := hf u
  exact hu (hfzero w)

theorem pair_seed_projections_ne_zero_source
    (K L T : Subgroup G) (z v : G)
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hLv : plusImage K L T z v hL hz (Lv L v) ≤
      plusImage K L T z v hL hz (Kminus K T v))
    (F : Type*) [Field F] [Finite F] [Algebra (ZMod 2) F]
    (e : plusImage K L T z v hL hz (Kminus K T v) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F)
    (f : Additive (WK K L T z v) →ₗ[ZMod 2] ((Fin 2 → F) × (Fin 2 → F)))
    (hf : Function.Surjective f)
    (he : ∀ (g : plusImage K L T z v hL hz (Kminus K T v)) w,
      f (wkRepresentation K L T z v hL hz g w) =
        SL2NaturalOffenders.naturalPair (F := F) (e g) (f w))
    (hzW : z ∈ WK K L T z v) :
    (f (Additive.ofMul ⟨z,hzW⟩)).1 ≠ 0 ∧
      (f (Additive.ofMul ⟨z,hzW⟩)).2 ≠ 0 := by
  let W := Fin 2 → F
  let D := Matrix.SpecialLinearGroup (Fin 2) F
  constructor
  · apply seed_projection_ne_zero_source K L T z v hL hz hLv
      ((SL2NaturalOffenders.NoStrong.natural (F := F)).comp
        ((MonoidHom.fst D D).comp e.toMonoidHom))
      ((LinearMap.fst (ZMod 2) W W).comp f)
      (by
        intro w
        obtain ⟨x,hx⟩ := hf (w,0)
        exact ⟨x,congrArg Prod.fst hx⟩) _ hzW
    exact fun g w => congrArg Prod.fst (he g w)
  · apply seed_projection_ne_zero_source K L T z v hL hz hLv
      ((SL2NaturalOffenders.NoStrong.natural (F := F)).comp
        ((MonoidHom.snd D D).comp e.toMonoidHom))
      ((LinearMap.snd (ZMod 2) W W).comp f)
      (by
        intro w
        obtain ⟨x,hx⟩ := hf (0,w)
        exact ⟨x,congrArg Prod.snd hx⟩) _ hzW
    exact fun g w => congrArg Prod.snd (he g w)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
