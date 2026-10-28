module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.PreservingComponent
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.PreservingActor
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.SourceClifford
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.MovingModule
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Normal.Filtration

/-!
# The preserving actor on the original exchanged module

On each irreducible factor of the whole acting group, Clifford theory makes
the component restriction semisimple. A conjugate of a locally minimum
quadratic subactor acts noncentrally on the marked component. The genuine
restriction-image bound recognizes every nontrivial simple component type,
so its Sylow normalizer fixes only component-fixed vectors. Conjugation
by an exchanger gives the other component, and their product gives the
residual fixed-space inclusion.

The odd-index trace extends this inclusion through all invariant submodules
and quotients, preserving the original quadratic actor and its codimension
bound throughout. This proves the Borel calculation needed in 15.3.65
without a full tensor or multiplicity classification.

Source: Aschbacher–Smith, D.3.6–D.3.7, pp.196–199; F.9.18, pp.325–326;
and the original seed contradiction in 15.3.65, p.1152.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
open RepresentationReduction RepresentationReduction.SourceRestrictions.Cases.Exchanged
open RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio
universe u
variable {D V : Type u} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [Finite V] (ρ : Representation (ZMod 2) D V) {K K₀ T B C A : Subgroup D}

theorem preserving_module_fixedSpace_le
    (geo : ExchangedGeometry K K₀ T B C)
    (hTK : T ≤ normalizer (K₀ : Set D)) (hgen : K₀ ⊔ T = ⊤)
    (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (_hρ : Function.Injective ρ) (hK : IsComponent D K) [IsSimpleGroup K]
    (hAT : A ≤ T) (hA : IsElementaryTwo A)
    (hq : IsQuadratic ρ A) (hAC : A ⊓ centralizer (K₀ : Set D) = ⊥)
    (hp : A ≤ normalizer (K : Set D)) (hd : fixedCodim ρ A ≤ 2 * rank A)
    {f : ℕ} (hm : SourceModel (K ⧸ center K) f) (hf : 1 < f) (ho : Odd f)
    (hC : ∃ P : Sylow 2 K, normalizer (P : Set K) = C.subgroupOf K) :
    fixedSpace ρ B ≤ fixedSpace ρ K₀ := by
  let : IsQuasisimple K := hK.2
  let : K₀.Normal := normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le K₀.le_normalizer hTK))
  have hZ : center K = ⊥ :=
    (inferInstance : (center K).Normal).eq_bot_or_eq_top.resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp h))
  have hBK : B ≤ K₀ := by
    obtain ⟨t,ht,hout⟩ := geo.moved
    obtain ⟨hpair,_,_,_,hB⟩ := geo.pair t ht hout
    rw [hB,←hpair]
    exact sup_le_sup geo.overlap_le (Subgroup.map_mono geo.overlap_le)
  have hBorel := borel_sylow_normalizer_of_geometry geo hTK hC
  have hindex : Odd (B.subgroupOf K₀).index := by
    obtain ⟨P,hP⟩ := hBorel
    exact odd_index_of_sylow_le P _ (hP ▸ (P : Subgroup K₀).le_normalizer)
  have hmain := Normal.fixedSpace_le_by_quadratic_irreducibles K₀ A (B.subgroupOf K₀)
    hindex (by
      intro W _ _ _ σ hi hqσ hdσ
      let : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
      let : IsSemisimpleRepresentation (σ.comp K.subtype) :=
        (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
          (component_restriction_semisimple σ geo hi)
      obtain ⟨J,hJN,hnJ,hJ,hqJ⟩ := exists_minimal_actor_on_component σ geo hAT hA hqσ hdσ hAC hp
      have hcomponent := component_fixedSpace_le_of_minimal_actor σ K J hZ hs
        hJN hnJ hJ hqJ hm hf ho (C.subgroupOf K) hC
      have hcomponent' : fixedSpace σ C ≤ fixedSpace σ K := by
        intro v hv k
        have hv' : v ∈ fixedSpace (σ.comp K.subtype) (C.subgroupOf K) := by
          intro c
          exact hv ⟨c.val,c.property⟩
        exact hcomponent hv' ⟨k,mem_top k⟩
      have hwhole := fixedSpace_le_residual_of_component σ geo hcomponent'
      intro v hv k
      have hv' : v ∈ fixedSpace σ B := by
        intro b
        exact hv ⟨⟨b,hBK b.property⟩,b.property⟩
      exact hwhole hv' k.val) ρ hq hd
  intro v hv k
  have hv' : v ∈ fixedSpace (ρ.comp K₀.subtype) (B.subgroupOf K₀) := by
    intro b
    exact hv ⟨b.val,b.property⟩
  exact hmain hv' ⟨k,mem_top k⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
