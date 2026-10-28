module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.FixedSections
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.MovingTensor

/-!
# Whole-module fixed spaces for a moving quadratic actor

The source geometry identifies the product Borel with a Sylow normalizer.
The genuine four-group theorem makes every nontrivial irreducible section a
natural tensor with zero Borel fixed space. Odd-index trace and induction on
submodule dimension extend this calculation through nonsplit extensions.

Source: Aschbacher–Smith D.3.7, pp.197–199, and 15.3.65, p.1152.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
open RepresentationReduction.SourceRestrictions.Cases.Exchanged
open Representation.QuadraticFourGroup RepresentationReduction
variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) {K K₀ T B C A : Subgroup D}

/-- The component overlap determines the Borel on the whole exchanged product. -/
theorem borel_sylow_normalizer_of_geometry (geo : ExchangedGeometry K K₀ T B C)
    (hTK : T ≤ normalizer (K₀ : Set D))
    (hC : ∃ P : Sylow 2 K, normalizer (P : Set K) = C.subgroupOf K) :
    ∃ P : Sylow 2 K₀, normalizer (P : Set K₀) = B.subgroupOf K₀ := by
  obtain ⟨t,ht,hout⟩ := geo.moved
  obtain ⟨hs,hd,hc,hr,hb⟩ := geo.pair t ht hout
  obtain ⟨p⟩ := productMarking_of_disjoint (hTK ht) hs hd hc hr
  exact p.borel_normalizer geo.overlap_le hb hC

/-- The genuine four-group theorem controls every actual irreducible section;
odd-index extension then controls the entire original module. -/
theorem fixedSpace_le_of_fourGroup {F : Subgroup D} {a : D}
    (h : Hypotheses ρ K F a) (he : componentOrbit K F = K₀)
    (hB : ∃ P : Sylow 2 K₀, normalizer (P : Set K₀) = B.subgroupOf K₀) :
    fixedSpace ρ B ≤ fixedSpace ρ K₀ := by
  have hindex : Odd (B.subgroupOf K₀).index := by
    obtain ⟨P,hP⟩ := hB
    exact odd_index_of_sylow_le P _ (hP ▸ (P : Subgroup K₀).le_normalizer)
  have hmain := fixedSpace_le_of_irreducible_sections (ρ.comp K₀.subtype)
    (B.subgroupOf K₀) hindex (by
      intro W _ _ _ σ hs
      by_cases ht : σ.IsTrivial
      · let := ht
        intro w _ g
        exact σ.isTrivial_apply g w
      · rw [irreducibleSection_fixedSpace_eq_bot_of_fourGroup ρ h he σ hs ht hB]
        exact bot_le)
  intro v hv g
  have hv' : v ∈ fixedSpace (ρ.comp K₀.subtype) (B.subgroupOf K₀) := by
    intro b
    exact hv ⟨b.val,b.property⟩
  exact hmain hv' ⟨g,mem_top g⟩

/-- The original small quadratic actor moving the component supplies the full
fixed-space calculation, including all nonsplit extensions. -/
theorem moving_module_fixedSpace_le
    (geo : ExchangedGeometry K K₀ T B C)
    (hTK : T ≤ normalizer (K₀ : Set D))
    (hρ : Function.Injective ρ) (hK : IsComponent D K) [IsSimpleGroup K]
    [IsElementaryAbelian 2 A] (hAT : A ≤ T)
    (hq : IsQuadratic ρ A) (hc : A ⊓ centralizer (K₀ : Set D) = ⊥)
    (hm : ¬A ≤ normalizer (K : Set D)) (hd : fixedCodim ρ A ≤ 2 * rank A)
    (hC : ∃ P : Sylow 2 K, normalizer (P : Set K) = C.subgroupOf K) :
    fixedSpace ρ B ≤ fixedSpace ρ K₀ := by
  obtain ⟨F,a,hF,he⟩ := moving_fourGroup_of_small_ratio ρ geo hTK hρ hK hAT hq hc hm hd
  exact fixedSpace_le_of_fourGroup ρ hF he (borel_sylow_normalizer_of_geometry geo hTK hC)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
