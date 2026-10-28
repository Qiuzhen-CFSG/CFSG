module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.FactorKernel
public import CFSG.Quasithin.Chapter10.SourceThompsonNormalization
public import CFSG.Quasithin.ChapterE.Section03.Parameters.SectionNormalizer
public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.SL2NaturalOffenders.NaturalNormalizer

/-!
# The Thompson action on the original natural A₅ cover

Every maximum elementary subgroup of T normalizes the component and its
moved module W. Restricting to the common normalizer preserves maximality.
The maximum-order inequality gives an offender on W and hence on its
faithful natural quotient. Natural-normalizer offender recognition places
that action in the original SL₂ layer. Thus J(T) acts on W through L,
retaining the entire central covering kernel and the original subgroup maps.
No equality between the local and full modules is required.
Source: Aschbacher–Smith 10.1.2(2), B.4.2(1), and 10.2.9, pp.741,86,751.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

omit [Finite G] in
private theorem maxFamily_subgroupOf (A T N : Subgroup G)
    (hA : A ∈ elementaryAbelianMaxSubgroups T) (hAN : A ≤ N) :
    A.subgroupOf N ∈ elementaryAbelianMaxSubgroups (T.subgroupOf N) := by
  let := hA.2.1
  refine ⟨fun x hx => hA.1 hx, IsElementaryAbelian.subgroupOf hAN, ?_⟩
  intro B hB he
  have hBT : B.map N.subtype ≤ T := by
    rintro _ ⟨b,hb,rfl⟩
    exact hB hb
  have hh := hA.2.2 (B.map N.subtype) hBT (he.map N.subtype)
  rw [card_map_of_injective N.subtype_injective] at hh
  exact hh.trans_eq (Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv).symm

variable (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
local instance pointSylowNaturalActorElementary :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance pointSylowNaturalActorAlgebra :
    Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

/-- The original Thompson subgroup acts on the natural central cover through L. -/
theorem source_a5_natural_thompson_le_linear_actor
    (f : alternatingGroup (Fin 5) ≃* SL(2,Representation.OrthogonalFourMinus.FiniteModel.Field 1))
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ L ⊔ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let M := D.maximalLocal ⊓ normalizer (L : Set G)
  let N := M ⊓ normalizer (W : Set G)
  let Q := inducedAutomizer W M
  let q := localNormalizerAction W M
  let σ := SL2.BinarySmall.natural (K := Representation.OrthogonalFourMinus.FiniteModel.Field 1)
  let π := f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
  have hπ : Function.Surjective π := f.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hLM : L ≤ M := le_inf ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) L.le_normalizer
  have hNL : N ≤ normalizer (L : Set G) := inf_le_left.trans inf_le_right
  have hNZ := (le_inf hNL (show N ≤ normalizer (W : Set G) from inf_le_right)).trans
    (source_original_moved_fixed_normalizer D)
  have hk : commutatorPreimage N W (sourceMovedFixed D) ≤ centralizer (W : Set G) := by
    have hh : commutatorPreimage N W (sourceMovedFixed D) ≤
        commutatorPreimage (normalizer (L : Set G) ⊓ normalizer (W : Set G)) W (sourceMovedFixed D) :=
      le_commutatorPreimage ((commutatorPreimage_le _ _ _).trans (le_inf hNL inf_le_right))
        (commutator_commutatorPreimage_le _ _ _ hNZ)
    rw [source_a5_original_moved_normalizer_quotient_kernel D e] at hh
    exact hh.trans inf_le_right
  obtain ⟨τ,ι,hι,hιτ,hact⟩ := exists_local_section_normalizer L W (sourceMovedFixed D) M
    σ π hπ c hLM hNL hNZ hk
  have hWN : W ≤ N := le_inf (c.section_le.trans hLM) W.le_normalizer
  have hLN : L ≤ N := le_inf hLM c.normalized
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) := sSup_le fun _ hA => hA.1
  have hJN : elementaryAbelianMaxJ (T : Subgroup G) ≤ N := by
    refine le_inf (le_inf (hJT.trans (le_normalizer_componentOrbit L T))
      D.thompson_normalizes_component) ?_
    intro j hj
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule
        (le_normalizer_componentOrbit L T (hJT hj))),
      mem_normalizer_iff_map_conj_eq.mp (D.thompson_normalizes_component hj)]
  have hWJ : W ≤ (T : Subgroup G) := by
    have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) D.simpleQTKE T D.maximal
    exact (le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)).trans (D.fullModule_le_sylow hu)
  let U := W.subgroupOf N
  let : U.Normal := normal_subgroupOf_of_le_normalizer (show N ≤ normalizer (W : Set G) from inf_le_right)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hWN
  have hq : Function.Surjective q := localNormalizerAction_surjective W M
  have hker : q.ker = centralizer (U : Set N) := by
    ext n
    rw [MonoidHom.mem_ker,localNormalizerAction_eq_one_iff]
    constructor
    · intro hn u hu
      exact Subtype.ext (hn u hu)
    · intro hn w hw
      exact congrArg N.subtype (hn ⟨w,hWN hw⟩ hw)
  let ρ := NormalElementaryQuotient.representation U q hq hker
  let r : Additive U →ₗ[ZMod 2] (Fin 2 → Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
    (c.coordinates.toAdditiveLeft.comp
      (subgroupOfEquivOfLe hWN).toMonoidHom.toAdditive).toZModLinearMap 2
  have hr : Function.Surjective r := c.onto.comp (subgroupOfEquivOfLe hWN).surjective
  have heq : ∀ a w, r (ρ a w) = τ a (r w) := by
    intro a w
    obtain ⟨n,rfl⟩ := hq a
    change (c.coordinates ((subgroupOfEquivOfLe hWN) (ρ (q n) w).toMul)).toAdd =
      τ (q n) (c.coordinates ((subgroupOfEquivOfLe hWN) w.toMul)).toAdd
    rw [hact]
    apply congrArg (fun x : W => (c.coordinates x).toAdd)
    apply Subtype.ext
    exact congrArg N.subtype (NormalElementaryQuotient.representation_apply U q hq hker n w)
  have hmark (l : L) : τ (q (inclusion hLN l)) = σ (π l) := by
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := c.onto (Multiplicative.ofAdd v)
    exact (hact (inclusion hLN l) w).trans (c.equivariant l w)
  apply sSup_le
  intro A hA a ha
  have hAN : A ≤ N := (le_sSup hA).trans hJN
  let A' := A.subgroupOf N
  let aN : N := ⟨a,hAN ha⟩
  have hA' : A' ∈ elementaryAbelianMaxSubgroups ((T : Subgroup G).subgroupOf N) :=
    maxFamily_subgroupOf A T N hA hAN
  have hlinear : ∃ g : SL(2,Representation.OrthogonalFourMinus.FiniteModel.Field 1), τ (q aN) = σ g := by
    by_cases hzero : A' ≤ q.ker
    · refine ⟨1,?_⟩
      rw [show q aN = 1 from hzero ha,map_one,map_one]
    · have hAρ := NormalElementaryQuotient.maxElementary_isOffender U q hq hker
        ((T : Subgroup G).subgroupOf N) A' (fun _ hw => hWJ hw) hA' hzero
      have hAτ : IsOffender τ (A'.map q) := ⟨hAρ.1,
        (fixedCodim_le_of_equivariant_surjection ρ τ r hr heq _).trans hAρ.2⟩
      have hAi := hAτ.map_equivariant τ (normalizerRepresentation σ) ι hι
        (LinearEquiv.refl _ _) (fun x v => (hιτ x v).symm)
      have hF : 2 < Nat.card (Representation.OrthogonalFourMinus.FiniteModel.Field 1) := by
        rw [GaloisField.card 2 2 (by decide)]; decide
      have hle := SL2NaturalOffenders.natural_normalizer_offender_le_layer hF _ hAi
      obtain ⟨g,hg⟩ := hle (mem_map_of_mem ι (mem_map_of_mem q (show aN ∈ A' from ha)))
      refine ⟨g,?_⟩
      have hh := congrArg (fun x : (Module.End (ZMod 2) (Fin 2 → Representation.OrthogonalFourMinus.FiniteModel.Field 1))ˣ => x.val) hg
      exact (LinearMap.ext (fun v => (hιτ (q aN) v).symm)).trans hh.symm
  obtain ⟨g,hg⟩ := hlinear
  obtain ⟨l,hl⟩ := hπ g
  have he : q aN = q (inclusion hLN l) := by
    apply hι
    apply Subtype.ext
    apply Units.ext
    calc
      (ι (q aN)).val.val = τ (q aN) := LinearMap.ext (fun v => hιτ (q aN) v)
      _ = σ g := hg
      _ = σ (π l) := (congrArg σ hl).symm
      _ = τ (q (inclusion hLN l)) := (hmark l).symm
      _ = (ι (q (inclusion hLN l))).val.val := LinearMap.ext (fun v => (hιτ _ v).symm)
  have hc : (a : G) * (l : G)⁻¹ ∈ centralizer (W : Set G) := by
    apply (localNormalizerAction_eq_one_iff W M (aN * (inclusion hLN l)⁻¹)).mp
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hm := (L ⊔ centralizer (W : Set G)).mul_mem ((show centralizer (W : Set G) ≤ L ⊔ centralizer (W : Set G) from le_sup_right) hc)
      ((show L ≤ L ⊔ centralizer (W : Set G) from le_sup_left) l.property)
  simpa only [inv_mul_cancel_right] using hm
end CFSG.Quasithin.Chapter10
