module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearWholeModuleAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.LinearReciprocal
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.OriginalProductModule
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearWholeModule
public import Theory.Representation.PSL3Two.FanoNonFF
public import Theory.Representation.BinaryConjugationCoordinates.ReciprocalNonFF

/-!
# Reciprocal conjugates of the original linear omega module: structure at the original group

The linear alternative of the original H₂,L₂T pair has one of the three
actual six-dimensional modules: natural plus dual, point core or line core.
Each model is non-FF. The component fills the quotient by O₂(H₀), and its
module-action kernel is precisely its two-core. It therefore supplements
the full module centralizer with the same quotient kernel, transferring
the non-FF property to the actual H₀ action on V₀=⟨Ω₁Z(T)^H₀⟩.

If V₀ᵍ≤H₀ and V₀≤H₀ᵍ, reciprocal noncentral action would give strict
centralizer-index inequalities in both directions. Hence [V₀,V₀ᵍ]=1.
The final theorem constructs the original pair for both the recognized
linear-three and ordinary A₆ centralizers, and applies this result under
the literal reciprocal containments in R₂=O₂(L₂T). Thus the linear case
of 13.4.16 is complete, including all three module alternatives.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/LinearReciprocal` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The actual linear omega module has a non-FF full action image. Its
reciprocal conjugates commute, using the original component supplement
and quotient kernel rather than an assumed full-actor module marking. -/
theorem original_linear_pair_module_nonFF_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (hlin : Solvable.LinearAmalgamConclusion T (A ⊔ B)) :
    let X := A ⊔ B
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    ∃ he : IsElementaryAbelian 2 U, let := he
      ¬ IsFFModule (imageRepresentation (elementaryRepresentation (p := 2)
        (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy
          (omegaOneCenterAmbient (T : Subgroup G)) X))))) ∧
      Nat.card U = 64 ∧ ∀ g : G,
        U.conjBy g ≤ X → U ≤ X.conjBy g → ⁅U,U.conjBy g⁆ = ⊥ := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  obtain ⟨C,hC,_,_,_,_,⟨eC⟩⟩ := hlin.1
  let K := C.subgroupOf X
  have hmap : K.map X.subtype = C := map_subgroupOf_eq_of_le hC.1
  have eK : ((K.map X.subtype) ⧸ pCore 2 (K.map X.subtype)) ≃* Matrix.PSL3Two.PSL :=
    hmap.symm ▸ eC
  obtain ⟨heU,e,hA,hB,hS,hm,hcard⟩ := Amalgam.original_pair_linear_whole_module_at
    h₀ h structural D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres
      h1332 K hC.2 eK
  let := heU
  let C' := K.map X.subtype
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C'))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hCU : C' ≤ normalizer (U : Set G) :=
    (map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X)
  have hker : f.ker = (centralizer (U : Set G)).subgroupOf C' := by
    change (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C'))).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    apply map_injective C'.subtype_injective
    rw [subgroupOf_map_subtype,inf_comm]
    exact (Amalgam.original_pair_component_action_kernel h₀ D m h1332 hTA hTB eA eB
      hne hindexA hindexB hres K hC.2).symm
  have hgen : C' ⊔ (X ⊓ centralizer (U : Set G)) = X := by
    apply le_antisymm (sup_le (map_subtype_le K) inf_le_left)
    have hg := (Amalgam.original_pair_linear_core_supplement h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hC.2 eK).2
    apply hg.symm.le.trans
    apply sup_le_sup_left
    exact le_inf (pCoreIn_le 2 X)
      ((Amalgam.original_pair_action_kernel h₀ D m hTA hTB eA eB hne
        hindexA hindexB).2.1.symm.le.trans inf_le_right)
  let ρ := elementaryRepresentation (p := 2)
    (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy Z X)))
  have hn : ¬ IsFFModule (imageRepresentation ρ) := by
    have step {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
        (σ : Representation (ZMod 2) BinaryLinearThree.Group M)
        (E : Representation.Equiv (σ.comp f) (elementaryRepresentation (p := 2)
          (U.normalizerMonoidHom.comp (inclusion hCU))))
        (hs : ¬ IsFFModule σ) : ¬ IsFFModule (imageRepresentation ρ) :=
      BinaryConjugationCoordinates.nonFF_of_supplement_model X U C'
        (le_normalizer_conjugateSpanBy Z X) (map_subtype_le K) hgen f hf hker σ E hs
    rcases hm with hm | hm | hm
    · obtain ⟨em⟩ := hm
      exact step _ em BinaryLinearThree.FanoNonFF.sum_not_ff
    · obtain ⟨em⟩ := hm
      exact step _ em BinaryLinearThree.FanoNonFF.point_not_ff
    · obtain ⟨em⟩ := hm
      exact step _ em BinaryLinearThree.FanoNonFF.line_not_ff
  refine ⟨heU,hn,hcard,fun g h₁ h₂ => ?_⟩
  exact BinaryConjugationCoordinates.reciprocal_conjugate_of_nonFF_image X U
    (le_normalizer_conjugateSpanBy Z X) hn g h₁ h₂

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
