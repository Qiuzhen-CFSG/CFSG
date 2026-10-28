module
public import Theory.Representation.BinaryTensorThree.ComponentRestriction
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.TensorExclusion

/-!
# Excluding all tensor constituents of the original terminal module

The original placed actor has trivial centralizer intersection with the full
normal component orbit and fixed codimension at most twice its rank. These
properties force every marked tensor constituent to be invariant under the
whole actor quotient. Restricting its tensor marking to the actual component
then contradicts the source Sylow normalizer's diagram automorphism.

Fixed codimension decreases on literal subquotients. The terminal application
therefore excludes tensor constituents on every subquotient of the original
U/Z using that same placed actor. It assumes neither invariance nor a chosen
coordinate factor for the original component, and retains the central kernel.

The remaining constituent argument must prove that every constituent moved by
both components has such a tensor marking. After that exclusion, single-factor
support and the Irr⁺ orbit argument must still prove whole-normalizer invariance
of the selected natural--dual support. Normal-component branches and the original
same-vector suitable construction remain with qt-e-suitable-component-supports.
Original14.6.18 remains hsolv, owned by qt-e-14625-source.
Source: Aschbacher--Smith D.3.7--9, F.9.18(2--5),14.6.22,
printed pp.197--200,325--326,1038.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Chapter13.Section08.CriticalGeometry.Reorientation
open Chapter13.Section08.Components.SourceModels
universe u v
variable {G : Type u} [Group G] [Finite G]
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


/-- Any tensor constituent in a representation of the original actor quotient
with the source budget is invariant under that whole quotient. -/
theorem source_tensor_constituent_invariant
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) V)
    (A : Subgroup (H ⧸ pCore 2 H)) (hA : IsElementaryTwo A)
    (hfaith : A ⊓ centralizer (actorImage H (conjugateSpanBy K (T : Subgroup G)) :
      Set (H ⧸ pCore 2 H)) = ⊥)
    (hbudget : fixedCodim σ A ≤ 2 * rank A)
    (U : Subrepresentation (σ.comp (actorImage H (conjugateSpanBy K (T : Subgroup G))).subtype))
    (eN : actorImage H (conjugateSpanBy K (T : Subgroup G)) ≃*
      BinaryTensorThree.Factor × BinaryTensorThree.Factor)
    (b : Representation.Equiv U.toRepresentation (BinaryTensorThree.baseRepresentation.comp eN.toMonoidHom)) :
    ∀ g : H ⧸ pCore 2 H, U.toSubmodule.map (σ g) = U.toSubmodule := by
  let N := actorImage H (conjugateSpanBy K (T : Subgroup G))
  let : N.Normal := by
    have hn := source_quotient_componentOrbit_normal
      hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
    rwa [quotient_componentOrbit H K T hKH hH.1.2] at hn
  exact BinaryTensorThree.marked_tensor_constituent_invariant σ N A hA hfaith hbudget U eN b

/-- Tensor constituents are excluded on the original quotient with no
ambient-invariance or coordinate-factor premise. The latter is derived from
actual componenthood in the marked square. -/
theorem source_no_tensor_constituent
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) V)
    (A : Subgroup (H ⧸ pCore 2 H)) (hA : IsElementaryTwo A)
    (hfaith : A ⊓ centralizer (actorImage H (conjugateSpanBy K (T : Subgroup G)) :
      Set (H ⧸ pCore 2 H)) = ⊥)
    (hbudget : fixedCodim σ A ≤ 2 * rank A)
    (U : Subrepresentation (σ.comp (actorImage H (conjugateSpanBy K (T : Subgroup G))).subtype))
    (eN : actorImage H (conjugateSpanBy K (T : Subgroup G)) ≃*
      BinaryTensorThree.Factor × BinaryTensorThree.Factor)
    (b : Representation.Equiv U.toRepresentation (BinaryTensorThree.baseRepresentation.comp eN.toMonoidHom)) :
    False := by
  let N := actorImage H (conjugateSpanBy K (T : Subgroup G))
  have hstable := source_tensor_constituent_invariant
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK σ A hA hfaith hbudget U eN b
  let U' : Subrepresentation σ := {
    toSubmodule := U.toSubmodule
    apply_mem_toSubmodule g v hv := by
      rw [←hstable g]
      exact ⟨v,hv,rfl⟩ }
  have hKN : actorImage H K ≤ N := by
    exact map_mono (comap_mono (le_conjugateSpanBy K (T : Subgroup G)))
  have hKq := source_quotient_component
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
  obtain ⟨eK,⟨bK⟩⟩ := BinaryTensorThree.exists_component_right_tensor_marking
    U'.toRepresentation N (actorImage H K) hKN (hKq.subgroupOf hKN) eN b
  exact source_no_invariant_tensor_factor
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK U'.toRepresentation eK bK

/-- On every literal subquotient of the terminal U/Z, its original placed
actor excludes all marked tensor constituents of the full component orbit. -/
theorem terminal_nonnormal_no_tensor_constituents
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc),
      let _ := hU
      ∃ (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
        (B : Subgroup Mc),
        B ≤ (((sourceResidual M Mc ⊔ (T : Subgroup G)) ⊓ Mc).pCoreIn 2).subgroupOf Mc ∧
        QuadraticMember a.representation (B.map (QuotientGroup.mk' (pCore 2 Mc))) ∧
        ∀ (S : Subrepresentation a.representation) (L : Subrepresentation S.toRepresentation)
          (U : Subrepresentation (L.quotientRepresentation.comp
            (actorImage Mc (conjugateSpanBy K (T : Subgroup G))).subtype))
          (eN : actorImage Mc (conjugateSpanBy K (T : Subgroup G)) ≃*
            BinaryTensorThree.Factor × BinaryTensorThree.Factor),
          ¬ Nonempty (Representation.Equiv U.toRepresentation
            (BinaryTensorThree.baseRepresentation.comp eN.toMonoidHom)) := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  obtain ⟨hU,a,B,I,hB,_,_,hA,hfaith,_⟩ := terminal_nonnormal_component_span_inputs
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  let := hU
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))) := Module.Finite.of_finite
  refine ⟨hU,a,B,hB,hA,?_⟩
  rintro S L U eN ⟨b⟩
  let A := B.map (QuotientGroup.mk' (pCore 2 Mc))
  have hd : fixedCodim L.quotientRepresentation A ≤ 2 * rank A := by
    have hS := fixedCodim_subrepresentation_le a.representation S A
    have hL := fixedCodim_quotient_add_subrepresentation_le S.toRepresentation L A
    have hh : fixedCodim a.representation A ≤ 2 * rank A := hA.2.2
    omega
  exact source_no_tensor_constituent
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK
    L.quotientRepresentation A hA.1 hfaith hd U eN b

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
