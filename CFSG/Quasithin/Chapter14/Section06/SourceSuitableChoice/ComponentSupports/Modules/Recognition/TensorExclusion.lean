module
public import Theory.Representation.BinaryTensorThree.FactorInertia
public import Theory.Representation.BinaryTensorThree.NormalizerNonFF
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.LinearThreeMovement
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.Exchanged

/-!
# Tensor exclusions on the original terminal module

An invariant tensor factor would make every component-normalizer automorphism
inner. The original Sylow normalizer supplies an outer automorphism, excluding
that marking on any invariant subquotient. This is the tensor exclusion needed
for F.9.18(5ii) in the14.6.22 argument.

Two disjoint tensor sections also contradict the actual placed quadratic
actor's codimension bound. Normality of the full component orbit is proved in
the original quotient. Its centralizer intersection gives faithfulness of the
same actor on both marked sections, so each costs strictly more than its rank.
The terminal application constructs the original U/Z and the original placed
actor and applies both exclusions, retaining the literal quotient maps.

The constituent argument producing split supports, or the two stable tensor
markings excluded here, remains open. In particular these results do not prove
whole-normalizer invariance of the selected joined natural/dual seed support.
That step, the normal-component branches and the same-vector suitable assembly
remain with qt-e-suitable-component-supports. Original14.6.18 remains hsolv,
with final discharge owned by qt-e-14625-source.
Source: Aschbacher--Smith D.3.5--9, F.9.18(2--5),14.6.22,
printed pp.195--200,325--326,1038.
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


/-- The original diagram automorphism excludes an invariant tensor factor.
The marking concerns the literal component image in H/O₂(H). -/
theorem source_no_invariant_tensor_factor
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) V)
    (eK : actorImage H K ≃* BinaryTensorThree.Factor)
    (b : Representation.Equiv (σ.comp (actorImage H K).subtype)
      (BinaryTensorThree.rightRepresentation.comp eK.toMonoidHom)) : False := by
  let c : Matrix.PSL3Two.SL ≃* BinaryTensorThree.Factor :=
    Matrix.PSL3Two.equivGL.trans
      ((Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := ZMod 2)).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) BinaryTensorThree.Natural))
  obtain ⟨s,hs⟩ := source_l3_component_outer_image
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK (eK.trans c.symm)
  let q := QuotientGroup.mk' (pCore 2 H)
  let sh : H := ⟨s,hH.1.2 s.property.1⟩
  have hn : q sh ∈ actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H)) := by
    rw [←source_component_normalizer_image T H hH K hKH hK]
    exact ⟨sh,s.property,rfl⟩
  obtain ⟨k,hk⟩ := BinaryTensorThree.normalizer_inner_of_right_tensor σ
    (actorImage H K) eK b ⟨q sh,hn.2⟩
  exact hs ⟨k,fun x => congrArg Subtype.val (MulEquiv.congr_fun hk x)⟩

/-- Two disjoint tensor sections cannot fit the original quadratic actor's
budget. Their intermediate actor contains the full original component orbit. -/
theorem source_no_two_disjoint_tensor_sections
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (A : Subgroup (H ⧸ pCore 2 H)) (hA : QuadraticMember a.representation A)
    (hfaith : A ⊓ centralizer (actorImage H (conjugateSpanBy K (T : Subgroup G)) :
      Set (H ⧸ pCore 2 H)) = ⊥)
    (J : Subgroup (H ⧸ pCore 2 H)) (hAJ : A ≤ J)
    (hNJ : actorImage H (conjugateSpanBy K (T : Subgroup G)) ≤ J)
    (U W : Subrepresentation (a.representation.comp J.subtype))
    (hd : Disjoint U.toSubmodule W.toSubmodule)
    (eU eW : (actorImage H (conjugateSpanBy K (T : Subgroup G))).subgroupOf J ≃*
      BinaryTensorThree.Factor × BinaryTensorThree.Factor)
    (bU : Representation.Equiv
      (U.toRepresentation.comp ((actorImage H (conjugateSpanBy K (T : Subgroup G))).subgroupOf J).subtype)
      (BinaryTensorThree.baseRepresentation.comp eU.toMonoidHom))
    (bW : Representation.Equiv
      (W.toRepresentation.comp ((actorImage H (conjugateSpanBy K (T : Subgroup G))).subgroupOf J).subtype)
      (BinaryTensorThree.baseRepresentation.comp eW.toMonoidHom)) : False := by
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H))) := Module.Finite.of_finite
  let N := actorImage H (conjugateSpanBy K (T : Subgroup G))
  let : N.Normal := by
    have hn := source_quotient_componentOrbit_normal
      hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
    rwa [quotient_componentOrbit H K T hKH hH.1.2] at hn
  exact (not_lt_of_ge hA.2.2)
    (BinaryTensorThree.twice_rank_lt_fixedCodim_of_restricted_marked_tensors
      a.representation N A hA.1 hfaith J hAJ hNJ U W hd eU eW bU bW)

/-- The original terminal U/Z and its placed quadratic actor exclude both
an invariant tensor subquotient and two disjoint marked tensor subspaces
preserved by an intermediate actor. No elementary subgroup is lifted. -/
theorem terminal_nonnormal_tensor_exclusions
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc),
      let _ := hU
      ∃ (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
        (B : Subgroup Mc),
        B ≤ (((sourceResidual M Mc ⊔ (T : Subgroup G)) ⊓ Mc).pCoreIn 2).subgroupOf Mc ∧
        QuadraticMember a.representation (B.map (QuotientGroup.mk' (pCore 2 Mc))) ∧
        (∀ (U : Subrepresentation a.representation) (L : Subrepresentation U.toRepresentation)
          (eK : actorImage Mc K ≃* BinaryTensorThree.Factor),
          ¬ Nonempty (Representation.Equiv
            (L.quotientRepresentation.comp (actorImage Mc K).subtype)
            (BinaryTensorThree.rightRepresentation.comp eK.toMonoidHom))) ∧
        ∀ (J : Subgroup (Mc ⧸ pCore 2 Mc)),
          B.map (QuotientGroup.mk' (pCore 2 Mc)) ≤ J →
          actorImage Mc (conjugateSpanBy K (T : Subgroup G)) ≤ J →
          ∀ (U W : Subrepresentation (a.representation.comp J.subtype)),
            Disjoint U.toSubmodule W.toSubmodule →
            ∀ (eU eW : (actorImage Mc (conjugateSpanBy K (T : Subgroup G))).subgroupOf J ≃*
              BinaryTensorThree.Factor × BinaryTensorThree.Factor),
              ¬ (Nonempty (Representation.Equiv
                (U.toRepresentation.comp
                  ((actorImage Mc (conjugateSpanBy K (T : Subgroup G))).subgroupOf J).subtype)
                (BinaryTensorThree.baseRepresentation.comp eU.toMonoidHom)) ∧
                Nonempty (Representation.Equiv
                (W.toRepresentation.comp
                  ((actorImage Mc (conjugateSpanBy K (T : Subgroup G))).subgroupOf J).subtype)
                (BinaryTensorThree.baseRepresentation.comp eW.toMonoidHom))) := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  obtain ⟨hU,a,B,I,hB,_,_,hA,hfaith,_⟩ := terminal_nonnormal_component_span_inputs
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  let := hU
  refine ⟨hU,a,B,hB,hA,?_,?_⟩
  · rintro U L eK ⟨b⟩
    exact source_no_invariant_tensor_factor hG T hempty hM hunique hmany hcard e hab hsolv
      Mc hout K hKM hK L.quotientRepresentation eK b
  · rintro J hAJ hNJ U W hd eU eW ⟨⟨bU⟩,⟨bW⟩⟩
    exact source_no_two_disjoint_tensor_sections hG T hempty hM hunique hmany hcard e hab hsolv
      Mc hout K hKM hK a (B.map (QuotientGroup.mk' (pCore 2 Mc))) hA hfaith
      J hAJ hNJ U W hd eU eW bU bW

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
