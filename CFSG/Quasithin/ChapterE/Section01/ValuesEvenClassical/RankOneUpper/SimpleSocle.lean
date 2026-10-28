module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.Assembly
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure

/-!
# The whole-group component case for a simple generalized Fitting subgroup

Suppose F*(G) is nonabelian simple and G = F*(G)T for a Sylow two-subgroup T.
The lower-layer structure theorem proves that the radical and two-core vanish,
and identifies the layer, two-residual and solvable residual with F*(G).
For nontrivial A, faithfulness and the simple-component dichotomy give
[F*(G), A] = F*(G).

To check E.1.2(E2) literally, we transport the simple component to the intrinsic
carrier of the top subgroup and then to its radical quotient. The quotient
isomorphism is proved to equal the canonical quotient map. Normality makes the
local tau orbit a single component. The final corollary connects this to the
existing E-member constructor, leaving only the model's rank bound explicit.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.2(E2) and the simple-F*(G), G = LT hypotheses of E.1.14,
printed pp.210, 214 (combined manuscript, 1 March 2004).
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem eCaseComponent_of_simple_normal (T A K : Subgroup G)
    (L : Subgroup K) [L.Normal] [IsSimpleGroup L] [IsQuasisimple L]
    (hC : centralizer (L : Set K) = ⊥) (hq : IsPGroup 2 (K ⧸ L))
    (hne : A.subgroupOf K ≠ ⊥) : ECaseComponent T A K := by
  have hR := SimpleSocle.radical_eq_bot L hC
  let e : K ≃* (K ⧸ solvableRadical K) :=
    ((QuotientGroup.quotientMulEquivOfEq hR).trans QuotientGroup.quotientBot).symm
  have he : e.toMonoidHom = QuotientGroup.mk' (solvableRadical K) := by
    ext x
    rfl
  let C := L.map e.toMonoidHom
  let : C.Normal := (inferInstance : L.Normal).map _ e.surjective
  have hLC : IsComponent K L := ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩
  have hComp : IsComponent (K ⧸ solvableRadical K) C := hLC.map_equiv e
  let := hComp.2
  have hqC : IsPGroup 2 ((K ⧸ solvableRadical K) ⧸ C) :=
    hq.of_equiv (QuotientGroup.congr L C e rfl)
  have hstr := SimpleSocle.layer_residuals C hqC
  have hres := SimpleSocle.layer_residuals L hq
  have hclosed : IsTwoClosed (solvableRadical K) := by
    have : Subsingleton (solvableRadical K) := by
      rw [hR]
      infer_instance
    let S : Sylow 2 (solvableRadical K) := default
    refine ⟨S, ?_⟩
    have hS : (S : Subgroup (solvableRadical K)) = ⊥ := Subsingleton.elim _ _
    rw [hS]
    infer_instance
  refine ⟨hclosed, ?_, hres.2.1.trans hres.2.2.symm, C, hComp, ?_, Or.inl ?_⟩
  · change HasTwoGroupQuotient (componentLayer (K ⧸ solvableRadical K))
    rw [hstr.1]
    exact ⟨inferInstance, hqC⟩
  · rw [conjugateJoin_eq_of_normal, hstr.1]
  · have hc := congrArg (Subgroup.map e.toMonoidHom)
      (SimpleSocle.commutator_eq L hC (A.subgroupOf K) hne)
    simpa only [C, map_commutator, he] using hc

/-- The whole group satisfies E.1.2(E2) whenever F*(G) is nonabelian simple
and supplemented by a Sylow two-subgroup. The structural assertion holds for
every nontrivial A; elementary abelianness and Sylow containment enter E0 and
the rank condition separately. The radical and the two-residual in the conclusion
are computed on the intrinsic top-subgroup carrier. -/
theorem eCaseComponent_top [IsSimpleGroup (generalizedFitting G)]
    (ha : ¬ IsMulCommutative (generalizedFitting G))
    (T₀ : Sylow 2 G) (hgen : generalizedFitting G ⊔ (T₀ : Subgroup G) = ⊤)
    (T A : Subgroup G) (hne : A ≠ ⊥) : ECaseComponent T A ⊤ := by
  let L := generalizedFitting G
  have hComp : IsComponent G L := SimpleSocle.isComponent ha
  let := hComp.2
  obtain ⟨_, hR, _, _, _, _, hq⟩ :=
    SimpleSocle.structure_of_sylow_supplement ha T₀ hgen
  let e : G ≃* (⊤ : Subgroup G) := Subgroup.topEquiv.symm
  let D := L.map e.toMonoidHom
  let : D.Normal := (inferInstance : L.Normal).map _ e.surjective
  let : IsSimpleGroup D := (MulEquiv.isSimpleGroup_congr (e.subgroupMap L)).mp inferInstance
  have hD := hComp.map_equiv e
  let := hD.2
  have hRD : solvableRadical (⊤ : Subgroup G) = ⊥ := by
    rw [← map_solvableRadical_equiv e, hR, Subgroup.map_bot]
  have hqD : IsPGroup 2 ((⊤ : Subgroup G) ⧸ D) :=
    hq.of_equiv (QuotientGroup.congr L D e rfl)
  have hCD : centralizer (D : Set (⊤ : Subgroup G)) = ⊥ :=
    centralizer_eq_bot_of_simple_two_quotient D (Group.IsPerfect.not_isMulCommutative D)
      hqD (SimpleSocle.pCore_eq_bot hRD 2)
  apply eCaseComponent_of_simple_normal T A ⊤ D hCD hqD
  intro h
  apply hne
  have hm := congrArg (Subgroup.map (⊤ : Subgroup G).subtype) h
  simpa only [map_subgroupOf_eq_of_le le_top, Subgroup.map_bot] using hm

/-- The actual whole-group E-member used by the rank-one upper-bound assembly.
The only remaining model input is the elementary rank bound. -/
theorem isEMemberAt_top_of_simple_generalizedFitting {i : ℕ}
    [IsSimpleGroup (generalizedFitting G)]
    (ha : ¬ IsMulCommutative (generalizedFitting G))
    (T₀ : Sylow 2 G) (hgen : generalizedFitting G ⊔ (T₀ : Subgroup G) = ⊤)
    (S : Sylow 2 G) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAS : A ≤ (S : Subgroup G)) (hne : A ≠ ⊥) (hrank : Group.rank A ≤ i) :
    IsEMemberAt i (S : Subgroup G) A ⊤ :=
  isEMemberAt_top_of_component_and_rank S A hA hAS
    (eCaseComponent_top ha T₀ hgen (S : Subgroup G) A hne) hrank

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper
