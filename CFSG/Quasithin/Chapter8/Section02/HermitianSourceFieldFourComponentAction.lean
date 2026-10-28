module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourTensor
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.DihedralInspection.Scalars
public import Theory.Representation.InvertedFiveTensor.Sixteen
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The containing Hermitian component on the quintic multiplicity plane

The literal D₁₀ quotient supplies a fifth rotation in the embedded O²(I).
Its action on P/U is fixed-point-free by the marked tensor construction.
The recovered sixteen-element scalars therefore act on the same carrier.
Perfectness of K makes its action commute with the residual rotation;
scalar refinement gives a two-dimensional action with determinant one.

The original quotient maps are retained. Its kernel is the full commutator
kernel C_K(P/U), and restriction to the original R has kernel O₂(R).
No equality R=K or extra field-generator marking is assumed. The Chapter12
consumer supplies the normalization and commutator inputs from the original
chosen module and containing component.

Source: Aschbacher–Smith 8.2.8(1), final paragraph on printed p.719,
refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open Normalizer.SmallOvergroups Normalizer.TensorRecognition
abbrev Sixteen := InvertedFiveTensor.Sixteen.Field
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G]

/-- The original containing component acts on P/U as a plane over F₁₆.
The scalar root is an actual residual rotation, and both the full kernel
and its restriction to R are retained. -/
@[expose] def QuinticComponentAction (R K I U : Subgroup G) : Prop :=
  ∃ hUP : (U.subgroupOf (I.pCoreIn 2)).Normal, letI := hUP
    ∃ hP : IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)), letI := hP
      ∃ eI : (I ⧸ pCore 2 I) ≃* DihedralGroup 5,
        ∃ σ : Representation (ZMod 2) (DihedralGroup 5) (CoreSection I U),
          ∃ hf : ∀ p, σ InvertedFiveTensor.rot p = p → p = 0,
            letI := InvertedFiveTensor.Sixteen.moduleSixteen σ hf
            ∃ hKP : K ≤ normalizer (I.pCoreIn 2 : Set G),
              ∃ hKU : K ≤ normalizer (U : Set G),
                ∃ hIC : I ≤ centralizer (U : Set G),
                  ∃ hRK : R ≤ K,
                    ∃ β : K →* (CoreSection I U ≃ₗ[Sixteen] CoreSection I U),
                      Module.finrank Sixteen (CoreSection I U) = 2 ∧
                      (∀ (k : K) p, β k p = Additive.ofMul
                        (sectionAction K (I.pCoreIn 2) U hKP hKU k p.toMul)) ∧
                      (∀ k, (β k).det = 1) ∧
                      (∀ k : K, k ∈ β.ker ↔ ∀ p : I.pCoreIn 2, ⁅(k : G),(p : G)⁆ ∈ U) ∧
                      (β.comp (inclusion hRK)).ker = pCore 2 R ∧
                      ∃ x : (pResidual 2 I).map I.subtype,
                        eI (QuotientGroup.mk' (pCore 2 I) ⟨x.val,map_subtype_le _ x.property⟩) =
                          InvertedFiveTensor.rot ∧
                        ∀ p : CoreSection I U,
                          InvertedFiveTensor.Sixteen.root • p =
                            Additive.ofMul (pairResidualQuotientAction I U hIC x p.toMul)

private theorem exists_residual_rotation (I : Subgroup G)
    (eI : (I ⧸ pCore 2 I) ≃* DihedralGroup 5) :
    ∃ x : (pResidual 2 I).map I.subtype,
      eI (QuotientGroup.mk' (pCore 2 I) ⟨x.val,map_subtype_le _ x.property⟩) =
        InvertedFiveTensor.rot := by
  let f := eI.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hm : InvertedFiveTensor.rot ∈ (pResidual 2 I).map f := by
    rw [map_pResidual_of_surjective 2 f
      (eI.surjective.comp (QuotientGroup.mk'_surjective _))]
    apply mem_pResidual_of_orderOf_coprime
    exact (by decide : Nat.Coprime 2 5).of_dvd_right
      (orderOf_dvd_of_pow_eq_one InvertedFiveTensor.rot_fifth)
  obtain ⟨a,ha,he⟩ := hm
  exact ⟨⟨a,⟨a,ha,rfl⟩⟩,he⟩

/-- Construct the full component's two-dimensional action from the marked
quintic tensor, retaining the original quotient and source residual. -/
theorem quintic_component_action {R K I V U : Subgroup G} [Group.IsPerfect K]
    (hp : PairProductAction R I V U) (ht : PairQuinticTensor R I V U)
    (hRK : R ≤ K) (hKU : K ≤ normalizer (U : Set G))
    (hQI : K.pCoreIn 2 ≤ normalizer (I : Set G))
    (hKI : ⁅K,I⁆ ≤ K.pCoreIn 2)
    (hUPle : U ≤ I.pCoreIn 2)
    (hfull : I.pCoreIn 2 = ⁅I.pCoreIn 2,(pResidual 2 I).map I.subtype⁆ ⊔ U)
    (hIC : I ≤ centralizer (U : Set G)) : QuinticComponentAction R K I U := by
  obtain ⟨hYP,hYU,hUP,hBU,hP,hB,eI,σ,hσ,hf,_⟩ := ht
  let := hUP
  let := hP
  obtain ⟨hYP',hYU',_,_,hcard,_,_,hRker,_⟩ := hp
  let P := I.pCoreIn 2
  have hPP : ⁅P,P⁆ ≤ U := by
    rw [←map_subtype_commutator]
    exact (map_mono (Normal.quotient_commutative_iff_commutator_le.mp
      (inferInstance : IsMulCommutative (P ⧸ U.subgroupOf P)))).trans
        (map_subgroupOf_eq_of_le hUPle).le
  obtain ⟨x,hx⟩ := exists_residual_rotation I eI
  have hscalar (p : P ⧸ U.subgroupOf P) :
      letI := InvertedFiveTensor.Sixteen.moduleSixteen σ hf
      Additive.ofMul (pairResidualQuotientAction I U hIC x p) =
        InvertedFiveTensor.Sixteen.root • Additive.ofMul p := by
    rw [InvertedFiveTensor.Sixteen.root_smul,←hx]
    exact (hσ ⟨x.val,map_subtype_le _ x.property⟩ (Additive.ofMul p)).symm
  let := InvertedFiveTensor.Sixteen.moduleSixteen σ hf
  let hKP := component_normalizes_pair_core K I U hQI hKI hKU hUPle hfull
  let β := componentMultiplicityAction K I U eI hQI hKI hKU hUPle hfull
    hIC hPP InvertedFiveTensor.Sixteen.root InvertedFiveTensor.Sixteen.root_generates x hscalar
  have hb (k : K) (p : CoreSection I U) :
      β k p = Additive.ofMul (sectionAction K P U hKP hKU k p.toMul) := by
    exact componentMultiplicityAction_apply K I U eI hQI hKI hKU hUPle hfull
      hIC hPP InvertedFiveTensor.Sixteen.root InvertedFiveTensor.Sixteen.root_generates x hscalar k p.toMul
  have hker : (β.comp (inclusion hRK)).ker = pCore 2 R := by
    rw [←hRker]
    ext r
    constructor
    · intro hr
      apply MulEquiv.ext
      intro p
      have he := LinearEquiv.congr_fun hr (Additive.ofMul p)
      rw [show β.comp (inclusion hRK) r = β (inclusion hRK r) from rfl,hb] at he
      exact congrArg Additive.toMul he
    · intro hr
      apply LinearEquiv.ext
      intro p
      rw [show β.comp (inclusion hRK) r = β (inclusion hRK r) from rfl,hb]
      exact congrArg Additive.ofMul (MulEquiv.congr_fun hr p.toMul)
  refine ⟨hUP,hP,eI,σ,hf,hKP,hKU,hIC,hRK,β,?_,hb,?_,?_,hker,x,hx,?_⟩
  · exact InvertedFiveTensor.Sixteen.finrank_two σ hf hcard
  · exact componentMultiplicityAction_det K I U eI hQI hKI hKU hUPle hfull
      hIC hPP InvertedFiveTensor.Sixteen.root InvertedFiveTensor.Sixteen.root_generates x hscalar
  · exact mem_componentMultiplicityAction_ker K I U eI hQI hKI hKU hUPle hfull
      hIC hPP InvertedFiveTensor.Sixteen.root InvertedFiveTensor.Sixteen.root_generates x hscalar
  · intro p
    exact (hscalar p.toMul).symm
end CFSG.Quasithin.Chapter8.Section02.HermitianSource
