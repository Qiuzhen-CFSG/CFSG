module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.SplitSixteen.FieldAction
public import Theory.SpecificGroups.PSL2.FieldActionComparison

/-!
# Original-input field-extension data

The component catalogue and its prime exclusion produce a quadratic
PSL2 model with prime congruent to three or five modulo eight. The actual
Sylow involution and semilinear action then supply all fields of a marked
Frobenius extension. Only the genuine earlier A/C inputs remain in the
source alternative; no action or recognition conclusion is a premise.

Source: Aschbacher--Smith F.6.18(8)--(9), printed p.310, with the square-field
alternative stated using its proved congruence and ambient action.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly

/-- The actual quadratic-field extension, preserving the original component,
Sylow involution, generated ambient group and Frobenius action. -/
structure QuadraticFieldExtensionData {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal] (T : Sylow 2 G) where
  prime : ℕ
  prime_isPrime : prime.Prime
  odd : Odd prime
  congruence : prime % 8 = 3 ∨ prime % 8 = 5
  field : Type
  [fieldStructure : Field field]
  [finite : Finite field]
  card : Nat.card field = prime ^ 2
  componentEquiv : K ≃* PSL(2,field)
  automorphism : field ≃+* field
  frobenius : ∀ x, automorphism x = x ^ prime
  element : G
  mem_sylow : element ∈ T
  involution : orderOf element = 2
  outside : element ∉ K
  generated : K ⊔ zpowers element = ⊤
  action : ∀ k : K, componentEquiv (MulAut.conjNormal element k) =
    Theory.PSL2.OuterSolvable.projectiveFieldAutHom automorphism (componentEquiv k)

attribute [instance] QuadraticFieldExtensionData.fieldStructure QuadraticFieldExtensionData.finite

variable {G : Type*} [Group G] [Finite G]

theorem quadratic_field_extension_data_of_component
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) [K.Normal] (hFstar : generalizedFitting G = K)
    (hquot : IsPGroup 2 (G ⧸ K)) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL K 2 (p ^ 2)) :
    Nonempty (QuadraticFieldExtensionData K T) := by
  have hmod := square_psl_component_congruence_of_split_sixteen T eT K hp ho hm
  obtain ⟨F, _, _, hF, ⟨j⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨eK, σ, t, hσ, ht, hto, hout, hgen, hact⟩ :=
    square_psl_component_frobenius_action T eT K hFstar hquot ho hF j
  exact ⟨{
    prime := p
    prime_isPrime := hp
    odd := ho
    congruence := hmod
    field := F
    card := hF
    componentEquiv := eK
    automorphism := σ
    frobenius := hσ
    element := t
    mem_sylow := ht
    involution := hto
    outside := hout
    generated := hgen
    action := by
      intro k
      rw [Theory.PSL2.projectiveFieldAutHom_eq_psl2FieldAut]
      exact hact k }⟩

universe u
variable {H : Type u} [Group H] [Finite H]

/-- The complete original-input split-sixteen source reduction to a marked
quadratic field extension or one of the actual alternating component covers. -/
theorem source_split_sixteen_field_or_alternating_components
    {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
    {G₁ G₂ : Subgroup G}
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ ((pResidual 2 G) ⧸ center (pResidual 2 G)))
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (_h : IsGoldschmidtTriple G₁ G₂)
    (hFstar : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G))
    (T : Sylow 2 G) (hT : (T : Subgroup G) = G₁ ⊓ G₂)
    (eT : (G₁ ⊓ G₂ : Subgroup G) ≃* (Multiplicative (ZMod 2) × DihedralGroup 4)) :
    Nonempty (QuadraticFieldExtensionData (pResidual 2 G) T) ∨
    Nonempty ((pResidual 2 G) ≃* Atlas.Codes.HexEvenAutomorphisms) ∨
    Nonempty ((pResidual 2 G) ≃* alternatingGroup (Fin 7)) ∨
    Nonempty ((pResidual 2 G) ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven) := by
  have hK : IsComponent G (pResidual 2 G) :=
    ⟨(inferInstance : (pResidual 2 G).Normal).isSubnormal, hq⟩
  let jT := (MulEquiv.subgroupCongr hT).trans eT
  rcases component_models_of_split_sixteen_refined hA hC hH e hK hFstar.symm
    (isPGroup_quotient_pResidual 2) T jT with hm | hm | hm | hm
  · obtain ⟨p, hp, ho, _, hm⟩ := hm
    exact .inl (quadratic_field_extension_data_of_component T jT (pResidual 2 G)
      hFstar.symm (isPGroup_quotient_pResidual 2) hp ho hm)
  · exact .inr (.inl hm)
  · exact .inr (.inr (.inl hm))
  · exact .inr (.inr (.inr hm))

end CFSG.Quasithin.ChapterF.SourceAssembly
