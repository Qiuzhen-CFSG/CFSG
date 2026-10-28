module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ComponentSource.B113Source
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ComponentSource.SelectionAlgebra
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.SourceRanks

/-!
# Specialized B.1.13 from the original SQTK source

B.1.10 and generalized-Fitting self-centralization select a cubic central seed
or an actual moved component. The full earlier A.3.6 gives its possible center
orders; the faithful B.1.11 section and full corrected B.4.2 then prove seed
containment. The bounded model inspection retains only the actual A₅/A₇
exceptions to equality. The final form is the exact subnormal quotient input
to C.1.27; it assumes no component or block-selection certificate.

Source: Aschbacher--Smith B.1.13, pp.73--74; C.1.27, pp.132--133.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource
open ChapterB Chapter1.Section02
universe u
variable {G V : Type u} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- B.1.13's actual component selection with genuine universal A.3.6 and B.4.2.
The proper-containment alternatives name the literal five/seven-letter groups. -/
theorem source_selection
    (h36 : A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (K : Subgroup G) (T : Sylow 2 G)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal)
    (hcomm : K = ⁅K, generatedBy {A | IsBestOffender ρ A} (T : Subgroup G)⁆) :
    (Nat.card K = 3 ∧ K ≤ (center (fittingSubgroup G)).map (fittingSubgroup G).subtype) ∨
    ∃ L, IsComponent G L ∧ K ≤ L ∧ ⁅L,K⁆ = L ∧
      (K = L ∨ Nonempty (L ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (L ≃* alternatingGroup (Fin 7))) := by
  rcases central_fitting_or_moved_component ρ hf hcore K (T : Subgroup G)
      hkind hK hcomm with hc | ⟨L,hL,hLK⟩
  · exact Or.inl hc
  · right
    let : IsQuasisimple L := hL.2
    have hc := ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.center_card_of_common
      (h36 G hG hcore L hL.isCComponent).2
    obtain ⟨hKL,hmodels⟩ := component_containment_of_source_section ρ K L T hL hLK
      hkind hK hcomm hf (hG.subgroup L) hc h4
    exact ⟨L,hL,hKL,hLK,hmodels⟩

omit [Finite G] in
/-- The cubic central alternative is subnormal in the original actor. -/
theorem subnormal_of_le_fitting_center (K : Subgroup G)
    (hz : K ≤ (center (fittingSubgroup G)).map (fittingSubgroup G).subtype) : K.IsSubnormal := by
  let F := fittingSubgroup G
  have hKF : K ≤ F := by
    rintro k hk
    obtain ⟨z,_,rfl⟩ := hz hk
    exact z.property
  have hcent : K.subgroupOf F ≤ center F := by
    intro k hk
    obtain ⟨z,hz,he⟩ := hz hk
    have he' : z = k := Subtype.ext he
    exact he' ▸ hz
  let : (K.subgroupOf F).Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [show g * k * g⁻¹ = k by
      rw [mem_center_iff.mp (hcent hk) g, mul_inv_cancel_right]]
    exact hk
  exact (inferInstance : (K.subgroupOf F).Normal).isSubnormal.trans hKF
    (inferInstance : F.Normal).isSubnormal

/-- Exact quotient-selection input for C.1.27, with an actual subnormal B
and the literal seed/commutator alternative; no selection premise remains. -/
theorem exists_subnormal_container
    (h36 : A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (K : Subgroup G) (T : Sylow 2 G)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal)
    (hcomm : K = ⁅K, generatedBy {A | IsBestOffender ρ A} (T : Subgroup G)⁆) :
    ∃ B : Subgroup G, B.IsSubnormal ∧ K ≤ B ∧
      (IsQuasisimple B ∨ Nat.card B = 3) ∧ (K = B ∨ ⁅K,B⁆ = B) ∧
      (K = B ∨ Nonempty (B ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (B ≃* alternatingGroup (Fin 7))) := by
  rcases source_selection ρ h36 h4 hG hf hcore K T hkind hK hcomm with hz | hL
  · exact ⟨K, subnormal_of_le_fitting_center K hz.2, le_rfl, Or.inr hz.1, Or.inl rfl, Or.inl rfl⟩
  · obtain ⟨L,hL,hKL,hLK,hm⟩ := hL
    exact ⟨L,hL.1,hKL,Or.inl hL.2,Or.inr ((commutator_comm K L).trans hLK),hm⟩

/-- Genuine earlier A/C discharge the universal A.3.6 premise in the original
quotient-selection consumer. Full corrected B.4.2 remains its earlier source. -/
theorem exists_subnormal_container_of_theorems_AC
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h4 : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (K : Subgroup G) (T : Sylow 2 G)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal)
    (hcomm : K = ⁅K, generatedBy {A | IsBestOffender ρ A} (T : Subgroup G)⁆) :
    ∃ B : Subgroup G, B.IsSubnormal ∧ K ≤ B ∧
      (IsQuasisimple B ∨ Nat.card B = 3) ∧ (K = B ∨ ⁅K,B⁆ = B) ∧
      (K = B ∨ Nonempty (B ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (B ≃* alternatingGroup (Fin 7))) :=
  exists_subnormal_container ρ (ChapterA.SQTKStructure.a36Input_of_theoremsAC hA hC)
    h4 hG hf hcore K T hkind hK hcomm

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource
