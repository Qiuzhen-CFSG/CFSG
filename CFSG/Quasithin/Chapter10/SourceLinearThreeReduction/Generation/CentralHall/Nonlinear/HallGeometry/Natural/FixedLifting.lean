module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.FactorKernel
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.Representation.SL2OrthogonalCover.FullFixed.Quotients

/-!
# Fixed quotient vectors in the original natural central cover

Every fixed vector in the given natural quotient has a lift fixed by the same
normalizer. The original two-core action descends to the component quotient;
the fully moved condition makes this a central cover. Apply the universal
orthogonal-cover fixed-lifting theorem without discarding the central kernel.
This extends the original nonzero-vector application in
`MovingHall.NaturalRow.FixedVector` to every fixed quotient vector.
Source: Aschbacher--Smith, I.2.3 and 10.1.2(5), printed pp.742,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

set_option backward.isDefEq.respectTransparency false in
theorem natural_section_fixed_lift
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (P : Subgroup G) (hPL : P ≤ normalizer (L : Set G))
    (hPW : P ≤ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (η : Representation (ZMod 2) P (Fin 2 → F))
    (hηc : ∀ (p : P) (w : (⁅D.fullModule,L⁆ : Subgroup G)),
      η p (c.coordinates w).toAdd =
        (c.coordinates ((⁅D.fullModule,L⁆ : Subgroup G).normalizerMonoidHom
          (inclusion hPW p) w)).toAdd)
    (v : Fin 2 → F) (hv : ∀ p, η p v = v) :
    ∃ w : (⁅D.fullModule,L⁆ : Subgroup G),
      (c.coordinates w).toAdd = v ∧ (w:G) ∈ centralizer (P : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  obtain ⟨σ,hσ⟩ := BinaryConjugationSection.exists_action_of_central_kernel
    L W (normalizer_commutator_ge_right _ _) q hq (by
      intro l hl
      have hp : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp
        (e.injective (hl.trans e.map_one.symm))
      exact centralizer_le hWV (source_component_core_centralizes_fullModule D
        (mem_map_of_mem L.subtype hp)))
  obtain ⟨π,hπ,hπc⟩ := c.exists_cover_of_fully_moved SL2.BinarySmall.natural q hq σ hσ
    inf_le_right (source_full_moved_eq_commutator D)
  let τ := BinaryConjugationSection.originalNormalizerAction hPW
  let a : P →* MulAut SL(2,F) :=
    (MulAut.congr e).toMonoidHom.comp
      ((quotientAut (pCore 2 L)).comp (L.normalizerMonoidHom.comp (inclusion hPL)))
  have ha (p : P) (l : L) : a p (q l) = q (L.normalizerMonoidHom (inclusion hPL p) l) := by
    change e (quotientAut (pCore 2 L)
      (L.normalizerMonoidHom (inclusion hPL p)) (e.symm (e (QuotientGroup.mk' _ l)))) = _
    rw [e.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have ht := BinaryConjugationSection.originalNormalizerAction_compatible q hq σ hσ hPL hPW a ha
  have hη (p : P) (w : Additive W) : π (τ p w) = η p (π w) := by
    rw [hπc,hπc,hηc]
    exact congrArg (fun x => (c.coordinates x).toAdd)
      (BinaryConjugationSection.originalNormalizerAction_apply hPW p w)
  have hqa := BinaryConjugationSection.quotient_action_compatible π hπ.1 τ η a ht hη
  obtain ⟨w,hw,hwf⟩ := SL2OrthogonalCover.FullFixed.fixed_lift_of_cover
    degree hdegree hF π hπ a η τ hqa ht hη hv
  refine ⟨w.toMul,?_,?_⟩
  · rw [←hπc]
    exact hw
  · intro p hp
    have hh := BinaryConjugationSection.originalNormalizerAction_apply_coe hPW ⟨p,hp⟩ w
    rw [hwf] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh.symm
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
