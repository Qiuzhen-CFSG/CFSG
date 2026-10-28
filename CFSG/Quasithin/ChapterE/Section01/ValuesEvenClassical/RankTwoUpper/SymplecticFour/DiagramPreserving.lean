module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.DiagramPreserving.LocalMembers
public import CFSG.Quasithin.Defs
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvariantLocalPair
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ResidualGeneration

/-!
# Diagram-preserving nonbinary symplectic E-generation

Choose an ambient Sylow subgroup extending the standard unipotent subgroup
of the normal symplectic model. Diagram preservation makes that Sylow
normalize both actual determinant kernels. Each kernel joined with this
Sylow is handled by the complete local E2 and quotient-rank calculation.
The two kernels generate the normal model, and the Sylow supplements it,
so these two local joins give E-generation for every elementary family.

The argument works for any normal Sp₄ with two-group quotient. In particular
it proves the source branch with simple F*(G), the SQTK hypothesis and
G = F*(G)T; no further local or generation premises are required. The full
source theorem's other automorphism and binary branches remain separate.

Source: Aschbacher--Smith E.1.14(1), printed p.214, citing Aschbacher (1982),
Lemma 4.7; definitions E.1.1--5 are on printed pp.209--211. The symplectic
local geometry is also used in F.1.12, printed pp.263--264.
-/

public section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.DiagramPreserving
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- E-generation in every diagram-preserving normal symplectic extension
with two-group quotient, including nontrivial field actions. -/
theorem isEGenerated_of_normal_symplectic {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (N : Subgroup G) [N.Normal] (e : Sp F ≃* N)
    (hq : IsPGroup 2 (G ⧸ N))
    (hdiagram : ∀ g : G, DiagramAutomorphisms.PreservesDiagram
      (DiagramAutomorphisms.extensionAction N e g)) : IsEGenerated f G := by
  let j := N.subtype.comp e.toMonoidHom
  have hj : Function.Injective j := N.subtype_injective.comp e.injective
  let D₁ := pointLocal.map j
  let D₂ := planeLocal.map j
  let d₁ : D₁ ≃* pointLocal (F := F) := (pointLocal.equivMapOfInjective j hj).symm
  let d₂ : D₂ ≃* planeLocal (F := F) := (planeLocal.equivMapOfInjective j hj).symm
  let := pointLocal_perfect hF hf
  let := planeLocal_perfect hF hf
  let : Group.IsPerfect D₁ := Group.IsPerfect.ofSurjective
    (f := d₁.symm.toMonoidHom) d₁.symm.surjective
  let : Group.IsPerfect D₂ := Group.IsPerfect.ofSurjective
    (f := d₂.symm.toMonoidHom) d₂.symm.surjective
  let e₁ : (D₁ ⧸ pCore 2 D₁) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.congr _ _ d₁ (pCore_map_iso 2 d₁)).trans
      (pointLocalCoreQuotientEquiv hF hf)
  let e₂ : (D₂ ⧸ pCore 2 D₂) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.congr _ _ d₂ (pCore_map_iso 2 d₂)).trans
      (planeLocalCoreQuotientEquiv hF hf)
  have hlocals : D₁ ⊔ D₂ = N := by
    change pointLocal.map j ⊔ planeLocal.map j = N
    rw [← Subgroup.map_sup, locals_sup_eq_top hF hf]
    dsimp only [j]
    rw [← Subgroup.map_map, map_top_of_surjective _ e.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  obtain ⟨S, _, hS₁, hS₂⟩ :=
    DiagramAutomorphisms.exists_sylow_normalizing_local_pair hF hf N e hdiagram
  apply IsEGeneratedAt.isEGenerated (T := S)
  intro Ω hΩ
  have h₁ := join_le_generated hF hf S D₁ hS₁ e₁ Ω hΩ
  have h₂ := join_le_generated hF hf S D₂ hS₂ e₂ Ω hΩ
  apply top_unique
  rw [← S.sup_eq_top_of_quotient_isPGroup N hq, ← hlocals]
  exact sup_le (le_sup_right.trans h₁)
    (sup_le (le_sup_left.trans h₁) (le_sup_left.trans h₂))

/-- The diagram-preserving nonbinary upper-bound branch of E.1.14(1),
with the source hypotheses and the actual full symplectic carrier. -/
theorem isEGenerated {K : GroupClass} (_hG : IsSQTK K G)
    [IsSimpleGroup (generalizedFitting G)] (T : Sylow 2 G)
    (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (e : Sp F ≃* generalizedFitting G)
    (hdiagram : ∀ g : G, DiagramAutomorphisms.PreservesDiagram
      (DiagramAutomorphisms.extensionAction (generalizedFitting G) e g)) :
    IsEGenerated f G :=
  isEGenerated_of_normal_symplectic hF hf (generalizedFitting G) e
    (isPGroup_quotient_of_sup_eq_top _ _ T.isPGroup' hgen) hdiagram

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.DiagramPreserving
