module

public import Mathlib.Algebra.Field.ULift
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SquareField
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.SplitSixteen.FieldExtension
public import Theory.SpecificGroups.PSL2.FieldActionTransport
/-!
# The literal square-field source adapter

The lower split-sixteen theorem constructs the actual component, Frobenius
involution and conjugation action from the original SQTK quotient. Field
transport lifts its field into the ambient universe and preserves that action.
The residual–Fitting equality transports the same embedded component; the
original common Sylow is unchanged. The alternative source branches are the
actual alternating-six and alternating-seven covers supplied by the catalogue.
Source: Aschbacher–Smith F.6.17–18, printed pp.309–310.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
universe u
variable {G : Type u} [Group G] [Finite G]
theorem square_field_extension_of_data (S : Sylow 2 G) (eS : S ≃* (C 2 × DihedralGroup 4))
    (hF : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G))
    (d : ChapterF.SourceAssembly.QuadraticFieldExtensionData (pResidual 2 G) S) :
    Nonempty (SquareFieldExtensionRow S) := by
  let F : FieldParameter.{u} :=
    { Carrier := ULift.{u} d.field
      prime := d.prime
      prime_isPrime := d.prime_isPrime
      degree := 2
      degree_pos := by decide
      card := by simpa using d.card }
  let j : d.field ≃+* F.Carrier := ULift.ringEquiv.symm
  let σ : F.Carrier ≃+* F.Carrier := (j.symm.trans d.automorphism).trans j
  let a : generalizedFitting G ≃* pResidual 2 G := MulEquiv.subgroupCongr hF.symm
  let e : generalizedFitting G ≃* PSL(2,F.Carrier) :=
    (a.trans d.componentEquiv).trans (Atlas.fieldEquivPSL 2 j)
  let : IsQuasisimple (pResidual 2 G) := hq
  refine ⟨{
    field := F
    degree := rfl
    congruence := d.congruence
    componentEquiv := e
    quasisimple := IsQuasisimple.of_mulEquiv a.symm
    sylow := ⟨eS⟩
    automorphism := σ
    frobenius := ?_
    element := d.element
    involution := d.involution
    outside := ?_
    generated := ?_
    action := ?_ }⟩
  · intro x
    change j (d.automorphism (j.symm x)) = x ^ d.prime
    rw [d.frobenius, map_pow, j.apply_symm_apply]
  · simpa only [← hF] using d.outside
  · simpa only [← hF] using d.generated
  · intro x
    let y : generalizedFitting G := MulAut.conjNormal d.element x
    refine ⟨y, rfl, ?_⟩
    have ha : a y = MulAut.conjNormal d.element (a x) := by rfl
    change Atlas.fieldEquivPSL 2 j (d.componentEquiv (a y)) =
      Theory.PSL2.OuterSolvable.projectiveFieldAutHom σ
        (Atlas.fieldEquivPSL 2 j (d.componentEquiv (a x)))
    rw [ha,d.action]
    exact Theory.PSL2.projectiveFieldAutHom_fieldEquiv j d.automorphism σ
      (fun z => by simp [σ]) _

/-- Original-input split-sixteen source reduction. The square-field branch
has every actual action field; the remaining component models feed the
separate alternating extension and marked-local source families. -/
theorem split_sixteen_source_reduction
    {κ : GroupClass.{u}} {G₁ G₂ : Subgroup G}
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (eS : S ≃* (C 2 × DihedralGroup 4))
    (hF : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G)) :
    Nonempty (SquareFieldExtensionRow S) ∨
      Nonempty ((pResidual 2 G) ≃* Atlas.Codes.HexEvenAutomorphisms) ∨
      Nonempty ((pResidual 2 G) ≃* alternatingGroup (Fin 7)) ∨
      Nonempty ((pResidual 2 G) ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven) := by
  let := q.coverGroup
  let := q.coverFinite
  rcases ChapterF.SourceAssembly.source_split_sixteen_field_or_alternating_components
    (hA _) (hC _) q.sqtk q.equiv.symm h hF hq S hS.symm
    ((MulEquiv.subgroupCongr hS).trans eS) with hd | hm
  · exact Or.inl (square_field_extension_of_data S eS hF hq hd.some)
  · exact Or.inr hm

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
