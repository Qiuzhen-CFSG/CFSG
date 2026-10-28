module
public import CFSG.Quasithin.ChapterG.Section11.Reduction
public import CFSG.Quasithin.ChapterG.Section09.CoverComponents
public import CFSG.Quasithin.ChapterG.Section10.Components.Source
public import CFSG.Quasithin.ChapterG.Section10.Components.Homogeneous
public import CFSG.Quasithin.ChapterG.Section10.Components.Exchanged
public import Theory.Representation.BinaryOffender.Homogeneous.SmallDisplacement

/-!
# Low-rank multiplicity in the actual G.11 component orbit

The SQTK cover bounds the component orbit by two conjugates; relative
Sylow normality supplies the G.10 movement and marked-point arguments.
For a constituent containing the marked point, those arguments construct
homogeneity, faithfulness and self-duality on the same normal orbit.

The low-rank witness then bounds multiplicity by two. A proper constituent
is isotropic, its two copies fill V, and the same witness acts with rank one
on each. An improper constituent supplies the original G.9 component
hypotheses. The other branch retains the actual exchanged-constituent
geometry, including its half-point. No model recognition is assumed here.

This eliminates the higher homogeneous multiplicities in the requested
G.11.1(3ii) specialization, but leaves group and module recognition open.
Source: Aschbacher--Smith G.10.16(4), G.11.6--8, printed pp.363--368.
-/

@[expose] public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

/-- The output of the marked low-rank multiplicity argument, before model
recognition. Both branches retain the same normal component orbit and action. -/
def MarkedConstituentAlternative (ρ : Representation (ZMod 2) G V)
    (B : LinearMap.BilinForm (ZMod 2) V) (v : V) (X : Subgroup G)
    [IsElementaryAbelian 2 X] (L : Subgroup G)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ (componentOrbit L ⊤) I) : Prop :=
  let H := componentOrbit L ⊤
  let R := invariantSubspace ρ H I hI.choose
  Homogeneous.homogeneousPart R ⊤ = ⊤ ∧
    Function.Injective R.toRepresentation ∧
    Nonempty (Representation.Equiv R.toRepresentation R.toRepresentation.dual) ∧
    ((I = ⊤ ∧ Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ X L H
        (finrank (ZMod 2) (Additive X))) ∨
      ((∀ u ∈ I, ∀ w ∈ I, B u w = 0) ∧
        finrank (ZMod 2) V = 2 * finrank (ZMod 2) I ∧
        Nonempty (Representation.Equiv (ρ.comp H.subtype)
          (R.toRepresentation.prod R.toRepresentation)) ∧
        ∃ a ∈ X, orderOf a = 2 ∧ v ∈ RankTwo.movedSpace ρ a ∧
          I.map (ρ a) = I ∧ finrank (ZMod 2) (RankTwo.movedSpace ρ a) = 2 ∧
          finrank (ZMod 2) (I.map (ρ a - LinearMap.id)) = 1))

/-- The marked constituent is the whole module or exactly half of it, with
an actual double-module equivalence and rank-one witness in the latter case. -/
theorem marked_constituent_alternative
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable G) {L : Subgroup G} (hL : IsComponent G L)
    (hm : ⁅L,X⁆ ≠ ⊥) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ (componentOrbit L ⊤) I) (hv : v ∈ I) :
    MarkedConstituentAlternative ρ B v X L I hI := by
  let := componentOrbit_top_normal L
  obtain ⟨S,hSv,hXS,hnS⟩ := hS
  have hnX := (normal_subgroupOf_iff_le_normalizer hXS).mp hnS
  obtain ⟨c⟩ := cover
  have hind := c.component_normalizer_index_le_two hL
  have hdata := h.constituent_homogeneous_faithful_selfDual_of_point_mem
    hn hL hm S hnX hind hI hv
  refine ⟨hdata.1,hdata.2.1,hdata.2.2.1,?_⟩
  by_cases ht : I = ⊤
  · left
    have hi : IsIrreducible (ρ.comp (componentOrbit L ⊤).subtype) := by
      have hR := hI.irreducible_of_normal_restriction ρ (h.irreducible_of_not_solvable hn)
        (componentOrbit L ⊤)
      have ha := (Subrepresentation.irreducible_iff_isAtom _).mp hR
      have htop : invariantSubspace ρ (componentOrbit L ⊤) I hI.choose = ⊤ :=
        Subrepresentation.toSubmodule_injective ht
      exact isSimpleOrder_iff_isAtom_top.mpr (htop ▸ ha)
    exact ⟨ht,h.componentHypothesis_of_orbit_irreducible ⟨c⟩ hL hm hind hi⟩
  · right
    have hiso := hdata.2.2.2.resolve_right (fun he => ht he.1)
    obtain ⟨a,ha,ha2,hapos,har,hav⟩ := hw.exists_involution h.point_ne_zero
    let H := componentOrbit L ⊤
    let := componentOrbit_top_normal L
    let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
    let R := invariantSubspace ρ H I hI.choose
    have hR := hI.irreducible_of_normal_restriction ρ (h.irreducible_of_not_solvable hn) H
    have hsame := h.constituent_sameModule_of_point_mem hn hL hm S hnX hind hI hv
    have hd := hI.finrank_gt_two ρ H
    have hdouble := Homogeneous.double_and_rank_one_of_small_displacement ρ H R hR
      hdata.1 hdata.2.1 hsame hd a hapos har ht
    exact ⟨hiso,hdouble.1,hdouble.2.1,a,ha,ha2,hav,hdouble.2.2⟩

/-- Concrete output of the constituent reduction. This predicate is
constructed below and contains no model-classification assertion. -/
def ComponentReduction (ρ : Representation (ZMod 2) G V)
    (B : LinearMap.BilinForm (ZMod 2) V) (v : V) (W : Submodule (ZMod 2) V)
    (X : Subgroup G) [IsElementaryAbelian 2 X] : Prop :=
    ∃ L : Subgroup G, IsComponent G L ∧ ⁅L,X⁆ ≠ ⊥ ∧
      Section10.ComponentOrthogonalData ρ B L ∧
      ∃ I : Submodule (ZMod 2) V, ∃ hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I,
        (v ∈ I ∧ MarkedConstituentAlternative ρ B v X L I hI.isIrrPlus) ∨
          (v ∉ I ∧ Section10.ExchangedConstituentGeometry ρ B v W X I)

/-- The two constituent branches are constructed from the original source
inputs. The marked branch has multiplicity at most two; the exchanged branch
retains its literal half-point and full transvection geometry. -/
theorem nonsolvable_constituent_reduction
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable G) :
    ComponentReduction ρ B v W X := by
  have hF := h.fitting_centralizer_ne_bot_of_not_solvable cover hn
  obtain ⟨L,hL,hm,hsel,horth⟩ := h.exists_moved_component_orthogonal_selection hn hF
  obtain ⟨_,_,I,hI,_⟩ := hsel
  refine ⟨L,hL,hm,horth,I,hI,?_⟩
  by_cases hv : v ∈ I
  · exact Or.inl ⟨hv,marked_constituent_alternative h cover hw hS hn hL hm hI.isIrrPlus hv⟩
  · right
    obtain ⟨S,hSv,hXS,hnS⟩ := hS
    obtain ⟨c⟩ := cover
    exact ⟨hv,h.exchanged_constituent_geometry hn hL hm S
      ((normal_subgroupOf_iff_le_normalizer hXS).mp hnS)
      (c.component_normalizer_index_le_two hL) hI hv⟩

/-- The original low-rank source input reduces to the proved small cases,
the degree-six solvable case, or the two concrete constituent branches. -/
theorem conclusion_or_component_reduction
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X) :
    Conclusion ρ B X ∨
      (IsIrreducible ρ ∧ 6 ≤ finrank (ZMod 2) V ∧
        ((Group.IsSolvable G ∧ finrank (ZMod 2) (Additive X) = 2 ∧
            finrank (ZMod 2) V = 6) ∨
          (¬ Group.IsSolvable G ∧ ComponentReduction ρ B v W X))) := by
  rcases conclusion_or_remaining_structure h cover hw with hc | ⟨hi,hd,hs | ⟨hn,_⟩⟩
  · exact Or.inl hc
  · exact Or.inr ⟨hi,hd,Or.inl hs⟩
  · exact Or.inr ⟨hi,hd,Or.inr ⟨hn,nonsolvable_constituent_reduction h cover hw hS hn⟩⟩

end CFSG.Quasithin.ChapterG.Section11
