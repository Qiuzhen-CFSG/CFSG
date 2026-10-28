module

public import CFSG.Quasithin.ChapterG.Section11.NaturalCentralizer
public import CFSG.Quasithin.ChapterG.Section07.AlternatingSevenCover.LocalStructure
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankSquareFree

/-!
# Excluding the doubled natural A₇ row

The original centralizer embeds in S₃ and so has two-rank at most one.
Conjugation on the normal A₇ subgroup has this centralizer as its kernel,
while Aut(A₇) has two-rank at most three. Hence the ambient group has
two-rank at most four. G.10.2 bounds the original module dimension by ten,
contrary to the twelve-dimensional doubled natural A₇ action.

The proper marked reduction therefore leaves only doubled natural A₆ or A₈,
with the centralizer bound already proved on the original component orbit.
The solvable, whole marked and exchanged branches remain explicit.

Source: Aschbacher--Smith G.10.2 and G.11.7--8, printed pp.357,366--368.
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

/-- The centralizer bound applies to the original subgroup, rather than
only to its image on a constituent. -/
theorem natural_centralizer_two_rank (hρ : Function.Injective ρ)
    (H : Subgroup G) (n : ℕ)
    (hmodel : Section09.Quasiequivalent (ρ.comp H.subtype)
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin n)).prod
        (BinaryPermutation.alternatingNaturalRepresentation (Fin n))))
    (hn : n = 6 ∨ n = 7 ∨ n = 8) :
    primeRank 2 (centralizer (H : Set G)) ≤ 1 := by
  obtain ⟨j,hj⟩ := natural_centralizer_embedding ρ hρ H n hmodel hn
  apply (_root_.primeRank_le_of_injective 2 j hj).trans
  apply primeRank_le_one_of_square_not_dvd
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

/-- Conjugation on a normal doubled natural A₇ component bounds the
two-rank of the entire faithful ambient group by four. -/
theorem doubled_seven_ambient_two_rank (hρ : Function.Injective ρ)
    (H : Subgroup G) [H.Normal]
    (hmodel : Section09.Quasiequivalent (ρ.comp H.subtype)
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin 7)).prod
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 7)))) :
    primeRank 2 G ≤ 4 := by
  have hC := natural_centralizer_two_rank hρ H 7 hmodel (by simp)
  obtain ⟨e,_,_⟩ := hmodel
  have hA : primeRank 2 (MulAut H) ≤ 3 :=
    (_root_.primeRank_le_of_injective 2 (MulAut.congr e).toMonoidHom
      (MulAut.congr e).injective).trans
      Section07.AlternatingSevenCover.alternating_seven_automorphism_two_rank
  have hG := primeRank_le_ker_add (p := 2) (MulAut.conjNormal : G →* MulAut H)
  rw [MulAut.conjNormal_ker_eq_centralizer] at hG
  omega

/-- G.10.2 excludes the twelve-dimensional doubled natural A₇ action
on any normal subgroup of the original faithful group. -/
theorem not_doubled_natural_seven (h : Section10.Hypothesis ρ B v W X X₀)
    (H : Subgroup G) [H.Normal]
    (hmodel : Section09.Quasiequivalent (ρ.comp H.subtype)
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin 7)).prod
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 7)))) : False := by
  have hr := doubled_seven_ambient_two_rank h.faithful H hmodel
  have hd := h.dimension_bound
  obtain ⟨_,f,_⟩ := hmodel
  have hdim : finrank (ZMod 2) V = 12 := by
    simpa only [Module.finrank_prod,
      BinaryPermutation.finrank_natural_odd (Fin 7) (by decide),Fintype.card_fin] using f.finrank_eq
  omega

/-- The proper marked branch has only the doubled natural A₆ and A₈ rows,
with the bound on its literal ambient centralizer. -/
theorem proper_marked_constituent_even_natural_actions
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable G) {L : Subgroup G} (hL : IsComponent G L)
    (hm : ⁅L,X⁆ ≠ ⊥) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ (componentOrbit L ⊤) I) (hv : v ∈ I) (hp : I ≠ ⊤) :
    Conclusion ρ B X ∨
      ∃ n, (n = 6 ∨ n = 8) ∧
        Section09.Quasiequivalent (ρ.comp (componentOrbit L ⊤).subtype)
          ((BinaryPermutation.alternatingNaturalRepresentation (Fin n)).prod
            (BinaryPermutation.alternatingNaturalRepresentation (Fin n))) ∧
        ((n = 6 ∧ finrank (ZMod 2) V = 8) ∨ (n = 8 ∧ finrank (ZMod 2) V = 12)) ∧
        primeRank 2 (centralizer (componentOrbit L ⊤ : Set G)) ≤ 1 := by
  rcases proper_marked_constituent_natural_actions h cover hw hS hn hL hm hI hv hp
    with hc | ⟨n,hn6,hn8,hmodel,hd⟩
  · exact Or.inl hc
  · let := componentOrbit_top_normal L
    have hn7 : n ≠ 7 := by
      intro he
      subst n
      exact not_doubled_natural_seven h (componentOrbit L ⊤) hmodel
    refine Or.inr ⟨n,by omega,hmodel,?_,?_⟩
    · rcases hd with hd | ⟨hn,hd⟩
      · exact Or.inl hd
      · exact Or.inr ⟨hn.resolve_left hn7,hd⟩
    · exact natural_centralizer_two_rank h.faithful _ n hmodel (by omega)

/-- The remaining component branches, with doubled natural A₇ excluded
from the proper marked branch and the actual centralizer rank retained. -/
def EvenNaturalComponentReduction (ρ : Representation (ZMod 2) G V)
    (B : LinearMap.BilinForm (ZMod 2) V) (v : V) (W : Submodule (ZMod 2) V)
    (X : Subgroup G) [IsElementaryAbelian 2 X] : Prop :=
    ∃ L : Subgroup G, IsComponent G L ∧ ⁅L,X⁆ ≠ ⊥ ∧
      Section10.ComponentOrthogonalData ρ B L ∧
      ∃ I : Submodule (ZMod 2) V, ∃ hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I,
        (v ∈ I ∧ MarkedConstituentAlternative ρ B v X L I hI.isIrrPlus ∧
          (I = ⊤ ∨ ∃ n, (n = 6 ∨ n = 8) ∧
            Section09.Quasiequivalent (ρ.comp (componentOrbit L ⊤).subtype)
              ((BinaryPermutation.alternatingNaturalRepresentation (Fin n)).prod
                (BinaryPermutation.alternatingNaturalRepresentation (Fin n))) ∧
            ((n = 6 ∧ finrank (ZMod 2) V = 8) ∨ (n = 8 ∧ finrank (ZMod 2) V = 12)) ∧
            primeRank 2 (centralizer (componentOrbit L ⊤ : Set G)) ≤ 1)) ∨
          (v ∉ I ∧ Section10.ExchangedConstituentGeometry ρ B v W X I)

/-- Apply the A₇ exclusion to the original low-rank source hypotheses,
preserving the other unresolved source branches. -/
theorem conclusion_or_even_natural_component_reduction
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X) :
    Conclusion ρ B X ∨
      (IsIrreducible ρ ∧ 6 ≤ finrank (ZMod 2) V ∧
        ((Group.IsSolvable G ∧ finrank (ZMod 2) (Additive X) = 2 ∧
            finrank (ZMod 2) V = 6) ∨
          (¬ Group.IsSolvable G ∧ EvenNaturalComponentReduction ρ B v W X))) := by
  rcases conclusion_or_component_reduction h cover hw hS with hc | ⟨hi,hd,hs | ⟨hn,hh⟩⟩
  · exact Or.inl hc
  · exact Or.inr ⟨hi,hd,Or.inl hs⟩
  · obtain ⟨L,hL,hm,horth,I,hI,hmarked | hexchanged⟩ := hh
    · obtain ⟨hv,hdata⟩ := hmarked
      by_cases hp : I = ⊤
      · exact Or.inr ⟨hi,hd,Or.inr ⟨hn,L,hL,hm,horth,I,hI,Or.inl ⟨hv,hdata,Or.inl hp⟩⟩⟩
      · rcases proper_marked_constituent_even_natural_actions h cover hw hS hn hL hm
          hI.isIrrPlus hv hp with hc | hnat
        · exact Or.inl hc
        · exact Or.inr ⟨hi,hd,Or.inr ⟨hn,L,hL,hm,horth,I,hI,Or.inl ⟨hv,hdata,Or.inr hnat⟩⟩⟩
    · exact Or.inr ⟨hi,hd,Or.inr ⟨hn,L,hL,hm,horth,I,hI,Or.inr hexchanged⟩⟩

end CFSG.Quasithin.ChapterG.Section11
