module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.Action
public import Theory.SpecificGroups.PSL3Two.Parabolics.WreathPairCore

/-!
# The half-Sylow is the factor-preserving kernel of the actual action

The original normalizer of L preserves the first simple factor of the
wreath image. A factor-swapping element cannot do this. On the original
Sylow, the index-two calculation and the specified exchanger give the
converse. Thus the two-cores of the concrete parabolics lie in T₁.
Source: Aschbacher--Smith 10.2.5, pp.747--748.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02
open SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {s : NaturalData D}
  {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

/-- Normalizing the original component forces the permutation coordinate to vanish. -/
theorem LiftData.right_eq_one_of_normalizes (f : LiftData s hz)
    (g : localJoin T L) (hg : (g : G) ∈ normalizer (L : Set G)) :
    (f.hom g).right = 1 := by
  rcases bit_cases (f.hom g).right with he | he
  · exact he
  · exfalso
    let : Nontrivial Matrix.PSL3Two.SL :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [Matrix.PSL3Two.card_SL]; decide)
    obtain ⟨a,ha⟩ := exists_ne (1 : Matrix.PSL3Two.SL)
    obtain ⟨l,hl⟩ := componentHom_surjective s a
    let k : L := ⟨(g : G) * l * (g : G)⁻¹,
      (mem_normalizer_iff.mp hg l).mp l.property⟩
    have hk : componentInclusion k = g * componentInclusion l * g⁻¹ := rfl
    have hm := congrArg f.hom hk
    rw [map_mul,map_mul,map_inv,f.component,f.component,hl,conjugate_first _ he] at hm
    have hc := congrArg (fun x : Actor => x.left other) hm
    simp only [firstBase,secondBase] at hc
    have hcancel : (f.hom g).left other * a * ((f.hom g).left other)⁻¹ = 1 := hc.symm
    have heq : a = 1 := by
      simpa only [mul_inv_eq_one, mul_eq_left] using hcancel
    exact ha heq

/-- On the original full Sylow, the base kernel is exactly N_T(L). -/
theorem LiftData.normalizes_of_right_eq_one (f : LiftData s hz)
    {g : G} (hg : g ∈ (T : Subgroup G))
    (he : (f.hom ⟨g,(show (T : Subgroup G) ≤ localJoin T L from le_sup_right) hg⟩).right = 1) :
    g ∈ normalizer (L : Set G) := by
  by_contra hn
  let A := (normalizer (L : Set G)).subgroupOf (T : Subgroup G)
  have hi : A.index = 2 :=
    source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 (selected_nonnormal s)
  have hmul : g * s.exchange⁻¹ ∈ normalizer (L : Set G) := by
    have hh := (mul_mem_iff_of_index_two hi
      (a := (⟨g,hg⟩ : (T : Subgroup G)))
      (b := (⟨s.exchange,s.exchange_mem⟩ : (T : Subgroup G))⁻¹)).mpr
      (iff_of_false hn (by change s.exchange⁻¹ ∉ normalizer (L : Set G); simpa only [inv_mem_iff] using s.exchange_moves))
    exact hh
  let g' : localJoin T L := ⟨g,(show (T : Subgroup G) ≤ localJoin T L from le_sup_right) hg⟩
  have hh := f.right_eq_one_of_normalizes (g' * (exchanger s)⁻¹) hmul
  rw [map_mul,map_inv,RegularWreathProduct.mul_right,RegularWreathProduct.inv_right,
    show (f.hom g').right = 1 from he,f.exchanger_right,other_inv,one_mul] at hh
  exact other_ne_one hh

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
