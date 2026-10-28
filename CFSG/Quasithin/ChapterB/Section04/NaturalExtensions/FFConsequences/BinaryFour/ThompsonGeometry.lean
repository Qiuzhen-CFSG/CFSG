module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.DoubleNatural
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FixedSpaces
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.SmallFields
public import Theory.Representation.BinaryNaturalDual.FourActors.PermutationCatalogue.ElementaryThompson
public import Stellmacher.ElementaryAbelianMaxJ

/-!
# The literal Thompson subgroup for a binary four-dimensional natural action

Prime-field transport and the genuine SL₄(2)–GL₄(2)–A₈ comparisons carry the
original actors into the eight-point model. Sylow placement in the binary-tree
group lets the elementary catalogue bound every actor by order sixteen and
identify any two actors of that order in a common two-subgroup.

The source elementary Thompson supremum is therefore the original dual
best offender. The two-factor budget then gives rank four, quadraticity and
quadratic ratio one, without a splitting premise.
Source: Aschbacher–Smith B.4.9(2)(iii), combined manuscript of 1 March 2004,
printed pp.92,94; Thompson convention in section 0.6.1, printed p.8.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions
open QuasisimpleSource
namespace BinaryFourGeometry
open BinaryNaturalDual.FourActors BinaryNaturalDual.FourActors.PermutationCatalogue
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals

private theorem place_two_subgroup {H : Type*} [Group H]
    (e : H ≃* alternatingGroup (Fin 8)) (P : Subgroup H) (hP : IsPGroup 2 P) :
    ∃ e' : H ≃* alternatingGroup (Fin 8),
      P.map ((alternatingGroup (Fin 8)).subtype.comp e'.toMonoidHom) ≤
        treeGroup ⊓ alternatingGroup (Fin 8) := by
  let f := (alternatingGroup (Fin 8)).subtype.comp e.toMonoidHom
  obtain ⟨Q, hQ⟩ := (hP.map f).exists_le_sylow
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq S Q treeSylow
  let e' := e.trans (MulAut.conjNormal q)
  refine ⟨e', ?_⟩
  rintro x ⟨y, hy, rfl⟩
  refine ⟨?_, (e' y).property⟩
  have hq' : (Q : Subgroup S).map (MulAut.conj q).toMonoidHom = treeGroup :=
    congrArg Sylow.toSubgroup hq
  rw [← hq']
  exact ⟨f y, hQ (Subgroup.mem_map_of_mem f hy), rfl⟩

/-- The elementary rank bound is transported along a genuine A₈ comparison. -/
private theorem elementary_card_le {H : Type*} [Group H]
    (e : H ≃* alternatingGroup (Fin 8)) (A : Subgroup H) [IsElementaryAbelian 2 A] :
    Nat.card A ≤ 16 := by
  obtain ⟨e', he'⟩ := place_two_subgroup e A (IsElementaryAbelian.isPGroup 2 A)
  let f := (alternatingGroup (Fin 8)).subtype.comp e'.toMonoidHom
  have hf : Function.Injective f := Subtype.coe_injective.comp e'.injective
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hc := permutation_even_tree_card_le (A.map f) he'
  rwa [Subgroup.card_map_of_injective hf] at hc

/-- Two elementary subgroups of order sixteen in a common two-subgroup agree. -/
private theorem elementary_eq_of_card_ge {H : Type*} [Group H]
    (e : H ≃* alternatingGroup (Fin 8)) (P A B : Subgroup H)
    (hP : IsPGroup 2 P) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hAP : A ≤ P) (hBP : B ≤ P) (hA : 16 ≤ Nat.card A) (hB : 16 ≤ Nat.card B) : A = B := by
  obtain ⟨e', he'⟩ := place_two_subgroup e P hP
  let f := (alternatingGroup (Fin 8)).subtype.comp e'.toMonoidHom
  have hf : Function.Injective f := Subtype.coe_injective.comp e'.injective
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  let : IsElementaryAbelian 2 (B.map f) := IsElementaryAbelian.map f
  have hA' : A.map f = permutationA0 :=
    permutation_even_tree_eq_A0_of_card_ge _ ((Subgroup.map_mono hAP).trans he')
      (by rwa [Subgroup.card_map_of_injective hf])
  have hB' : B.map f = permutationA0 :=
    permutation_even_tree_eq_A0_of_card_ge _ ((Subgroup.map_mono hBP).trans he')
      (by rwa [Subgroup.card_map_of_injective hf])
  exact Subgroup.map_injective hf (hA'.trans hB'.symm)

/-- The source elementary Thompson subgroup is literal in the original ambient group. -/
private theorem elementary_thompson_eq {H : Type*} [Group H]
    (e : H ≃* alternatingGroup (Fin 8)) (P A : Subgroup H)
    (hP : IsPGroup 2 P) [IsElementaryAbelian 2 A]
    (hAP : A ≤ P) (hA : Nat.card A = 16) : Stellmacher.elementaryAbelianMaxJ P = A := by
  have he : Stellmacher.elementaryAbelianMaxSubgroups P = {A} := by
    ext B
    change (B ≤ P ∧ IsElementaryAbelian 2 B ∧
      ∀ C : Subgroup H, C ≤ P → IsElementaryAbelian 2 C → Nat.card C ≤ Nat.card B) ↔ B = A
    constructor
    · rintro ⟨hBP, hb, hm⟩
      let := hb
      apply elementary_eq_of_card_ge e P B A hP hBP hAP
      · simpa only [hA] using hm A hAP inferInstance
      · exact hA.ge
    · rintro rfl
      refine ⟨hAP, inferInstance, ?_⟩
      intro B hBP hb
      let := hb
      rw [hA]
      exact elementary_card_le e B
  rw [Stellmacher.elementaryAbelianMaxJ, he, sSup_singleton]
end BinaryFourGeometry

namespace DoubleNatural
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {F : BinaryField} {ρ : Representation (ZMod 2) G V}
  (d : DoubleNatural F 4 ρ)

/-- The natural marking over an arbitrary degree-one carrier, with the original actors. -/
noncomputable def binary_four_marking (hF : F.degree = 1) :
    ActionEquiv d.space.toRepresentation (linearNatural BinaryField.two 4) := by
  let eTop : ActionEquiv (d.space.toRepresentation.comp (⊤ : Subgroup G).subtype)
      (linearNatural F 4) :=
    ⟨Subgroup.topEquiv.trans d.natural.groupEquiv, d.natural.linearEquiv,
      fun g v => d.natural.intertwines g v⟩
  let e := ChapterK.Linear.Natural.primeFieldActionEquiv d.space.toRepresentation ⊤ F hF 4 eTop
  exact ⟨Subgroup.topEquiv.symm.trans e.groupEquiv, e.linearEquiv,
    fun g v => e.intertwines ⟨g, Subgroup.mem_top g⟩ v⟩

/-- The exceptional comparison is composed with the marked natural action. -/
noncomputable def binary_four_alternatingEquiv (hF : F.degree = 1) :
    G ≃* alternatingGroup (Fin 8) :=
  (d.binary_four_marking hF).groupEquiv |>.trans (BinaryLinear.OuterCyclic.slEquivLinear 4)
    |>.trans BinaryNaturalDual.FourActors.linearAlternatingEquiv

omit [FiniteDimensional (ZMod 2) V] in
include d in
/-- Every elementary actor in the original group has rank at most four. -/
theorem binary_four_rank_le (hF : F.degree = 1) {A : Subgroup G}
    (hA : IsElementaryTwo A) : rank A ≤ 4 := by
  let : Finite G := Finite.of_injective d.natural.groupEquiv d.natural.groupEquiv.injective
  let : IsElementaryAbelian 2 A := hA.2
  have hc := BinaryFourGeometry.elementary_card_le (d.binary_four_alternatingEquiv hF) A
  rw [hA.card_eq_two_pow_rank] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

/-- B.4.9(2)(iii), including the elementary Thompson convention and the original Sylow inclusion. -/
theorem binary_four_dual_geometry (hF : F.degree = 1)
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    (T : Sylow 2 G) {A : Subgroup G} (hAT : A ≤ (T : Subgroup G))
    (hA : IsBestOffender ρ A) :
    A = Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ∧ rank A = 4 ∧
      quadraticRatio ρ = 1 ∧ IsQuadratic ρ A := by
  let : Finite G := Finite.of_injective d.natural.groupEquiv d.natural.groupEquiv.injective
  have hff : IsFFModule ρ := ⟨A, hA.isOffender ρ⟩
  have hr : rank A = 4 := le_antisymm (d.binary_four_rank_le hF hA.1)
    (d.dual_offender_bounds e (hA.isOffender ρ)).2.2
  let : IsElementaryAbelian 2 A := hA.1.2
  refine ⟨?_, hr, ?_, d.dual_rank_four_quadratic e hA hr⟩
  · exact (BinaryFourGeometry.elementary_thompson_eq (d.binary_four_alternatingEquiv hF)
      (T : Subgroup G) A T.isPGroup' hAT (by rw [hA.1.card_eq_two_pow_rank, hr]; rfl)).symm
  · exact d.dual_ratio_one_of_rank_bound e (fun B hB => (d.binary_four_rank_le hF hB).trans
      (by decide)) hff
end DoubleNatural
end CFSG.Quasithin.ChapterB.NaturalExtensions
