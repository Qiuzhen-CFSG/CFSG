module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionCentralizerStructure
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourcePrime
public import Theory.Representation.BinaryOffender.QuadraticHomogeneousOrbit

/-!
# The three-core branch of the cubic centralizer argument

A displacement of dimension at most two commuting with a perfect component
is a trivial component module. If the component generates the whole module
by commutators, equivariance makes the displacement zero. Thus a rank-one
starred cubic actor is faithful on the component.

For a nontrivial component centralizer, apply D.2.13 to the same starred actor
and the ambient prime core containing the selected odd-prime subgroup. Only
three and five can occur, and five would force actor rank one. The preceding
argument excludes it. The resulting nontrivial A-invariant X in C_H(K) satisfies
X = [X,C_A(K)] and is a three-subgroup or a literal A-orbit of a component.

`SeedAlternativesMovedExhaustionCentralizerStructure` supplies full movement
from the original chosen seed. Suzuki exclusion, order three for the selected
three-group, D.3.13--18 and Source325 assembly remain with qt-baumann-fsu.
No simple quotient replaces the original component's central cover.
Source: Aschbacher--Smith, D.2.13 and D.3.9(2), printed pp.184--185 and200--201.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterD
variable {H E : Type*} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

omit [Finite H] in
/-- A displacement of dimension at most two commuting with a perfect actor
is zero when that actor generates the whole module by commutators. -/
theorem centralizing_small_displacement_eq_one
    (ρ : Representation (ZMod 2) H E) (hf : Function.Injective ρ)
    (K : Subgroup H) [Group.IsPerfect K]
    (hfull : subspaceCommutator ρ ⊤ K = ⊤) (a : H)
    (hac : a ∈ centralizer (K : Set H))
    (hd : Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) ≤ 2) : a = 1 := by
  let f : E →ₗ[ZMod 2] E := ρ a - 1
  let I := LinearMap.range f
  have hcomm (k : K) (v : E) : ρ k.val (f v) = f (ρ k.val v) := by
    change ρ k.val (ρ a v - v) = ρ a (ρ k.val v) - ρ k.val v
    rw [map_sub,←Module.End.mul_apply,←map_mul, hac k.val k.property,
      map_mul,Module.End.mul_apply]
  have hs : K ≤ subspaceStabilizer ρ I := by
    apply le_subspaceStabilizer
    rintro k hk _ ⟨v,rfl⟩
    exact ⟨ρ k v,(hcomm ⟨k,hk⟩ v).symm⟩
  have hfix (k : K) (v : E) : ρ k.val (f v) = f v :=
    congrArg (fun z => (z (⟨f v,LinearMap.mem_range_self f v⟩ : I) : E))
      (representation_eq_one_of_isPerfect_of_finrank_le_two
        (invariantSubspace ρ K I hs).toRepresentation hd k)
  have hker : subspaceCommutator ρ ⊤ K ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,v,_,rfl⟩
    change f (ρ k v - v) = 0
    rw [map_sub,←hcomm ⟨k,hk⟩ v,hfix ⟨k,hk⟩ v,sub_self]
  have hz : f = 0 := LinearMap.ker_eq_top.mp (top_unique (hfull ▸ hker))
  apply hf
  rw [map_one]
  exact sub_eq_zero.mp hz

/-- A rank-one cubic actor is faithful on a perfect component that moves
the whole module. In particular a nontrivial component centralizer forces
rank greater than one, eliminating the five-core case of D.2.13. -/
theorem rank_one_starred_component_centralizer_eq_bot
    (ρ : Representation (ZMod 2) H E) (hf : Function.Injective ρ)
    (K : Subgroup H) [Group.IsPerfect K]
    (hfull : subspaceCommutator ρ ⊤ K = ⊤)
    {A : Subgroup H} (hA : A ∈ QhatStar ρ) (hr : rank A = 1) :
    A ⊓ centralizer (K : Set H) = ⊥ := by
  have hb := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hA.1.1)
  rw [hr,mul_one] at hb
  apply bot_unique
  intro a ha
  apply centralizing_small_displacement_eq_one ρ hf K hfull a ha.2
  change Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 2
  rw [←fixedCodim_zpowers_eq_displacement_rank]
  have hm := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr ha.1))
  have hz := fixedCodim_add_finrank ρ (zpowers a)
  have hA' := fixedCodim_add_finrank ρ A
  omega

/-- The original starred condition and full component movement remove every
odd prime except three. The selected component orbit is retained literally;
Suzuki exclusion and order three for the three-group are later source steps. -/
theorem exists_starred_moved_subgroup_in_component_centralizer
    (ρ : Representation (ZMod 2) H E) (hf : Function.Injective ρ)
    (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (hcore : pCore 2 H = ⊥) (hfull : subspaceCommutator ρ ⊤ K = ⊤)
    {A : Subgroup H} (hA : A ∈ QhatStar ρ)
    (hBn : A ⊓ centralizer (K : Set H) ≠ ⊥) :
    let C := centralizer (K : Set H)
    ∃ X : Subgroup H, X ≤ C ∧ A ≤ normalizer (X : Set H) ∧ X ≠ ⊥ ∧
      ⁅X,A ⊓ C⁆ = X ∧
      ((X ≤ (pCore 3 C).map C.subtype ∧ IsPGroup 3 X) ∨
        ∃ J : Subgroup H, IsComponent H J ∧ J ≤ C ∧ X = componentOrbit J A) := by
  let C := centralizer (K : Set H)
  let B := A ⊓ C
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hAB : A ≤ normalizer (B : Set H) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨b,hb.1⟩ : A) ⟨a,ha⟩)
  obtain ⟨X,hXC,hn,hXn,hXB,hcase⟩ := exists_moved_subgroup_in_component_centralizer
    K hcore A B ((IsElementaryAbelian.isPGroup 2 A).to_le inf_le_left)
    hBn inf_le_left hAB inf_le_right
  refine ⟨X,hXC,hn,hXn,hXB,?_⟩
  rcases hcase with ⟨p,hp,ho,hXP,hXp⟩ | hcomp
  · let : Fact p.Prime := ⟨hp⟩
    have hP : (pCore p C).map C.subtype ≤ pCore p H :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map C.subtype⟩
    have hm : ⁅pCore p H,A⁆ ≠ ⊥ := by
      intro hz
      apply hXn
      apply bot_unique
      rw [←hXB]
      exact (commutator_mono (hXP.trans hP) inf_le_left).trans hz.le
    have hp35 := ChapterD.source_lemma_D_2_13_one_two ρ hf hA ho hm
    rcases hp35.1 with rfl | hp5
    · exact Or.inl ⟨hXP,hXp⟩
    · have hr := (hp35.2 hp5).2.1
      exact (hBn (rank_one_starred_component_centralizer_eq_bot ρ hf K hfull hA hr)).elim
  · exact Or.inr hcomp

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
