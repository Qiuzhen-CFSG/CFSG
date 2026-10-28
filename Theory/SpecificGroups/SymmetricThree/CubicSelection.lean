module
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Cubic selection for an elementary actor in S₃

The alternating subgroup A₃ is exactly O²(S₃). A nontrivial elementary
abelian two-subgroup A has order two, acts on A₃ with [A₃,A]=A₃, and generates
S₃ together with A₃. Thus R=1 and L=A₃ satisfy the index-two selection for
any prescribed overgroup of A. The same data transport through a specified
S₃ group equivalence, retaining the original actor and overgroup.

The three elementary permutation calculations range over just six elements;
all transport, residual identification, and generation use subgroup APIs.
Source: Aschbacher–Smith, 3.1.9(5) and 15.1.12(3–4), pp.577–578,1090.
-/

public section
open Subgroup Equiv
open scoped commutatorElement IsMulCommutative
namespace Theory.SpecificGroups.SymmetricThree.CubicSelection
abbrev Sym := Perm (Fin 3)

/-- The canonical selected cubic is precisely the two-residual of S₃. -/
theorem residual_eq : pResidual 2 Sym = alternatingGroup (Fin 3) := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    change (alternatingGroup (Fin 3)).index = 2 ^ 1
    simp
  · intro x hx
    have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      rfl
    have hp : x ^ 3 = 1 := congrArg Subtype.val
      (hc ▸ pow_card_eq_one' (x := (⟨x, hx⟩ : alternatingGroup (Fin 3))))
    exact mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hp))

theorem residual_card : Nat.card (pResidual 2 Sym) = 3 := by
  rw [residual_eq,nat_card_alternatingGroup,Nat.card_fin]
  rfl

/-- A nontrivial elementary two-subgroup of S₃ is a transposition subgroup;
the normal cubic is its commutator and generates S₃ with it. -/
theorem elementary_selection (S A : Subgroup Sym) [IsElementaryAbelian 2 A]
    (hne : A ≠ ⊥) (hAS : A ≤ S) :
    Nat.card A=2 ∧ alternatingGroup (Fin 3)=⁅alternatingGroup (Fin 3),A⁆ ∧
      alternatingGroup (Fin 3) ⊔ S=⊤ := by
  obtain ⟨⟨a,ha⟩,hane'⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hane : a≠1 := fun h => hane' (Subtype.ext h)
  have hp : a^2=1 := elemPow_eq_one_of_isElementaryAbelian a ha
  have hc : ∀ a : Sym, a^2=1 → a≠1 → ∀ b : Sym, b*a=a*b → b=1 ∨ b=a := by
    decide +kernel
  have hcard : Nat.card A=2 := by
    apply (Nat.card_eq_two_iff' (1 : A)).mpr
    refine ⟨⟨a,ha⟩,?_,?_⟩
    · intro h
      exact hane (congrArg Subtype.val h)
    · intro b hb
      have hh := congrArg Subtype.val (mul_comm' b (⟨a,ha⟩ : A))
      rcases hc a hp hane b hh with he | he
      · exact (hb (Subtype.ext he)).elim
      · exact Subtype.ext he
  refine ⟨hcard,?_,?_⟩
  · apply le_antisymm ?_ (le_normalizer_iff_commutator_le_left.mp le_normalizer_of_normal)
    have hcomm : ∀ a : Sym, a^2=1 → a≠1 → ∀ x : Sym,
        x∈alternatingGroup (Fin 3) →
        ∃ y : Sym, y∈alternatingGroup (Fin 3) ∧ ⁅y,a⁆=x := by
      change ∀ a : Sym, a^2=1 → a≠1 → ∀ x : Sym, x.sign=1 →
        ∃ y : Sym, y.sign=1 ∧ ⁅y,a⁆=x
      decide +kernel
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hcomm a hp hane x hx
    exact commutator_mem_commutator hy ha
  · apply top_unique
    intro x _
    have hgen : ∀ a : Sym, a^2=1 → a≠1 → ∀ x : Sym,
        x∈alternatingGroup (Fin 3) ∨ ∃ y : Sym, y∈alternatingGroup (Fin 3) ∧ x=y*a := by
      change ∀ a : Sym, a^2=1 → a≠1 → ∀ x : Sym,
        x.sign=1 ∨ ∃ y : Sym, y.sign=1 ∧ x=y*a
      decide +kernel
    rcases hgen a hp hane x with hx | ⟨y,hy,rfl⟩
    · exact mem_sup_left hx
    · exact mul_mem (mem_sup_left hy) (mem_sup_right (hAS ha))

/-- The same selected cubic transported through the specified S₃ coordinates. -/
theorem exists_selection_of_equiv {G : Type*} [Group G]
    (e : G ≃* Sym) (S A : Subgroup G) [IsElementaryAbelian 2 A]
    (hne : A≠⊥) (hAS : A≤S) :
    ∃ L R : Subgroup G, Nat.card L=3 ∧ R ≤ A ∧ R.relIndex A=2 ∧
      A ≤ normalizer (R : Set G) ∧ L ≤ centralizer (R : Set G) ∧
      A ≤ normalizer (L : Set G) ∧ L=⁅L,A⁆ ∧ L ⊔ S=⊤ := by
  let B := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map e.toMonoidHom
  have hBne : B≠⊥ := by
    intro h
    apply hne
    apply map_injective (f := e.toMonoidHom) e.injective
    simpa only [Subgroup.map_bot] using h
  obtain ⟨hcard,hcomm,hgen⟩ := elementary_selection (S.map e.toMonoidHom) B hBne (map_mono hAS)
  have hAe : B.map e.symm.toMonoidHom=A := by
    change (A.map e.toMonoidHom).map e.symm.toMonoidHom=A
    rw [map_map]; simp
  have hSe : (S.map e.toMonoidHom).map e.symm.toMonoidHom=S := by
    rw [map_map]; simp
  refine ⟨(alternatingGroup (Fin 3)).map e.symm.toMonoidHom,⊥,?_,bot_le,?_,?_,?_,?_,?_,?_⟩
  · rw [card_map_of_injective e.symm.injective,nat_card_alternatingGroup,Nat.card_fin]
    rfl
  · rw [relIndex_bot_left]
    have hh : Nat.card B=Nat.card A := card_map_of_injective e.injective
    exact hh ▸ hcard
  · exact le_normalizer_of_normal
  · intro x hx y hy
    have hy1 : y = 1 := hy
    simp [hy1]
  · have hh := map_mono (f := e.symm.toMonoidHom)
      (show B ≤ normalizer (alternatingGroup (Fin 3) : Set Sym) from le_normalizer_of_normal)
    rwa [hAe,map_equiv_normalizer_eq] at hh
  · have hh := congrArg (map e.symm.toMonoidHom) hcomm
    rwa [map_commutator,hAe] at hh
  · rw [←hSe,←Subgroup.map_sup,hgen,map_top_of_surjective _ e.symm.surjective]

end Theory.SpecificGroups.SymmetricThree.CubicSelection
