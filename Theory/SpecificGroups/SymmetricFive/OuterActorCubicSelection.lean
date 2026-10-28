module
public import Theory.SpecificGroups.SymmetricFive.CubicSelection
import all Theory.SpecificGroups.SymmetricFive.CubicSelection
/-!
# Cubic selection for an elementary outer actor in S₅

An elementary two-subgroup containing an odd permutation can be marked inside
its prescribed Sylow subgroup so that it contains (01) and lies in
⟨(01),(23)⟩. The cubic on {0,1,4} is inverted by the active transposition.
The inactive part of the actor centralizes it and has index two. This cubic
and the prescribed Sylow generate all of S₅, because the cubic moves the
Sylow's fixed letter. All conclusions transport through the specified action.

The finite checks use the existing four- and eight-element word tables.
Source: Aschbacher–Smith, proof of 3.1.9(5) and 15.1.12(4), together with
B.3.2's natural-module offender classification.
-/
public section
open Subgroup Equiv
open scoped commutatorElement
namespace Theory.SpecificGroups.SymmetricFive.CubicSelection
open OuterFourGeometry

private theorem mem_centralizer_cubic_iff (x : Sym) :
    x ∈ centralizer (cubic : Set Sym) ↔ cycle * x = x * cycle := by
  constructor
  · intro h
    exact mem_centralizer_iff.mp h cycle cycle_mem
  · intro h
    rw [mem_centralizer_iff]
    rintro y ⟨i,rfl⟩
    fin_cases i
    · simp [word]
    · exact h
    · exact (Commute.pow_left h 2).eq

/-- The inactive part of any positioned outer actor has index two and
centralizes the selected cubic. -/
theorem positioned_selection (A : Subgroup Sym) (hA : A ≤ four)
    (ha : swap (0 : Fin 5) 1 ∈ A) :
    ∃ R : Subgroup Sym, R ≤ A ∧ R.relIndex A = 2 ∧
      A ≤ normalizer (R : Set Sym) ∧ cubic ≤ centralizer (R : Set Sym) ∧
      A ≤ normalizer (cubic : Set Sym) ∧ cubic = ⁅cubic,A⁆ := by
  let R := A ⊓ centralizer (cubic : Set Sym)
  have hRA : R ≤ A := inf_le_left
  refine ⟨R,hRA,?_,?_,le_centralizer_iff.mp inf_le_right,
    hA.trans four_normalizes_cubic,?_⟩
  · apply relIndex_eq_two_iff.mpr
    refine ⟨swap 0 1,ha,?_⟩
    intro b hb
    have hc : ∀ i : Fin 4,
        Xor (cycle * (fourWord i * swap 0 1) = (fourWord i * swap 0 1) * cycle)
          (cycle * fourWord i = fourWord i * cycle) := by decide +kernel
    obtain ⟨i,hi⟩ := hA hb
    change Xor (_ ∈ A ∧ _ ∈ centralizer (cubic : Set Sym))
      (_ ∈ A ∧ _ ∈ centralizer (cubic : Set Sym))
    have hc' := hc i
    rw [hi] at hc'
    simpa only [A.mul_mem hb ha,hb,true_and,mem_centralizer_cubic_iff] using hc'
  · intro a ha'
    apply mem_normalizer_iff.mpr
    intro r
    have he : ∀ x ∈ A, a*x*a⁻¹=x := by
      intro x hx
      have hcomm := congrArg Subtype.val
        (mul_comm' (⟨a,hA ha'⟩ : four) ⟨x,hA hx⟩)
      change a*x=x*a at hcomm
      rw [hcomm,mul_inv_cancel_right]
    constructor
    · intro hr
      rwa [he r (hRA hr)]
    · intro hr
      have har : a*r*a⁻¹ ∈ A := hRA hr
      have hrA : r ∈ A := by
        have hm := A.mul_mem (A.mul_mem (A.inv_mem ha') har) ha'
        simpa [mul_assoc] using hm
      rwa [he r hrA] at hr
  · apply le_antisymm ?_ (le_normalizer_iff_commutator_le_left.mp
      (hA.trans four_normalizes_cubic))
    have he : ⁅cycle^2,swap (0 : Fin 5) 1⁆=cycle := by decide +kernel
    have hc : cycle∈⁅cubic,A⁆ := he ▸ commutator_mem_commutator (cubic.pow_mem cycle_mem 2) ha
    rintro g ⟨i,rfl⟩
    fin_cases i
    · exact one_mem _
    · exact hc
    · exact pow_mem hc 2

/-- Mark an elementary outer actor inside its prescribed Sylow subgroup. -/
theorem exists_outer_actor_marking (S : Sylow 2 Sym) (A : Subgroup Sym)
    [IsElementaryAbelian 2 A] (hAS : A ≤ (S : Subgroup Sym))
    (hout : ¬ A ≤ alternatingGroup (Fin 5)) :
    ∃ e : Sym ≃* Sym, (S : Subgroup Sym).map e.toMonoidHom = eight ∧
      A.map e.toMonoidHom ≤ four ∧ swap (0 : Fin 5) 1 ∈ A.map e.toMonoidHom := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Sym S standardSylow
  let e := MulAut.conj g
  have hS : (S : Subgroup Sym).map e.toMonoidHom = eight :=
    congrArg (fun Q : Sylow 2 Sym => (Q : Subgroup Sym)) hg
  let B := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map e.toMonoidHom
  have hBS : B ≤ eight := hS ▸ map_mono hAS
  obtain ⟨x,hx,hxout⟩ := Set.not_subset.mp hout
  have hxB : e x ∈ B := mem_map_of_mem e.toMonoidHom hx
  have hsign : (e x).sign ≠ 1 := by
    intro h
    apply hxout
    apply Perm.mem_alternatingGroup.mpr
    change (g*x*g⁻¹).sign=1 at h
    simpa only [map_mul,map_inv,mul_comm (Perm.sign g) (Perm.sign x),
      mul_inv_cancel_right] using h
  obtain ⟨i,hi⟩ := hBS hxB
  have hp : (OuterFourGeometry.word i)^2=1 :=
    hi ▸ elemPow_eq_one_of_isElementaryAbelian (e x) hxB
  have hs : (OuterFourGeometry.word i).sign ≠ 1 := hi ▸ hsign
  have hB : B ≤ four := by
    have hc : ∀ i j, (OuterFourGeometry.word i)^2=1 →
        (OuterFourGeometry.word i).sign ≠ 1 →
        OuterFourGeometry.word j * OuterFourGeometry.word i =
          OuterFourGeometry.word i * OuterFourGeometry.word j →
        ∃ k, fourWord k=OuterFourGeometry.word j := by decide +kernel
    intro y hy
    obtain ⟨j,hj⟩ := hBS hy
    have hcomm := congrArg Subtype.val (mul_comm' (⟨y,hy⟩ : B) ⟨e x,hxB⟩)
    change y*e x=e x*y at hcomm
    obtain ⟨k,hk⟩ := hc i j hp hs (by simpa only [hi,hj] using hcomm)
    exact ⟨k,hk.trans hj⟩
  have hc : ∀ i, (OuterFourGeometry.word i)^2=1 →
      (OuterFourGeometry.word i).sign ≠ 1 →
      OuterFourGeometry.word i=swap 0 1 ∨ OuterFourGeometry.word i=swap 2 3 := by
    decide +kernel
  rcases hc i hp hs with ha | hb
  · exact ⟨e,hS,hB,(hi.symm.trans ha) ▸ hxB⟩
  · let c : Sym := swap 0 2 * swap 1 3
    let d := MulAut.conj c
    have hceight : c∈eight := ⟨4,rfl⟩
    have hdeight : eight.map d.toMonoidHom=eight :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer hceight)
    have hdfour : four.map d.toMonoidHom=four := by
      apply eq_of_le_of_card_ge
      · rintro _ ⟨y,⟨j,rfl⟩,rfl⟩
        have hh : ∀ j, ∃ k, fourWord k=d (fourWord j) := by decide +kernel
        exact hh j
      · rw [card_map_of_injective d.injective]
    refine ⟨e.trans d,?_,?_,?_⟩
    · change (S : Subgroup Sym).map (d.toMonoidHom.comp e.toMonoidHom)=eight
      rw [←map_map,hS,hdeight]
    · change A.map (d.toMonoidHom.comp e.toMonoidHom)≤four
      rw [←map_map]
      exact (map_mono hB).trans_eq hdfour
    · have hbB : swap (2 : Fin 5) 3 ∈ B := (hi.symm.trans hb) ▸ hxB
      have hd : d (swap 2 3)=swap 0 1 := by decide +kernel
      change swap (0 : Fin 5) 1 ∈ A.map (d.toMonoidHom.comp e.toMonoidHom)
      rw [←map_map,←hd]
      exact mem_map_of_mem d.toMonoidHom hbB

/-- A selected cubic and the index-two inactive part of the same elementary
actor, retaining the prescribed Sylow subgroup. -/
theorem exists_outer_actor_selection (S : Sylow 2 Sym) (A : Subgroup Sym)
    [IsElementaryAbelian 2 A] (hAS : A ≤ (S : Subgroup Sym))
    (hout : ¬ A ≤ alternatingGroup (Fin 5)) :
    ∃ L R : Subgroup Sym, Nat.card L=3 ∧ L ≤ alternatingGroup (Fin 5) ∧
      R ≤ A ∧ R.relIndex A=2 ∧ A ≤ normalizer (R : Set Sym) ∧
      L ≤ centralizer (R : Set Sym) ∧ A ≤ normalizer (L : Set Sym) ∧
      L=⁅L,A⁆ ∧ L ⊔ (S : Subgroup Sym)=⊤ := by
  obtain ⟨e,hS,hA,ha⟩ := exists_outer_actor_marking S A hAS hout
  obtain ⟨R,hRA,hi,hnR,hc,hnL,hcom⟩ := positioned_selection _ hA ha
  have hAe : (A.map e.toMonoidHom).map e.symm.toMonoidHom=A := by
    rw [map_map]; simp
  have hSe : eight.map e.symm.toMonoidHom=(S : Subgroup Sym) := by
    rw [←hS,map_map]; simp
  refine ⟨cubic.map e.symm.toMonoidHom,R.map e.symm.toMonoidHom,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [card_map_of_injective e.symm.injective,cubic_card]
  · exact (map_mono cubic_le_alternating).trans_eq
      (characteristic_iff_map_eq.mp inferInstance e.symm)
  · exact (map_mono hRA).trans_eq hAe
  · rw [←hAe,relIndex_map_map_of_injective _ _ e.symm.injective]
    exact hi
  · have hh := map_mono (f := e.symm.toMonoidHom) hnR
    rwa [hAe,map_equiv_normalizer_eq] at hh
  · rintro _ ⟨x,hx,rfl⟩
    apply mem_centralizer_iff.mpr
    rintro _ ⟨y,hy,rfl⟩
    simpa only [map_mul,MulEquiv.coe_toMonoidHom] using congrArg e.symm (mem_centralizer_iff.mp (hc hx) y hy)
  · have hh := map_mono (f := e.symm.toMonoidHom) hnL
    rwa [hAe,map_equiv_normalizer_eq] at hh
  · have hh := congrArg (map e.symm.toMonoidHom) hcom
    rwa [map_commutator,hAe] at hh
  · rw [←hSe,←Subgroup.map_sup,cubic_sup_eight,map_top_of_surjective _ e.symm.surjective]

/-- Transport the cubic selection through a specified five-point action. -/
theorem exists_outer_actor_selection_of_equiv {G : Type*} [Group G] [Finite G]
    (e : G ≃* Sym) (S : Sylow 2 G) (A : Subgroup G)
    [IsElementaryAbelian 2 A] (hAS : A ≤ (S : Subgroup G))
    (hout : ¬ A.map e.toMonoidHom ≤ alternatingGroup (Fin 5)) :
    ∃ L R : Subgroup G, Nat.card L=3 ∧ R ≤ A ∧ R.relIndex A=2 ∧
      A ≤ normalizer (R : Set G) ∧ L ≤ centralizer (R : Set G) ∧
      A ≤ normalizer (L : Set G) ∧ L=⁅L,A⁆ ∧ L ⊔ (S : Subgroup G)=⊤ := by
  let B := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map e.toMonoidHom
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨L,R,hcard,_,hRA,hi,hnR,hc,hnL,hcom,hgen⟩ :=
    exists_outer_actor_selection S' B (map_mono hAS) hout
  have hAe : B.map e.symm.toMonoidHom=A := by
    change (A.map e.toMonoidHom).map e.symm.toMonoidHom=A
    rw [map_map]; simp
  have hSe : (S' : Subgroup Sym).map e.symm.toMonoidHom=(S : Subgroup G) := by
    change ((S : Subgroup G).map e.toMonoidHom).map e.symm.toMonoidHom=_
    rw [map_map]; simp
  refine ⟨L.map e.symm.toMonoidHom,R.map e.symm.toMonoidHom,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [card_map_of_injective e.symm.injective,hcard]
  · exact (map_mono hRA).trans_eq hAe
  · rw [←hAe,relIndex_map_map_of_injective _ _ e.symm.injective]
    exact hi
  · have hh := map_mono (f := e.symm.toMonoidHom) hnR
    rwa [hAe,map_equiv_normalizer_eq] at hh
  · rintro _ ⟨x,hx,rfl⟩
    apply mem_centralizer_iff.mpr
    rintro _ ⟨y,hy,rfl⟩
    simpa only [map_mul,MulEquiv.coe_toMonoidHom] using
      congrArg e.symm (mem_centralizer_iff.mp (hc hx) y hy)
  · have hh := map_mono (f := e.symm.toMonoidHom) hnL
    rwa [hAe,map_equiv_normalizer_eq] at hh
  · have hh := congrArg (map e.symm.toMonoidHom) hcom
    rwa [map_commutator,hAe] at hh
  · rw [←hSe,←Subgroup.map_sup,hgen,map_top_of_surjective _ e.symm.surjective]

end Theory.SpecificGroups.SymmetricFive.CubicSelection
