module
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Choices
public import Theory.Representation.BinaryOffender.PermutedSupports
public import Theory.Representation.SL2NaturalOffenders.Internal
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Fixed lines in the original solvable natural factors

A Sylow two-subgroup of the offender product preserves each natural plane.
The two-group fixed-point theorem supplies a nonzero fixed vector there.
Its intersection with the corresponding normal S₃ factor is nontrivial,
and a nonidentity natural matrix has at most two fixed vectors. Thus the
fixed part of each original support has order two; independence of the
supports makes these lines pairwise disjoint.

The consumer is the original Eᵢ=C_{Uᵢ}(Baum(T)) in Aschbacher–Smith
E.2.3 and13.2.8(6),13.2.11(3), printed pp.216–217,880–881.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (c : SolvableFFFactors ρ)

noncomputable def factorFixedSpace (A : Subgroup G) (i : Fin c.count) : Submodule (ZMod 2) V :=
  subspaceCommutator ρ ⊤ (c.factor i) ⊓ fixedSpace ρ A

theorem factorFixedSpace_disjoint (A : Subgroup G) {i j : Fin c.count} (hij : i ≠ j) :
    Disjoint (c.factorFixedSpace A i) (c.factorFixedSpace A j) :=
  (c.supports_independent.pairwiseDisjoint hij).mono inf_le_left inf_le_left

theorem factorFixedSpace_card [Finite G] [FiniteDimensional (ZMod 2) V]
    (P : Sylow 2 (offenderSubgroup ρ)) (i : Fin c.count) :
    Nat.card (c.factorFixedSpace ((P : Subgroup (offenderSubgroup ρ)).map
      (offenderSubgroup ρ).subtype) i) = 2 := by
  let O := offenderSubgroup ρ
  let A := (P : Subgroup O).map O.subtype
  let W := subspaceCommutator ρ ⊤ (c.factor i)
  let E := c.factorFixedSpace A i
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hA : A ≤ O := map_subtype_le _
  obtain ⟨v,hv,hv0,hvf⟩ := PermutedSupports.exists_nonzero_fixed ρ A
    (P.isPGroup'.map O.subtype) W (c.support_ne_bot i)
    (hA.trans (c.offenderSubgroup_le_support_stabilizer i))
  have hlow : 2 ≤ Nat.card E := by
    let : Nontrivial E := ⟨⟨⟨v,hv,hvf⟩,0,fun he => hv0 (congrArg Subtype.val he)⟩⟩
    by_contra! hn
    have he : Nat.card E = 1 := by have := Nat.card_pos (α := E); omega
    have : Subsingleton E := (Nat.card_eq_one_iff_unique.mp he).1
    exact not_subsingleton E this
  let N := (c.factor i).subgroupOf O
  let := c.factor_normal_in_offenderSubgroup i
  obtain ⟨Q,hQ⟩ := P.exists_sylow_map_eq_inf_of_normal N
  have hN : Nat.card N = 6 :=
    (Nat.card_congr (subgroupOfEquivOfLe (c.factor_le_offenderSubgroup i)).toEquiv).trans
      (c.factor_card i)
  have hQne : (Q : Subgroup N) ≠ ⊥ := Q.ne_bot_of_dvd_card (by rw [hN]; decide)
  obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQne
  let g : c.factor i := ⟨((a : N) : O), a.val.property⟩
  have hgA : (g : G) ∈ A := by
    have hh : (a.val : O) ∈ (P : Subgroup O) ⊓ N :=
      hQ ▸ mem_map_of_mem N.subtype a.property
    exact mem_map_of_mem O.subtype hh.1
  have hgne : g ≠ 1 := by
    intro he
    apply ha
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : c.factor i => (x : G)) he
  have hM : (c.factorModel i g).val ≠ 1 := by
    intro he
    have hh : c.factorModel i g = 1 := Subtype.ext he
    exact hgne ((c.factorModel i).injective (hh.trans (map_one _).symm))
  let f : E → {w : Fin 2 → ZMod 2 // (c.factorModel i g).val.mulVec w = w} :=
    fun w => ⟨c.naturalEquiv i ⟨w,w.property.1⟩, by
      have hh := (c.naturalEquiv_action i g ⟨w,w.property.1⟩).symm.trans
        (w.property.2 ⟨g,hgA⟩)
      have hW : (c.naturalEquiv i).symm
          (specialLinearNatural 2 (c.factorModel i g) (c.naturalEquiv i ⟨w,w.property.1⟩)) =
          (⟨w,w.property.1⟩ : W) := Subtype.ext hh
      have hh' := congrArg (c.naturalEquiv i) hW
      simpa only [LinearEquiv.apply_symm_apply, specialLinearNatural_apply] using hh'⟩
  have hfi : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    exact congrArg (fun x : W => (x : V))
      ((c.naturalEquiv i).injective (congrArg Subtype.val he))
  have hhigh := (Nat.card_le_card_of_injective f hfi).trans
    (SL2NaturalOffenders.fixedVectors_card_le (c.factorModel i g).val hM)
  have hz : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  change Nat.card E = 2
  omega
end CFSG.Quasithin.ChapterB.SolvableFFFactors
