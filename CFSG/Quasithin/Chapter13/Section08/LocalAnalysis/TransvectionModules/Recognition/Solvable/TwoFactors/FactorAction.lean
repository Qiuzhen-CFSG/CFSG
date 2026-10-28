module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.TwoFactors.Basic
public import Theory.GroupTheory.SpecificGroups.PermThreeProduct
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Conjugation permutes the two actual symmetric-three factors

A normal subgroup isomorphic to S₃ in S₃ × S₃ is a coordinate factor.
The coordinate-compatible B.1.8 decomposition therefore makes ambient
conjugation permute its factors. Uniqueness of their indices constructs a
homomorphism to the permutation group, with the literal conjugation equation.
The normal-generation and Sylow-image arguments in `Basic` now apply with
this action constructed, rather than assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.5, printed p.947 (PDF p.964).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.TwoFactors
open ChapterB
variable {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : Representation (ZMod 2) A E}

/-- The actual internal product, transported to two concrete symmetric groups. -/
noncomputable def twoFactorModel (d : SolvableFFFactors ρ)
    (hJ : offenderSubgroup ρ = ⊤) (hc : d.count = 2) :
    A ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
  let e : ((i : Fin d.count) → d.factor i) ≃* A :=
    d.groupProduct.trans ((MulEquiv.subgroupCongr hJ).trans Subgroup.topEquiv)
  let q : (Fin d.count → Equiv.Perm (Fin 3)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
    rw [hc]
    exact { toEquiv := finTwoArrowEquiv _
            map_mul' := fun _ _ => rfl }
  exact e.symm.trans ((MulEquiv.piCongrRight (factorSymmetricModel d)).trans q)

private theorem factor_normal (d : SolvableFFFactors ρ)
    (hJ : offenderSubgroup ρ = ⊤) (i : Fin d.count) : (d.factor i).Normal := by
  have hn := d.factor_normal_in_offenderSubgroup i
  have he : ((d.factor i).subgroupOf (offenderSubgroup ρ)).map
      (offenderSubgroup ρ).subtype = d.factor i :=
    map_subgroupOf_eq_of_le (d.factor_le_offenderSubgroup i)
  have hs : Function.Surjective (offenderSubgroup ρ).subtype := by
    intro x
    exact ⟨⟨x, hJ ▸ mem_top x⟩, rfl⟩
  exact he ▸ hn.map _ hs

/-- A normal symmetric-three subgroup of the actual product is a literal factor. -/
theorem normal_symmetricThree_eq_factor (d : SolvableFFFactors ρ)
    (hJ : offenderSubgroup ρ = ⊤) (hc : d.count = 2)
    (N : Subgroup A) [N.Normal] (eN : N ≃* Equiv.Perm (Fin 3)) :
    ∃ i, N = d.factor i := by
  let e := twoFactorModel d hJ hc
  have he (B : Subgroup A) (hB : B.Normal) (eB : B ≃* Equiv.Perm (Fin 3)) :
      B.map e.toMonoidHom = (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥ ∨
      B.map e.toMonoidHom = (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod ⊤ := by
    let := hB.map e.toMonoidHom e.surjective
    exact Theory.GroupTheory.PermThreeProduct.normal_subgroup_eq_factor _
      ((e.subgroupMap B).symm.trans eB)
  let i : Fin d.count := ⟨0, by omega⟩
  let j : Fin d.count := ⟨1, by omega⟩
  have hij : d.factor i ≠ d.factor j := by
    intro hh
    have := congrArg Fin.val (d.factor_injective hh)
    change 0 = 1 at this
    omega
  have hmap := map_injective (f := e.toMonoidHom) e.injective
  have hi := he (d.factor i) (factor_normal d hJ i) (factorSymmetricModel d i)
  have hj := he (d.factor j) (factor_normal d hJ j) (factorSymmetricModel d j)
  have hn := he N inferInstance eN
  rcases hn with hn | hn <;> rcases hi with hi | hi <;> rcases hj with hj | hj
  all_goals first | exact ⟨i, hmap (hn.trans hi.symm)⟩
                  | exact ⟨j, hmap (hn.trans hj.symm)⟩
                  | exact False.elim (hij (hmap (hi.trans hj.symm)))

theorem conjugate_factor_exists (t : A)
    (d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set A)).subtype))
    (hJ : offenderSubgroup (ρ.comp (normalClosure ({t} : Set A)).subtype) = ⊤)
    (hc : d.count = 2) (a : A) (i : Fin d.count) :
    ∃ j, (ambientFactor t d i).map (MulAut.conj a).toMonoidHom = ambientFactor t d j := by
  let K := normalClosure ({t} : Set A)
  let β : MulAut K := MulAut.conjNormal a
  let : (d.factor i).Normal := factor_normal d hJ i
  let : ((d.factor i).map β.toMonoidHom).Normal :=
    (inferInstance : (d.factor i).Normal).map _ β.surjective
  obtain ⟨j, hj⟩ := normal_symmetricThree_eq_factor d hJ hc
    ((d.factor i).map β.toMonoidHom)
    ((β.subgroupMap (d.factor i)).symm.trans (factorSymmetricModel d i))
  refine ⟨j, ?_⟩
  have he : (ambientFactor t d i).map (MulAut.conj a).toMonoidHom =
      ((d.factor i).map β.toMonoidHom).map K.subtype := by
    rw [ambientFactor, map_map, map_map]
    rfl
  rw [he, hj]
  rfl

theorem ambientFactor_injective (t : A)
    (d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set A)).subtype)) :
    Function.Injective (ambientFactor t d) := by
  intro i j h
  exact d.factor_injective (map_injective (normalClosure ({t} : Set A)).subtype_injective h)

/-- Ambient conjugation permutes the actual coordinate subgroups. -/
noncomputable def factorAction (t : A)
    (d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set A)).subtype))
    (hJ : offenderSubgroup (ρ.comp (normalClosure ({t} : Set A)).subtype) = ⊤)
    (hc : d.count = 2) : FactorAction t d := by
  classical
  let f (a : A) (i : Fin d.count) := (conjugate_factor_exists t d hJ hc a i).choose
  have hf (a : A) (i : Fin d.count) :
      (ambientFactor t d i).map (MulAut.conj a).toMonoidHom = ambientFactor t d (f a i) :=
    (conjugate_factor_exists t d hJ hc a i).choose_spec
  have hone (i : Fin d.count) : f 1 i = i := by
    apply ambientFactor_injective t d
    rw [← hf]
    rw [show (MulAut.conj (1 : A)).toMonoidHom = MonoidHom.id A by ext x; simp]
    exact map_id _
  have hmul (a b : A) (i : Fin d.count) : f (a*b) i = f a (f b i) := by
    apply ambientFactor_injective t d
    rw [← hf, ← hf, ← hf, map_map]
    congr 1
    ext x
    change (a*b)*x*(a*b)⁻¹ = a*(b*x*b⁻¹)*a⁻¹
    group
  let e (a : A) : Equiv.Perm (Fin d.count) :=
    { toFun := f a
      invFun := f a⁻¹
      left_inv := fun i => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun i => by rw [← hmul, mul_inv_cancel, hone] }
  exact
    { permutation :=
        { toFun := e
          map_one' := Equiv.ext hone
          map_mul' := fun a b => Equiv.ext (hmul a b) }
      map_factor := hf }

/-- The genuine factor action now discharges the permutation premise of the
normal-generation argument. -/
theorem sylow_moves_actual_factor [Finite A] (t : A)
    (d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set A)).subtype))
    (hJ : offenderSubgroup (ρ.comp (normalClosure ({t} : Set A)).subtype) = ⊤)
    (hc : d.count = 2) (i : Fin d.count) (hi : t ∈ ambientFactor t d i)
    (T : Sylow 2 A) :
    ∃ a ∈ (T : Subgroup A),
      (ambientFactor t d i).map (MulAut.conj a).toMonoidHom ≠ ambientFactor t d i := by
  obtain ⟨a, ha, hm⟩ := sylow_moves_factor t d hJ hc (factorAction t d hJ hc) i hi T
  refine ⟨a, ha, ?_⟩
  rw [(factorAction t d hJ hc).map_factor]
  exact fun he => hm (ambientFactor_injective t d he)

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.TwoFactors

end
