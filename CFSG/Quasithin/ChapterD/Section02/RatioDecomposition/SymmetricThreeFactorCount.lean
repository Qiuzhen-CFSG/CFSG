module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.SymmetricThreeSeparation

/-!
# Counting marked symmetric-three factors on the original cover

The literal factor product equivalence would project onto three S₃
coordinates if there were three factors. Pulling back the decomposed
subgroup through the original cover retains three-rank at most two, so
this projection is impossible. This supplies the factor-count input to
the proper-orbit symmetric-three separation.

Source: Aschbacher--Smith 15.1.2, printed pp.1084--1085.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G} {U : Submodule (ZMod 2) V}
  (c : FactorData ρ K U) (d : Decomposition c.representation)
namespace FactorData

theorem symmetricThree_factor_count
    (he : ∀ i : d.Index, Nonempty ((d.factor i).Carrier ≃* Equiv.Perm (Fin 3)))
    {B : Type*} [Group B] [Finite B] (f : B →* G) (hf : Function.Surjective f)
    (hrank : primeRank 3 B ≤ 2) : Nat.card d.Index ≤ 2 := by
  classical
  let := Fintype.ofFinite d.Index
  by_contra hcount
  have hthree : 3 ≤ ENat.card d.Index := by
    rw [ENat.card_eq_coe_fintype_card]
    have hn : 3 ≤ Fintype.card d.Index := by
      rw [←Nat.card_eq_fintype_card]
      omega
    exact_mod_cast hn
  let i : d.Index := Classical.arbitrary _
  obtain ⟨j,hj⟩ := (ENat.exists_ne_ne_of_three_le hthree i i)
  obtain ⟨k,hki,hkj⟩ := ENat.exists_ne_ne_of_three_le hthree i j
  let m : ∀ i, (d.factor i).Carrier ≃* Equiv.Perm (Fin 3) := fun i => (he i).some
  obtain ⟨e,_⟩ := d.product_equiv c.faithful
  let a := e.symm.trans (MulEquiv.piCongrRight m)
  let q : K →* Equiv.Perm (Fin 3) × (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
    ((Pi.evalMonoidHom (fun _ : d.Index => Equiv.Perm (Fin 3)) i).prod
      ((Pi.evalMonoidHom (fun _ : d.Index => Equiv.Perm (Fin 3)) j).prod
        (Pi.evalMonoidHom (fun _ : d.Index => Equiv.Perm (Fin 3)) k))).comp a.toMonoidHom
  have hq : Function.Surjective q := by
    intro y
    let w : d.Index → Equiv.Perm (Fin 3) :=
      fun x => if x = i then y.1 else if x = j then y.2.1 else y.2.2
    refine ⟨a.symm w,?_⟩
    change (a (a.symm w) i,a (a.symm w) j,a (a.symm w) k) = y
    simp only [a.apply_symm_apply,w,ite_true,if_neg hj.1,if_neg hki,if_neg hkj]
  let C := K.comap f
  exact Theory.GroupTheory.not_surjective_symmetricThreeCube_of_threeRank_le_two
    ((primeRank_subgroup_le 3 C).trans hrank) (q.comp (f.subgroupComap K))
    (hq.comp (f.subgroupComap_surjective_of_surjective K hf))
end FactorData
end CFSG.Quasithin.ChapterD.RatioDecomposition
