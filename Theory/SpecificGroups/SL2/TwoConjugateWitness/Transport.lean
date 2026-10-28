module

public import Theory.SpecificGroups.SL2.TwoConjugateWitness.Standard
/-!
# Transport of the binary linear two-conjugate witness

Injective homomorphisms preserve a witness when the prescribed Sylow and Borel
subgroups pull back to its original markings. The proof transports every
literal subgroup and the internal conjugator, then uses the surjective
restricted equivalence for the normal core. Sylow conjugacy gives the witness
for every Sylow of SL₂, and arbitrary model equivalences give the same source
witness in any group with that actual matrix model.

Source application: Aschbacher–Smith E.2.7, printed p.218; the same marked
transport applies to the central-root linear subgroup of the unitary model.
-/

@[expose] public section

open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup.TwoConjugateWitness

namespace Witness
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H] {S M V : Subgroup G} {n : ℕ}

noncomputable def map (w : Witness S M V n) (f : G →* H) (hf : Function.Injective f)
    (S' M' : Subgroup H) (hS : S'.comap f = S) (hM : M'.comap f = M) :
    Witness S' M' (V.map f) n := by
  let I := w.subgroup.map f
  let e : w.subgroup ≃* I := w.subgroup.equivMapOfInjective f hf
  have he (x : w.subgroup) : (e x : H) = f x := rfl
  have hmap (A : Subgroup H) (B : Subgroup G) (hAB : A.comap f = B) :
      (B.subgroupOf w.subgroup).map e.toMonoidHom = A.subgroupOf I := by
    have hc : (A.subgroupOf I).comap e.toMonoidHom = B.subgroupOf w.subgroup := by
      ext x
      change f x ∈ A ↔ (x : G) ∈ B
      exact SetLike.ext_iff.mp hAB (x : G)
    rw [← hc, map_comap_eq_self_of_surjective e.surjective]
  have hV : (V.subgroupOf w.subgroup).map e.toMonoidHom = (V.map f).subgroupOf I :=
    hmap _ _ (comap_map_eq_self_of_injective hf V)
  have hS' : (S.subgroupOf w.subgroup).map e.toMonoidHom = S'.subgroupOf I := hmap _ _ hS
  have hM' : (M.subgroupOf w.subgroup).map e.toMonoidHom = M'.subgroupOf I := hmap _ _ hM
  let g := e w.conjugator
  let P := w.sylow.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPe : (P : Subgroup I) = (w.sylow : Subgroup w.subgroup).map e.toMonoidHom := rfl
  let d := e.symm.trans w.model
  have hd : d.toMonoidHom.comp e.toMonoidHom = w.model.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change w.model (e.symm (e x)) = w.model x
    rw [e.symm_apply_apply]
  have hgen : (V.map f).subgroupOf I ⊔
      ((V.map f).subgroupOf I).map (MulAut.conj g).toMonoidHom = ⊤ := by
    have hh := congrArg (Subgroup.map e.toMonoidHom) w.generate
    rw [pair_map, hV, map_top_of_surjective _ e.surjective] at hh
    exact hh
  have hcore : (M'.subgroupOf I).normalCore = ⊥ := by
    have hm : (M'.subgroupOf I).comap e.toMonoidHom = M.subgroupOf w.subgroup := by
      rw [← hM', comap_map_eq_self_of_injective e.injective]
    have hh := normalCore_comap_of_surjective e.toMonoidHom e.surjective (M'.subgroupOf I)
    rw [hm,w.corefree] at hh
    have hi := congrArg (Subgroup.map e.toMonoidHom) hh
    rw [Subgroup.map_bot,map_comap_eq_self_of_surjective e.surjective] at hi
    exact hi.symm
  refine ⟨I,map_mono w.le,g,?_,hgen,P,?_,w.degree,w.degree_gt_one,w.degree_dvd,d,?_,?_,hcore⟩
  · intro hg
    apply w.outside
    exact (SetLike.ext_iff.mp hM (w.conjugator : G)).mp hg
  · rw [hPe,w.sylow_eq,hS']
  · rw [hPe,Subgroup.map_map,hd,w.sylow_model]
  · rw [← hM',Subgroup.map_map,hd,w.borel_model]

end Witness


theorem exists_sylow {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (S : Sylow 2 SL(2,F))
    (V : Subgroup SL(2,F)) (hVS : V ≤ S) (hVc : 4 ≤ Nat.card V) :
    Nonempty (Witness (S : Subgroup SL(2,F)) (normalizer (S : Set SL(2,F))) V n) := by
  obtain ⟨z,hz⟩ := MulAction.exists_smul_eq SL(2,F) (upperUnipotentSylow F 2) S
  let f := MulAut.conj z
  have hUS : (upperUnipotent F).map f.toMonoidHom = (S : Subgroup SL(2,F)) :=
    congrArg (fun R : Sylow 2 SL(2,F) => R.toSubgroup) hz
  have hS : (S : Subgroup SL(2,F)).comap f.toMonoidHom = upperUnipotent F := by
    rw [← hUS, comap_map_eq_self_of_injective f.injective]
  let W := V.comap f.toMonoidHom
  have hWU : W ≤ upperUnipotent F := by
    rw [← hS]
    exact comap_mono hVS
  have hWV : W.map f.toMonoidHom = V := map_comap_eq_self_of_surjective f.surjective V
  have hWc : 4 ≤ Nat.card W := by
    rw [← Subgroup.card_map_of_injective (f := f.toMonoidHom) (K := W) f.injective, hWV]
    exact hVc
  obtain ⟨w⟩ := exists_upper hF W hWU hWc
  have hM : (normalizer (S : Set SL(2,F))).comap f.toMonoidHom = rankOneBorel F := by
    change (normalizer ((S : Subgroup SL(2,F)) : Set SL(2,F))).comap f.toMonoidHom = _
    rw [comap_normalizer_eq_of_surjective (S : Subgroup SL(2,F)) f.surjective, hS]
  have hm := w.map f.toMonoidHom f.injective (S : Subgroup SL(2,F))
    (normalizer (S : Set SL(2,F))) hS hM
  rw [hWV] at hm
  exact ⟨hm⟩


theorem exists_of_equiv {G F : Type*} [Group G] [Finite G]
    [Field F] [Finite F] [CharP F 2] {n : ℕ} (hF : Nat.card F = 2^n)
    (e : G ≃* SL(2,F)) (S : Sylow 2 G) (V : Subgroup G)
    (hVS : V ≤ S) (hVc : 4 ≤ Nat.card V) :
    Nonempty (Witness (S : Subgroup G) (normalizer (S : Set G)) V n) := by
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let W := V.map e.toMonoidHom
  have hWQ : W ≤ (Q : Subgroup SL(2,F)) := map_mono hVS
  have hWc : 4 ≤ Nat.card W := by
    have hh : Nat.card W = Nat.card V := card_map_of_injective e.injective
    omega
  obtain ⟨w⟩ := exists_sylow hF Q W hWQ hWc
  have hS : (S : Subgroup G).comap e.symm.toMonoidHom = (Q : Subgroup SL(2,F)) :=
    comap_equiv_eq_map_symm e.symm (S : Subgroup G)
  have hM : (normalizer (S : Set G)).comap e.symm.toMonoidHom =
      normalizer (Q : Set SL(2,F)) := by
    change (normalizer ((S : Subgroup G) : Set G)).comap e.symm.toMonoidHom = _
    rw [comap_normalizer_eq_of_surjective (S : Subgroup G) e.symm.surjective,hS]
    rfl
  have hm := w.map e.symm.toMonoidHom e.symm.injective (S : Subgroup G)
    (normalizer (S : Set G)) hS hM
  have hWV : W.map e.symm.toMonoidHom = V := by
    change (V.map e.toMonoidHom).map e.symm.toMonoidHom = V
    rw [Subgroup.map_map]
    have hc : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      apply MonoidHom.ext
      intro x
      exact e.symm_apply_apply x
    rw [hc,Subgroup.map_id]
  rw [hWV] at hm
  exact ⟨hm⟩

end Matrix.SpecialLinearGroup.TwoConjugateWitness
