module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.Rank

/-!
# Genuine cyclic conjugates and residual lifts in N_G(U)

Transitivity of the decomposition supplies conjugating automizers, which are
lifted to actual elements of N_G(V). Conjugating X there produces faithful
cyclic subgroups of the same order, with images in the respective factors.
Commutation of their images with the distinguished image shows that every
one normalizes U. The same argument puts residual lifts of all the other
factors in N_G(U).

Pairwise commutation of the cyclic lifts is a further local-group argument;
it is not inferred from commutation of their action images.
Source: Aschbacher–Smith, E.6.25, printed p.255 (PDF p.266).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors
variable {G : Type*} [Group G] {M V U X : Subgroup G} [IsElementaryAbelian 2 V]

/-- Commutation of the actual induced actions implies normalization of the fixed subgroup. -/
theorem normalizes_fixed_of_image_commutes (hX : RegularCyclicSection M V U X)
    (A : Subgroup (normalizer (V : Set G)))
    (hc : ∀ a ∈ A.map V.normalizerMonoidHom.rangeRestrict,
      ∀ x ∈ inducedAutomizer V X, Commute a x) :
    A.map (normalizer (V : Set G)).subtype ≤ normalizer (U : Set G) := by
  have hXN : X ≤ normalizer (V : Set G) :=
    hX.contained.trans (inf_le_left.trans inf_le_right)
  apply le_normalizer_iff.mpr
  rintro g ⟨a, ha, rfl⟩ u hu
  have huV : u ∈ V := (hX.fixed.symm ▸ hu).1
  let v : Additive V := Additive.ofMul ⟨u, huV⟩
  let b := V.normalizerMonoidHom.rangeRestrict a
  have hv : v ∈ fixedSpace (automizerRepresentation V) (inducedAutomizer V X) :=
    (mem_fixedSpace_inducedAutomizer V X hXN v).mpr (hX.fixed.symm ▸ hu).2
  have hw : automizerRepresentation V b v ∈
      fixedSpace (automizerRepresentation V) (inducedAutomizer V X) := by
    intro x
    have he := congrArg (fun c => automizerRepresentation V c v)
      (hc b (mem_map_of_mem _ ha) x x.property).eq.symm
    have hvx := hv x
    change automizerRepresentation V (x : Automizer V) v = v at hvx
    change automizerRepresentation V (x : Automizer V) (automizerRepresentation V b v) = _
    simpa only [map_mul, Module.End.mul_apply, hvx] using he
  have hwC := (mem_fixedSpace_inducedAutomizer V X hXN _).mp hw
  rw [← hX.fixed]
  exact ⟨(V.normalizerMonoidHom a ⟨u, huV⟩).property, hwC⟩

private theorem map_conjugate {A B : Type*} [Group A] [Group B]
    (f : A →* B) (C : Subgroup A) (a : A) :
    (C.map (MulAut.conj a).toMonoidHom).map f =
      (C.map f).map (MulAut.conj (f a)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp

/-- Each factor contains the faithful action of an actual conjugate of X in N_G(U).
The theorem does not claim that these conjugates commute in the ambient group. -/
theorem exists_conjugate_cyclic_lift (hX : RegularCyclicSection M V U X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X)) (i : Fin D.size) :
    ∃ n : normalizer (V : Set G),
      let A := (X.subgroupOf (normalizer (V : Set G))).map (MulAut.conj n).toMonoidHom
      A.map (normalizer (V : Set G)).subtype ≤ normalizer (U : Set G) ∧
      IsCyclic A ∧ Nat.card A = Nat.card X ∧
      Function.Injective (V.normalizerMonoidHom.rangeRestrict.comp A.subtype) ∧
      A.map V.normalizerMonoidHom.rangeRestrict ≤ D.factor i := by
  have hXN : X ≤ normalizer (V : Set G) :=
    hX.contained.trans (inf_le_left.trans inf_le_right)
  let N := normalizer (V : Set G)
  let f := V.normalizerMonoidHom.rangeRestrict
  let C := X.subgroupOf N
  have hinjC : Function.Injective (f.comp C.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have he : V.normalizerMonoidHom x.val = 1 :=
      congrArg (fun a : Automizer V => (a : MulAut V)) hx
    have hxC : (x.val : G) ∈ centralizer (V : Set G) := by
      have hk : x.val ∈ V.normalizerMonoidHom.ker := he
      rwa [Subgroup.normalizerMonoidHom_ker] at hk
    apply mem_bot.mpr
    apply Subtype.ext
    apply Subtype.ext
    exact mem_bot.mp (hX.faithful ▸ (show (x.val : G) ∈ X ⊓ centralizer (V : Set G) from
      ⟨x.property, hxC⟩))
  have hcycC : IsCyclic C := by
    let _ := hX.cyclic
    exact isCyclic_of_surjective (subgroupOfEquivOfLe hXN).symm
      (subgroupOfEquivOfLe hXN).symm.surjective
  have hcardC : Nat.card C = Nat.card X :=
    Nat.card_congr (subgroupOfEquivOfLe hXN).toEquiv
  have hbase (n : N) :
      IsCyclic (C.map (MulAut.conj n).toMonoidHom) ∧
      Nat.card (C.map (MulAut.conj n).toMonoidHom) = Nat.card X ∧
      Function.Injective (f.comp (C.map (MulAut.conj n).toMonoidHom).subtype) := by
    let e := C.equivMapOfInjective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective
    refine ⟨?_, (Nat.card_congr e.toEquiv).symm.trans hcardC, ?_⟩
    · let _ := hcycC
      exact isCyclic_of_surjective e e.surjective
    · intro x y he
      obtain ⟨x', rfl⟩ := e.surjective x
      obtain ⟨y', rfl⟩ := e.surjective y
      apply congrArg e
      apply hinjC
      change f (n * (x' : N) * n⁻¹) = f (n * (y' : N) * n⁻¹) at he
      change f (x' : N) = f (y' : N)
      simpa only [map_mul, map_inv, mul_left_cancel_iff, mul_right_cancel_iff] using he
  by_cases hid : i = D.distinguished
  · subst i
    refine ⟨1, ?_⟩
    have hm : C.map (MulAut.conj (1 : N)).toMonoidHom = C := by
      ext x
      simp
    dsimp only
    rw [hm]
    refine ⟨?_, hcycC, hcardC, hinjC, D.contained⟩
    rw [map_subgroupOf_eq_of_le hXN]
    exact hX.contained.trans (inf_le_right.trans (centralizer_le_normalizer _))
  · obtain ⟨b, hb, _⟩ := D.transitive D.distinguished i
    obtain ⟨n, hn⟩ := V.normalizerMonoidHom.rangeRestrict_surjective b
    let A := C.map (MulAut.conj n).toMonoidHom
    have him : A.map f ≤ D.factor i := by
      rw [map_conjugate, hn, ← hb]
      exact map_mono D.contained
    refine ⟨n, ?_, (hbase n).1, (hbase n).2.1, (hbase n).2.2, him⟩
    apply normalizes_fixed_of_image_commutes hX A
    intro a ha x hx
    exact D.commuting hid a (him ha) x (D.contained hx)
/-- A commuting automizer subgroup has its full preimage in the normalizer
of U. This is a containment assertion, with no order claim on the preimage. -/
theorem automizerPreimage_normalizes_fixed (hX : RegularCyclicSection M V U X)
    (B : Subgroup (Automizer V))
    (hc : ∀ b ∈ B, ∀ x ∈ inducedAutomizer V X, Commute b x) :
    automizerPreimage V B ≤ normalizer (U : Set G) := by
  apply normalizes_fixed_of_image_commutes hX
  intro b hb x hx
  have he : (B.comap V.normalizerMonoidHom.rangeRestrict).map
      V.normalizerMonoidHom.rangeRestrict = B :=
    map_comap_eq_self_of_surjective V.normalizerMonoidHom.rangeRestrict_surjective B
  exact hc b (he ▸ hb) x hx

/-- Each nondistinguished factor has a genuine two-perfect lift normalizing U. -/
theorem residualLift_factor_normalizes_fixed (hX : RegularCyclicSection M V U X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (i : Fin D.size) (hi : i ≠ D.distinguished) :
    residualLift V (D.factor i) ≤ normalizer (U : Set G) := by
  apply (residualLift_le_preimage V _).trans
  apply automizerPreimage_normalizes_fixed hX
  intro b hb x hx
  exact D.commuting hi b hb x (D.contained hx)
end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors
