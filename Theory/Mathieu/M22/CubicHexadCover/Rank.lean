module
public import Theory.Alternating.TripleSevenLocalRank.CentralSix
public import Theory.Alternating.PrimeRank

/-!
# The perfect section above a cubic central hexad cover

A central cover with kernel of order dividing three retains three-rank at
least two above an embedded A₆. Over a perfect image, the solvable residual
still maps onto that image. These facts supply the rank half of the M₂₂
hexad argument in Aschbacher--Smith 14.3.6(6), printed p.994.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.CubicHexadCover
variable {E H : Type*} [Group E] [Finite E] [Group H] [Finite H]

omit [Finite H] in
theorem rank_two_of_cubic_central_cover
    (f : E →* H) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker ∣ 3)
    (j : alternatingGroup (Fin 6) →* H) (hj : Function.Injective j) :
    2 ≤ primeRank 3 E := by
  rcases (Nat.dvd_prime Nat.prime_three).mp hk with h1 | h3
  · have hi : Function.Injective f := f.ker_eq_bot_iff.mp (eq_bot_of_card_eq _ h1)
    let e := MulEquiv.ofBijective f ⟨hi,hf⟩
    have hh := Theory.GroupTheory.primeRank_le_of_injective 3 (e.symm.toMonoidHom.comp j) (e.symm.injective.comp hj)
    rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 (by decide) (by decide)] at hh
    exact hh
  · exact (GLS3.Chapter5.OddCentralCovers.twoLocalThreeRank_ge_two_of_embedded_six
      f hf hc h3 j hj).trans (twoLocalPrimeRank_le_primeRank 3)

omit [Finite H] in
/-- The derived group above a perfect hexad image retains three-rank two. -/
theorem perfect_rank_two_in_preimage
    (f : E →* H)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker ∣ 3)
    (A : Subgroup E) (B : Subgroup H) [Group.IsPerfect B]
    (hm : A.map f = B)
    (j : alternatingGroup (Fin 6) →* B) (hj : Function.Injective j) :
    ∃ D : Subgroup E, D ≤ A ∧ Group.IsPerfect D ∧ 2 ≤ primeRank 3 D := by
  let R := solvableResidual A
  let D := R.map A.subtype
  let r : D ≃* R := (R.equivMapOfInjective A.subtype A.subtype_injective).symm
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective
    (f := r.symm.toMonoidHom) r.symm.surjective
  have hmap : D.map f = B := by
    let g : A →* B := (f.comp A.subtype).codRestrict B (by
      intro a
      exact hm ▸ mem_map_of_mem f a.property)
    have hg : Function.Surjective g := by
      intro b
      obtain ⟨a,ha,hab⟩ := (show b.val ∈ A.map f from hm.symm ▸ b.property)
      exact ⟨⟨a,ha⟩,Subtype.ext hab⟩
    have hh := map_solvableResidual_eq g hg
    rw [solvableResidual_eq_top (G := B)] at hh
    have hx := congrArg (Subgroup.map B.subtype) hh
    rw [map_map,←MonoidHom.range_eq_map,range_subtype] at hx
    change R.map (f.comp A.subtype) = B at hx
    simpa only [D,map_map] using hx
  let g : D →* B := (f.comp D.subtype).codRestrict B (fun d => hmap ▸ mem_map_of_mem f d.property)
  have hg : Function.Surjective g := by
    intro b
    obtain ⟨d,hd,hdb⟩ := (show b.val ∈ D.map f from hmap.symm ▸ b.property)
    exact ⟨⟨d,hd⟩,Subtype.ext hdb⟩
  have hgc : g.ker ≤ center D := by
    intro d hd
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact mem_center_iff.mp (hc (congrArg Subtype.val hd)) x
  have hkd : Nat.card g.ker ∣ Nat.card f.ker := by
    let k : g.ker →* f.ker := (D.subtype.comp g.ker.subtype).codRestrict f.ker
      (fun d => congrArg Subtype.val d.property)
    apply card_dvd_of_injective k
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.ker => (z : E)) h
  exact ⟨D,map_subtype_le R,inferInstance,
    rank_two_of_cubic_central_cover g hg hgc (hkd.trans hk) j hj⟩

end Sporadic.Mathieu.CubicHexadCover
