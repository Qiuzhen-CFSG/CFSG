module
public import Theory.SpecificGroups.PSL3Two.Parabolics.ResidualRecognition
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals

/-!
# Cubic subgroups normalized by a full binary-three Sylow

A three-subgroup of SL₃(2) has order one or three. If it is two-perfect
and normalized by a full Sylow two-subgroup, the parabolic residual
recognition theorem makes it an A₄, contradicting odd order. Projection
applies the same argument to the product of two binary-three groups.

This detects survival of the original parabolic radical in the L₀/O₂(L₀)
quotient in Aschbacher--Smith 10.2.5, printed pp.747--748. It does not assert
survival in a different containing-component quotient.
-/

public section
open Subgroup
namespace Matrix.PSL3Two

/-- A full Sylow cannot normalize a nontrivial two-perfect three-subgroup. -/
theorem sylow_normalized_three_eq_bot (A : Subgroup SL) (S : Sylow 2 SL)
    (hp : IsPGroup 3 A) (hA : IsPPerfect 2 A)
    (hn : (S : Subgroup SL) ≤ normalizer (A : Set SL)) : A = ⊥ := by
  by_contra hne
  obtain ⟨n,hnc⟩ := hp.exists_card_eq
  have hd : 3^n ∣ 168 := by
    simpa only [hnc,card_SL] using A.card_subgroup_dvd_card
  have hn1 : n ≤ 1 := by
    by_contra! hn1
    have h9 : 9 ∣ 168 := (Nat.pow_dvd_pow 3 (by omega : 2 ≤ n)).trans hd
    norm_num at h9
  have hc : Nat.card A = 3 := by
    have hn0 : n ≠ 0 := by
      intro he
      exact hne (card_eq_one.mp (by simpa [he] using hnc))
    rw [hnc,show n=1 by omega,pow_one]
  have hcore : Nat.card (pCore 2 A) = 1 :=
    pCore_isPGroup.card_eq_or_dvd.resolve_right (fun hh => by
      have hd := hh.trans (pCore 2 A).card_subgroup_dvd_card
      rw [hc] at hd
      norm_num at hd)
  have hq : Nat.card (A ⧸ pCore 2 A) = 3 := by
    have he := card_eq_card_quotient_mul_card_subgroup (pCore 2 A)
    rw [hc,hcore,mul_one] at he
    exact he.symm
  obtain ⟨_,_,_,_,g,P,hP,_,hAP,_,_⟩ := ResidualRecognition.recognize A S hA hq hn
  have hsize := Nat.card_congr ((MulAut.conj g).subgroupMap A).toEquiv
  change Nat.card A = Nat.card (A.map (MulAut.conj g).toMonoidHom) at hsize
  rw [hc,hAP] at hsize
  rcases hP with rfl | rfl
  · change 3 = Nat.card (MarkedAutomorphisms.residual pointParabolicSL) at hsize
    rw [MarkedAutomorphisms.card_point_residual] at hsize
    norm_num at hsize
  · change 3 = Nat.card (MarkedAutomorphisms.residual lineParabolicSL) at hsize
    rw [MarkedAutomorphisms.card_line_residual] at hsize
    norm_num at hsize

/-- The same exclusion holds in the product, with its full Sylow retained. -/
theorem pair_sylow_normalized_three_eq_bot
    {B : Type*} [Group B] [Finite B] (e : B ≃* SL × SL)
    (A : Subgroup B) (S : Sylow 2 B) (hp : IsPGroup 3 A) (hA : IsPPerfect 2 A)
    (hn : (S : Subgroup B) ≤ normalizer (A : Set B)) : A = ⊥ := by
  let A' := A.map e.toMonoidHom
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hnorm : (S' : Subgroup (SL × SL)) ≤ normalizer (A' : Set (SL × SL)) :=
    (map_mono hn).trans (le_normalizer_map e.toMonoidHom)
  have hz (f : (SL × SL) →* SL) (hf : Function.Surjective f) : A'.map f = ⊥ :=
    sylow_normalized_three_eq_bot _ (S'.mapSurjective hf)
      ((hp.map e.toMonoidHom).map f)
      ((hA.of_surjective (e.toMonoidHom.subgroupMap A) (e.toMonoidHom.subgroupMap_surjective A)).of_surjective
        (f.subgroupMap A') (f.subgroupMap_surjective A'))
      ((map_mono hnorm).trans (le_normalizer_map f))
  apply (map_eq_bot_iff_of_injective (f := e.toMonoidHom) A e.injective).mp
  apply bot_unique
  intro x hx
  exact Prod.ext
    (mem_bot.mp (hz (MonoidHom.fst SL SL) (fun x => ⟨(x,1),rfl⟩) ▸
      mem_map_of_mem (MonoidHom.fst SL SL) hx))
    (mem_bot.mp (hz (MonoidHom.snd SL SL) (fun x => ⟨(1,x),rfl⟩) ▸
      mem_map_of_mem (MonoidHom.snd SL SL) hx))
end Matrix.PSL3Two
