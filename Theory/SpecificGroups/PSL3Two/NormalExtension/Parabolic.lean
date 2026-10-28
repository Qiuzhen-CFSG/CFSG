module
public import Theory.SpecificGroups.PSL3Two.NormalExtension
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterCentralizerGeneration

/-!
# An S₃ parabolic excludes the outer binary linear-three extension

A normal L₃(2) section supplemented by a two-group gives L₃(2) or its full
automorphism group modulo the ambient two-core. In the outer case a full
Sylow two-subgroup has order sixteen and therefore contains an outer actor.
Every non-two-group over it contains the inner L₃(2), by the concrete
parabolic automorphism theorem. An overgroup with S₃ two-core quotient is
not a two-group but has no factor seven in its order, a contradiction.

Thus an actual S₃ parabolic upgrades the normal component quotient to the
whole group's L₃(2) quotient. The argument uses the literal core quotient
and does not assume a split extension or identify the two quotients.
Source application: Aschbacher–Smith 13.4.7(ii) to 13.4.9, printed p.906.
The imported linear-three automorphism models retain their existing ATLAS
attribution and license, LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Two
variable {G : Type*} [Group G] [Finite G]

private theorem symmetricThree_quotient_not_two {A : Type*} [Group A]
    (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) : ¬ IsPGroup 2 A := by
  intro hp
  obtain ⟨n,hn⟩ := ((hp.to_quotient (pCore 2 A)).of_equiv e).exists_card_eq
  have hd : 3 ∣ Nat.card (Equiv.Perm (Fin 3)) := by
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
  rw [hn] at hd
  exact (by decide : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

private theorem symmetricThree_quotient_seven_free {A : Type*} [Group A] [Finite A]
    (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) : ¬ 7 ∣ Nat.card A := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  have hc : Nat.card A = 6 * 2 ^ n := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 A),Nat.card_congr e.toEquiv,
      Nat.card_perm,Nat.card_fin,hn]
    rfl
  rw [hc]
  intro hd
  rcases (by decide : Nat.Prime 7).dvd_mul.mp hd with hd | hd
  · exact (by decide : ¬ (7 : ℕ) ∣ 6) hd
  · exact (by decide : ¬ (7 : ℕ) ∣ 2) ((by decide : Nat.Prime 7).dvd_of_dvd_pow hd)

/-- A two-group-kernel quotient onto Aut(L₃(2)) is incompatible with an
S₃ two-core quotient on an overgroup of a full Sylow two-subgroup. -/
theorem no_automorphism_quotient_with_symmetricThree_parabolic
    (f : G →* MulAut SL) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Sylow 2 G) (B : Subgroup G) (hSB : (S : Subgroup G) ≤ B)
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) : False := by
  let R := S.mapSurjective hf
  let H := B.map f
  have hRH : (R : Subgroup (MulAut SL)) ≤ H := map_mono hSB
  have hH : ¬ IsPGroup 2 H := by
    intro hp
    exact symmetricThree_quotient_not_two eB
      ((hp.comap_of_ker_isPGroup f hk).to_le (le_comap_map f B))
  have hAut : Nat.card (MulAut SL) = 336 := by
    rw [Nat.card_congr (MulAut.congr equiv).toEquiv]
    exact Automorphisms.card_aut
  have hR : Nat.card (R : Subgroup (MulAut SL)) = 16 := by
    rw [R.card_eq_multiplicity,hAut]
    decide +kernel
  have hinj : Function.Injective (MulAut.conj : SL →* MulAut SL) :=
    MulAut.conj_injective_of_center_eq_bot center_eq_bot
  have hI : Nat.card (MulAut.innerSubgroup SL) = 168 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,card_SL]
  have hnot : ¬ (R : Subgroup (MulAut SL)) ≤ MulAut.innerSubgroup SL := by
    intro hh
    have hd := card_dvd_of_le hh
    rw [hR,hI] at hd
    norm_num at hd
  obtain ⟨a,ha,hna⟩ := SetLike.not_le_iff_exists.mp hnot
  have hIH := Automorphisms.OuterCentralizerGeneration.inner_le_of_sylow_le_of_not_isTwoGroup
    R H hRH hH a (hRH ha) hna
  have hd : 7 ∣ Nat.card H := (show 7 ∣ Nat.card (MulAut.innerSubgroup SL) by rw [hI]; decide).trans
    (card_dvd_of_le hIH)
  exact symmetricThree_quotient_seven_free eB (hd.trans
    (card_dvd_of_surjective (f.subgroupMap B) (f.subgroupMap_surjective B)))

/-- The normal L₃(2) component and an actual S₃ parabolic exclude diagram
extension, so the whole group's quotient is L₃(2). -/
theorem quotient_of_normal_component_and_symmetricThree_parabolic
    (N : Subgroup G) [N.Normal]
    (eN : (N ⧸ pCore 2 N) ≃* PSL)
    (S : Sylow 2 G) (hgen : N ⊔ (S : Subgroup G) = ⊤)
    (B : Subgroup G) (hSB : (S : Subgroup G) ≤ B)
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) :
    Nonempty ((G ⧸ pCore 2 G) ≃* PSL) := by
  let t := BinaryLinear.OuterCyclic.slEquivLinear 3
  obtain hinner | houter := BinaryLinear.NormalThreeExtension.quotient N (S : Subgroup G)
    (eN.trans (equiv.symm.trans t)) S.isPGroup' hgen
  · obtain ⟨e⟩ := hinner
    exact ⟨e.trans (t.symm.trans equiv)⟩
  · obtain ⟨e⟩ := houter
    let a := e.trans (MulAut.congr t.symm)
    let f := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
    have hf : Function.Surjective f := a.surjective.comp (QuotientGroup.mk'_surjective _)
    have hk : IsPGroup 2 f.ker := by
      rw [MonoidHom.ker_comp_of_injective _ _ a.injective,QuotientGroup.ker_mk']
      exact pCore_isPGroup
    exact (no_automorphism_quotient_with_symmetricThree_parabolic f hf hk S B hSB eB).elim
end Matrix.PSL3Two
