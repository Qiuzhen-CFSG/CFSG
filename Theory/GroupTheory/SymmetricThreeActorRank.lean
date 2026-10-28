module

public import Theory.GroupTheory.NormalSymmetricThree
public import Theory.GroupTheory.SymmetricThreeSylowNormalizer
public import Theory.GroupTheory.CentralizingTorusRank
public import Theory.Quasithin.Rank

/-!
# A two-perfect actor normalizing a marked symmetric-three Sylow

A normal S₃ factor splits off its centralizer. An actor normalizing its
specified Sylow two-subgroup projects into that self-normalizing Sylow.
Two-perfectness kills this projection, so the actor centralizes the factor.
Their independent three-ranks then force the actor to have three-rank at
most one when the ambient three-rank is at most two.

The Chapter13 application uses the actual L₁ image and J(R₁) image in
H/C_H(V_H). Source: Aschbacher–Smith 13.4.8, printed p.905.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.NormalSymmetricThree
variable {G : Type*} [Group G] [Finite G]
local notation "S3" => Equiv.Perm (Fin 3)

theorem twoPerfect_normalizer_centralizes (I : Subgroup G) [I.Normal]
    (e : I ≃* S3) (P : Sylow 2 I) (A : Subgroup G)
    (hA : IsPPerfect 2 A)
    (hn : A ≤ normalizer ((P : Subgroup I).map I.subtype : Set G)) :
    A ≤ centralizer (I : Set G) := by
  let C := centralizer (I : Set G)
  let J := (P : Subgroup I).map I.subtype
  obtain ⟨d,hd⟩ := exists_product_equiv I e
  let f : G →* I := (MonoidHom.fst I C).comp d.symm.toMonoidHom
  have hproj (a : A) : f a ∈ (P : Subgroup I) := by
    let i : I := (d.symm a).1
    let c : C := (d.symm a).2
    have ha : (a : G) = i.val * c.val := by
      rw [← hd]
      exact (d.apply_symm_apply a).symm
    have hJI : J ≤ I := map_subtype_le _
    have hc : c.val ∈ normalizer (J : Set G) :=
      Subgroup.centralizer_le_normalizer _ (centralizer_le (show (J : Set G) ⊆ I from hJI) c.property)
    have hin : i.val ∈ normalizer (J : Set G) := by
      have hh := (normalizer (J : Set G)).mul_mem (hn a.property)
        ((normalizer (J : Set G)).inv_mem hc)
      simpa only [ha,mul_inv_cancel_right] using hh
    have hJP : J.subgroupOf I = (P : Subgroup I) := by
      ext x
      exact mem_map_iff_mem I.subtype_injective
    have hip : i ∈ normalizer (P : Set I) := by
      change i ∈ normalizer ((P : Subgroup I) : Set I)
      rw [← hJP, ← subgroupOf_normalizer_eq hJI]
      exact hin
    rw [SymmetricThreeSylowNormalizer.of_models (Or.inl ⟨e⟩) P] at hip
    exact hip
  let g : A →* (P : Subgroup I) := (f.comp A.subtype).codRestrict _ hproj
  have hg := hA.hom_eq_one_of_isPGroup P.isPGroup' g
  intro a ha
  have hi : (d.symm a).1 = 1 := congrArg Subtype.val (DFunLike.congr_fun hg (⟨a,ha⟩ : A))
  have hc : a = ((d.symm a).2 : G) := by
    calc
      a = d (d.symm a) := (d.apply_symm_apply a).symm
      _ = ((d.symm a).1 : G) * ((d.symm a).2 : G) := hd _ _
      _ = _ := by rw [hi]; simp only [coe_one,one_mul]
  rw [hc]
  exact (d.symm a).2.property

theorem threeRank_le_one_of_twoPerfect_normalizer
    (I : Subgroup G) [I.Normal] (e : I ≃* S3) (P : Sylow 2 I)
    (A : Subgroup G) (hA : IsPPerfect 2 A)
    (hn : A ≤ normalizer ((P : Subgroup I).map I.subtype : Set G))
    (hrank : primeRank 3 G ≤ 2) : primeRank 3 A ≤ 1 := by
  have hc := twoPerfect_normalizer_centralizes I e P A hA hn
  have hd : Disjoint I A := (centralizer_disjoint I e).mono_right hc
  have hcard : 3 ∣ Nat.card I := by
    rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]
    decide
  by_contra h
  have hb := three_le_primeRank_of_disjoint_commuting I A hd
    (le_centralizer_iff.mp hc) hcard (by omega)
  have hup := (primeRank_subgroup_le (p := 3) (I ⊔ A)).trans hrank
  omega
end Theory.GroupTheory.NormalSymmetricThree
