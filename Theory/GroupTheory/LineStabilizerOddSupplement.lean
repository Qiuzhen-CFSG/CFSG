module
public import Theory.GroupTheory.Hall.OddSylowComplement
public import Mathlib.Algebra.Group.Subgroup.Actions

/-!
# Odd supplements inside a line stabilizer

Let C be a finite solvable subgroup containing an ambient Sylow
two-subgroup S. Suppose C permutes an indexed family of subgroups and S
is transitive on that family, in the explicit conjugation sense at a
selected member. Then C is the literal set product U S for an odd-order
subgroup U contained in C and in the selected member's normalizer.

The orbit hypotheses give C = S K, where K is that stabilizer in C.
Extend a Sylow subgroup of K to one of C and conjugate it into S.
Factoring the conjugating element through S K shows that a conjugate
inside K already lies in S. Hall's theorem supplies an odd complement
to this Sylow subgroup of K. Inverting the S K factorization then gives
the required order U S.

This general orbit-stabilizer and Hall argument supplies the compatible
odd supplement in Stellmacher (4.6), Journal of Algebra 190 (1997), p26.
Source: refs/latex/stellmacher-n-group.tex. Neither the stabilizer nor its
odd supplement is assumed normal.
-/

open scoped Pointwise
namespace Subgroup

private theorem odd_supplement_of_sylow_stabilizer_product
    {G : Type*} [Group G] [Finite G] (hsolv : Group.IsSolvable G)
    (S : Sylow 2 G) (K : Subgroup G)
    (hprod : ∀ g : G, ∃ s ∈ S, ∃ k ∈ K, g = s * k) :
    ∃ U : Subgroup G, U ≤ K ∧ Odd (Nat.card U) ∧
      ∀ g : G, ∃ u ∈ U, ∃ s ∈ S, g = u * s := by
  classical
  let P : Sylow 2 K := default
  have hp : IsPGroup 2 ((P : Subgroup K).map K.subtype) := P.isPGroup'.map K.subtype
  obtain ⟨Q, hPQ⟩ := hp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G Q S
  obtain ⟨s, hs, k, hk, hck⟩ := hprod c
  let kK : K := ⟨k, hk⟩
  let PK : Sylow 2 K := kK • P
  have hPKS : (PK : Subgroup K).map K.subtype ≤ (S : Subgroup G) := by
    rintro x ⟨y, hy, rfl⟩
    change y ∈ ((P : Subgroup K).map (MulAut.conj kK).toMonoidHom) at hy
    obtain ⟨p, hp, rfl⟩ := hy
    have hpQ : (p : G) ∈ Q := hPQ (mem_map_of_mem K.subtype hp)
    have hcp : c * (p : G) * c⁻¹ ∈ S := by
      rw [← hc]
      change c * (p : G) * c⁻¹ ∈ (Q : Subgroup G).map (MulAut.conj c).toMonoidHom
      exact mem_map_of_mem (MulAut.conj c).toMonoidHom hpQ
    have hclosed := (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem
      ((S : Subgroup G).inv_mem hs) hcp) hs
    change k * (p : G) * k⁻¹ ∈ S
    have heq : s⁻¹ * (c * (p : G) * c⁻¹) * s = k * (p : G) * k⁻¹ := by
      rw [hck]
      group
    rw [heq] at hclosed
    exact hclosed
  have hKsolv : Group.IsSolvable K := by
    let _ := hsolv
    infer_instance
  obtain ⟨UK, hUKodd, hUK⟩ := exists_odd_complement_sylow_two hKsolv PK
  let U := UK.map K.subtype
  refine ⟨U, map_subtype_le _, ?_, ?_⟩
  · rw [card_map_of_injective K.subtype_injective]
    exact hUKodd
  · intro g
    obtain ⟨t, ht, a, ha, hga⟩ := hprod g⁻¹
    obtain ⟨pair, hpair, _⟩ := hUK.symm.existsUnique (⟨a⁻¹, K.inv_mem ha⟩ : K)
    let u : G := (pair.1 : K)
    let b : G := (pair.2 : K)
    have hu : u ∈ U := mem_map_of_mem K.subtype pair.1.property
    have hb : b ∈ S := hPKS (mem_map_of_mem K.subtype pair.2.property)
    have hba : u * b = a⁻¹ := congrArg Subtype.val hpair
    refine ⟨u, hu, b * t⁻¹, (S : Subgroup G).mul_mem hb ((S : Subgroup G).inv_mem ht), ?_⟩
    have hg : g = a⁻¹ * t⁻¹ := by
      have he := congrArg Inv.inv hga
      simpa only [inv_inv, mul_inv_rev] using he
    rw [hg, ← hba, mul_assoc]

/-- A transitive Sylow action on a subgroup family gives an odd stabilizer supplement. -/
public theorem exists_odd_stabilizer_supplement
    {G I : Type*} [Group G] [Finite G]
    (C : Subgroup G) (hsolv : Group.IsSolvable C)
    (S : Sylow 2 G) (hSC : (S : Subgroup G) ≤ C)
    (R : I → Subgroup G) (i0 : I)
    (hperm : ∀ c ∈ C, ∃ j, (R i0).map (MulAut.conj c).toMonoidHom = R j)
    (htrans : ∀ j, ∃ s ∈ S, (R i0).map (MulAut.conj s).toMonoidHom = R j) :
    ∃ U : Subgroup G, U ≤ C ⊓ normalizer (R i0 : Set G) ∧
      Odd (Nat.card U) ∧ (C : Set G) = (U : Set G) * (S : Set G) := by
  classical
  let K : Subgroup C := (normalizer (R i0 : Set G)).subgroupOf C
  let SC := S.subtype hSC
  have hprod : ∀ c : C, ∃ s ∈ SC, ∃ k ∈ K, c = s * k := by
    intro c
    obtain ⟨j, hj⟩ := hperm c c.property
    obtain ⟨s, hs, hsj⟩ := htrans j
    let sC : C := ⟨s, hSC hs⟩
    let kC : C := sC⁻¹ * c
    refine ⟨sC, hs, kC, ?_, ?_⟩
    · change s⁻¹ * (c : G) ∈ normalizer (R i0 : Set G)
      apply mem_normalizer_iff_map_conj_eq.mpr
      have heq := congrArg (fun W : Subgroup G => W.map (MulAut.conj s⁻¹).toMonoidHom)
        (hj.trans hsj.symm)
      rw [map_map, map_map] at heq
      have hcomp : (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj (c : G)).toMonoidHom =
          (MulAut.conj (s⁻¹ * (c : G))).toMonoidHom := by
        ext x
        simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
          MulAut.conj_apply]
        group
      have hcancel : (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
          MonoidHom.id G := by
        ext x
        simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
          MulAut.conj_apply, MonoidHom.id_apply]
        group
      rw [hcomp, hcancel, map_id] at heq
      exact heq
    · dsimp only [kC]
      group
  obtain ⟨UC, hUCK, hUCodd, hUCprod⟩ :=
    odd_supplement_of_sylow_stabilizer_product hsolv SC K hprod
  let U := UC.map C.subtype
  refine ⟨U, ?_, ?_, ?_⟩
  · rintro x ⟨u, hu, rfl⟩
    exact ⟨u.property, hUCK hu⟩
  · rw [card_map_of_injective C.subtype_injective]
    exact hUCodd
  · ext g
    constructor
    · intro hg
      obtain ⟨u, hu, s, hs, heq⟩ := hUCprod ⟨g, hg⟩
      exact Set.mem_mul.mpr ⟨u, mem_map_of_mem C.subtype hu, s, hs,
        (congrArg Subtype.val heq).symm⟩
    · rintro ⟨u, ⟨uC, huC, rfl⟩, s, hs, rfl⟩
      exact C.mul_mem uC.property (hSC hs)

end Subgroup

