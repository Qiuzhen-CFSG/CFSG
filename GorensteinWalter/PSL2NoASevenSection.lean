module
public import GorensteinWalter.PSL2NotASeven
public import Theory.SpecificGroups.DihedralSolvable
public import GorensteinWalter.PSL2CoreModelFacts
public import Glauberman.DicksonClassification
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.GroupTheory.Solvable

/-!
# Odd PSL2 has no alternating-seven section

No subgroup of PSL2 over an odd finite field surjects onto A7. The quotient
kernel is arbitrary; this is stronger than excluding central quotients.

Apply the actual nine-case Dickson subgroup classification. The elementary,
cyclic, dihedral and elementary-by-cyclic cases are solvable; the A4, S4
and A5 cases are too small. A PSL2 subfield group has order12 at field
order three; at larger orders it is simple, so a surjection onto A7 would
be an isomorphism, excluded by the exact order formula. For a PGL2 subfield
group, perfection of A7 makes the restriction to the derived PSL2 subgroup
surjective, including the field-order-three case.

This supplies the arbitrary-section exclusion cited in ABG II.3 Lemma2,
article p24, from the Gorenstein--Walter Dickson lemma. It uses no assumption
that the quotient kernel is central and no later ABG structure theorem.
-/

namespace GorensteinWalter
universe u

private theorem no_a7_of_small {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G < 2520) (f : G →* alternatingGroup (Fin 7))
    (hf : Function.Surjective f) : False := by
  have h := Nat.le_of_dvd (Nat.card_pos (α := G)) (Subgroup.card_dvd_of_surjective f hf)
  have hA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]
    norm_num
  omega

private theorem no_a7_of_solvable {G : Type*} [Group G] [Group.IsSolvable G]
    (f : G →* alternatingGroup (Fin 7)) (hf : Function.Surjective f) : False := by
  let : Group.IsPerfect (alternatingGroup (Fin 7)) :=
    ⟨commutator_alternatingGroup_eq_top (by norm_num)⟩
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 7))
    (Group.isSolvable_of_surjective hf)

private theorem solvable_semidirect {G : Type*} [Group G]
    (N C : Subgroup G) [N.Normal] [Group.IsSolvable N] [IsCyclic C]
    (hsup : N ⊔ C = ⊤) : Group.IsSolvable G := by
  let q := QuotientGroup.mk' N
  let f : C →* G ⧸ N := q.comp C.subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hg : g ∈ N ⊔ C := by rw [hsup]; trivial
    obtain ⟨n, hn, c, hc, hgc⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := N) (t := C)).mp hg
    have hqn : q n = 1 := (QuotientGroup.eq_one_iff (N := N) n).mpr hn
    refine ⟨⟨c, hc⟩, ?_⟩
    change q c = q g
    rw [← hgc, map_mul, hqn, one_mul]
  let : IsCyclic (G ⧸ N) := isCyclic_of_surjective f hf
  let : CommGroup (G ⧸ N) := IsCyclic.commGroup
  exact (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance, inferInstance⟩

private theorem no_a7_of_psl2 (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (f : PSL2 K →* alternatingGroup (Fin 7))
    (hf : Function.Surjective f) : False := by
  have h3 := odd_prime_power_three_le _ hK
  by_cases hsmall : Nat.card K = 3
  · apply no_a7_of_small (G := PSL2 K) _ f hf
    rw [psl2_card_formula K hK, hsmall]
    norm_num
  let : IsSimpleGroup (PSL2 K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker inferInstance with hbot | htop
  · exact psl2_ne_a7 hK ⟨MulEquiv.ofBijective f ⟨(MonoidHom.ker_eq_bot_iff f).mp hbot, hf⟩⟩
  · obtain ⟨t, ht⟩ := exists_ne (1 : alternatingGroup (Fin 7))
    obtain ⟨x, rfl⟩ := hf t
    exact ht (show f x = 1 from show x ∈ f.ker by rw [htop]; trivial)

private theorem no_a7_of_pgl2 (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (f : PGL2 K →* alternatingGroup (Fin 7))
    (hf : Function.Surjective f) : False := by
  let : Finite (PGL2 K) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  let C := commutator (PGL2 K)
  have hmap : C.map f = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    exact commutator_alternatingGroup_eq_top (by norm_num)
  let g : C →* alternatingGroup (Fin 7) := f.comp C.subtype
  have hg : Function.Surjective g := by
    intro y
    have hy : y ∈ C.map f := by rw [hmap]; trivial
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  let e := (commutator_mulEquiv_psl2_of_mulEquiv_pgl2 K hK (MulEquiv.refl _)).some
  exact no_a7_of_psl2 K hK (g.comp e.symm.toMonoidHom)
    (hg.comp e.symm.surjective)

public theorem no_surjective_subgroup_a7_of_psl2_odd
    (F : Type u) [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (U : Subgroup (PSL2 F)) (f : U →* alternatingGroup (Fin 7))
    (hf : Function.Surjective f) : False := by
  obtain ⟨p, n, hp, hpodd, hn, hcard⟩ := hF
  let : Fact p.Prime := ⟨hp⟩
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hcard U with
    hEl | hCy | hDi | hA4 | hS4 | hA5 | hSemi | hPSL | hPGL
  · let : IsElementaryAbelian p U := hEl
    let : Group.IsSolvable U := Group.isSolvable_of_comm
      (fun a b => IsMulCommutative.is_comm.comm a b)
    exact no_a7_of_solvable f hf
  · obtain ⟨z, _, _, hcyc⟩ := hCy
    let : IsCyclic U := hcyc
    let : CommGroup U := IsCyclic.commGroup
    exact no_a7_of_solvable f hf
  · obtain ⟨z, _, _, ⟨e⟩⟩ := hDi
    let : Group.IsSolvable (DihedralGroup z) := GLS3.Chapter5.dihedralGroup_isSolvable z
    exact no_a7_of_solvable (f.comp e.symm.toMonoidHom) (hf.comp e.symm.surjective)
  · obtain ⟨_, ⟨e⟩⟩ := hA4
    apply no_a7_of_small (G := U) _ f hf
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  · obtain ⟨_, ⟨e⟩⟩ := hS4
    apply no_a7_of_small (G := U) _ f hf
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  · obtain ⟨_, ⟨e⟩⟩ := hA5
    apply no_a7_of_small (G := U) _ f hf
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  · obtain ⟨m, t, _, _, N, C, hN, hEl, _, hC, _, _, hsup⟩ := hSemi
    let : N.Normal := hN
    let : IsElementaryAbelian p N := hEl
    let : IsCyclic C := hC
    let : Group.IsSolvable N := Group.isSolvable_of_comm
      (fun a b => IsMulCommutative.is_comm.comm a b)
    let : Group.IsSolvable U := solvable_semidirect N C hsup
    exact no_a7_of_solvable f hf
  · obtain ⟨m, hm, _, ⟨e⟩⟩ := hPSL
    have hK : IsOddPrimePower (Nat.card (GaloisField p m)) :=
      ⟨p, m, hp, hpodd, Nat.pos_of_ne_zero hm, GaloisField.card p m hm⟩
    exact no_a7_of_psl2 (GaloisField p m) hK
      (f.comp e.symm.toMonoidHom) (hf.comp e.symm.surjective)
  · obtain ⟨m, hm, _, ⟨e⟩⟩ := hPGL
    have hK : IsOddPrimePower (Nat.card (GaloisField p m)) :=
      ⟨p, m, hp, hpodd, Nat.pos_of_ne_zero hm, GaloisField.card p m hm⟩
    exact no_a7_of_pgl2 (GaloisField p m) hK
      (f.comp e.symm.toMonoidHom) (hf.comp e.symm.surjective)

end GorensteinWalter

