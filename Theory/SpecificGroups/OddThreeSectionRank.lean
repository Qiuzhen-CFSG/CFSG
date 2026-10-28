module

public import Theory.SpecificGroups.GL2.OddCharacteristicTwoRank
public import GorensteinWalter.PGL2DihedralSylow
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.SingleInvolutionClassSylow
public import Theory.SpecificGroups.SL3.InvolutionConjugacy
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.SpecificGroups.ProjectiveLinearInvolutions

/-!
# Two-rank of sections of odd ternary groups

Every quotient of every subgroup of odd-field PSL₃ or PSU₃ has two-rank
at most three. In GL₂, project a two-subgroup into PGL₂ and place its image
inside a dihedral Sylow subgroup. The inverse image of the cyclic rotation
subgroup is abelian and has index at most two. Its two-rank is at most two,
and this bound persists in its homomorphic images.

The single involution class in SL₃ identifies its Sylow two-subgroups with
those of an involution centralizer GL₂. The odd central projective kernel
preserves these Sylow subgroups. SU₃ embeds in SL₃ over its coefficient
field, and its projective kernel is also odd. Finally, map a Sylow subgroup
of the original subgroup onto a Sylow subgroup of the requested quotient.
No assertion that ordinary two-rank is monotone under quotients is used.

These are the small-degree Sylow-section calculations for Aschbacher--Smith,
A.3.12 and A.3.21(a), printed pp.47--48 and 55, used in 1.2.8(1), p.506.
-/

public section

open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups

namespace Theory.SpecificGroups.OddThreeSectionRank
variable {G H : Type*} [Group G] [Group H] [Finite G]

private theorem abelian_image_rank [IsMulCommutative G] {p : ℕ}
    (hp : IsPGroup p G) (f : G →* H) (hf : Function.Surjective f) :
    primeRank p H ≤ primeRank p G := by
  apply csSup_le'
  rintro n ⟨B,_,_,_,hn⟩
  let A := B.comap f
  exact hn.trans ((Group.rank_le_of_surjective (f.subgroupComap B)
    (f.subgroupComap_surjective_of_surjective B hf)).trans
      (A.rank_le_primeRank p (hp.to_subgroup A)))

/-- All images of a two-subgroup of odd GL₂ have two-rank at most three. -/
theorem gl2_twoGroup_image_twoRank_le_three
    {F : Type*} [Field F] [Finite F]
    (hF : GorensteinWalter.IsOddPrimePower (Nat.card F)) (h2 : (2 : F) ≠ 0)
    (hG : IsPGroup 2 G) (rho : G →* GL (Fin 2) F) (hrho : Function.Injective rho)
    (f : G →* H) (hf : Function.Surjective f) : primeRank 2 H ≤ 3 := by
  let : Finite H := Finite.of_surjective f hf
  let : Finite PGL(2,F) := Finite.of_surjective
    (ProjGenLinGroup.mk : GL (Fin 2) F →* PGL(2,F)) ProjGenLinGroup.mk_surjective
  let g := (ProjGenLinGroup.mk : GL (Fin 2) F →* PGL(2,F)).comp rho
  obtain ⟨S,hS⟩ := (hG.of_surjective g.rangeRestrict g.rangeRestrict_surjective).exists_le_sylow
  obtain ⟨n,_,⟨e⟩⟩ := GorensteinWalter.pgl2_odd_hasDihedralSylowTwo_model F hF S
  let gS : G →* S := g.codRestrict (S : Subgroup PGL(2,F)) (fun x => hS ⟨x,rfl⟩)
  let d := e.toMonoidHom.comp gS
  have hd : d.ker ≤ center G := by
    intro x hx
    have he : e (gS x) = e 1 := by
      rw [map_one]
      exact hx
    have hg : g x = 1 := congrArg Subtype.val (e.injective he)
    have hz : rho x ∈ center (GL (Fin 2) F) := ProjGenLinGroup.mk_eq_one.mp hg
    apply mem_center_iff.mpr
    intro y
    apply hrho
    simpa only [map_mul] using mem_center_iff.mp hz (rho y)
  let R := zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ n))
  have hiR : R.index = 2 := by
    have hc : Nat.card R = 2 ^ n := by
      rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
    have hi := R.card_mul_index
    rw [hc, DihedralGroup.nat_card] at hi
    have hp : 0 < 2 ^ n := pow_pos (by decide) _
    nlinarith
  let A := R.comap d
  have hiA : A.index ≤ 2 := by
    rw [show A = R.comap d from rfl, index_comap]
    calc
      R.relIndex d.range ≤ R.index := by
        simpa only [relIndex_top_right] using
          (relIndex_le_of_le_right (H := R) (K := d.range) (L := ⊤) le_top (by
            simpa only [relIndex_top_right] using R.index_ne_zero_of_finite))
      _ = 2 := hiR
  let : IsMulCommutative A :=
    (d.subgroupComap R).isMulCommutative_of_isCyclic_of_ker_le_center (by
      intro x hx
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      exact mem_center_iff.mp (hd (congrArg Subtype.val (MonoidHom.mem_ker.mp hx))) y)
  have hrA : primeRank 2 A ≤ 2 :=
    (primeRank_le_of_injective 2 (rho.comp A.subtype) (hrho.comp A.subtype_injective)).trans
      (GeneralLinearGroup.twoRank_le_two_of_two_ne_zero F h2)
  have hrAf : primeRank 2 (A.map f) ≤ 2 :=
    (abelian_image_rank (hG.to_subgroup A) (f.subgroupMap A)
      (f.subgroupMap_surjective A)).trans hrA
  have hiAf : (A.map f).index ≤ 2 ^ 1 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero A.index_ne_zero_of_finite)
      (A.index_map_dvd hf)).trans hiA
  have hb := primeRank_le_add_of_index_le (A.map f) hiAf
  omega

omit [Finite G] in
private theorem sl3_two_group_embedding
    {F : Type*} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (hG : IsPGroup 2 G) (rho : G →* SL(3,F)) (hrho : Function.Injective rho) :
    ∃ j : G →* GL (Fin 2) F, Function.Injective j := by
  obtain ⟨S,hS⟩ := (hG.of_surjective rho.rangeRestrict rho.rangeRestrict_surjective).exists_le_sylow
  let P : Sylow 2 (GL (Fin 2) F) := Classical.choice inferInstance
  have hi := odd_index_centralizer_of_one_involution_class
    (SL3.standardInvolution F) (SL3.standardInvolution_orderOf F h2)
    (fun z hz => SL3.involution_isConj_standard F z hz h2)
  obtain ⟨e⟩ := sylow_equiv_of_odd_index _ hi
    (SL3.standardInvolutionCentralizerEquiv F h2).symm S P
  let r : G →* S := rho.codRestrict (S : Subgroup SL(3,F)) (fun x => hS ⟨x,rfl⟩)
  have hir : Function.Injective r := fun x y he => hrho (congrArg Subtype.val he)
  refine ⟨(P : Subgroup _).subtype.comp (e.toMonoidHom.comp r), ?_⟩
  intro x y he
  exact hir (e.injective (Subtype.ext he))

omit [Finite G] in
private theorem cover_two_group_embedding
    {F E X : Type*} [Field F] [Finite F] [Group E] [Finite E]
    [Group X] [Finite X] (h2 : (2 : F) ≠ 0)
    (r : E →* SL(3,F)) (hr : Function.Injective r)
    (q : E →* G) (hq : Function.Surjective q)
    (hk : Nat.Coprime 2 (Nat.card q.ker))
    (hX : IsPGroup 2 X) (i : X →* G) (hi : Function.Injective i) :
    ∃ j : X →* GL (Fin 2) F, Function.Injective j := by
  obtain ⟨T,hT⟩ := (hX.of_surjective i.rangeRestrict i.rangeRestrict_surjective).exists_le_sylow
  let S : Sylow 2 E := Classical.choice inferInstance
  let e : S ≃* T := Sylow.equivOfSurjectiveCoprime q hq hk S T
  let iT : X →* T := i.codRestrict (T : Subgroup G) (fun x => hT ⟨x,rfl⟩)
  let j := r.comp ((S : Subgroup E).subtype.comp (e.symm.toMonoidHom.comp iT))
  have hj : Function.Injective j := by
    intro x y he
    apply hi
    have he' : e.symm (iT x) = e.symm (iT y) := Subtype.ext (hr he)
    exact congrArg Subtype.val (e.symm.injective he')
  exact sl3_two_group_embedding h2 hX j hj

private theorem cover_subgroup_quotient_rank
    {F E : Type*} [Field F] [Finite F] [Group E] [Finite E]
    (hF : GorensteinWalter.IsOddPrimePower (Nat.card F)) (h2 : (2 : F) ≠ 0)
    (r : E →* SL(3,F)) (hr : Function.Injective r)
    (q : E →* G) (hq : Function.Surjective q)
    (hk : Nat.Coprime 2 (Nat.card q.ker))
    (P : Subgroup G) (N : Subgroup P) [N.Normal] :
    primeRank 2 (P ⧸ N) ≤ 3 := by
  let T : Sylow 2 P := Classical.choice inferInstance
  let i : T →* G := P.subtype.comp (T : Subgroup P).subtype
  have hi : Function.Injective i := P.subtype_injective.comp (T : Subgroup P).subtype_injective
  obtain ⟨j,hj⟩ := cover_two_group_embedding h2 r hr q hq hk T.isPGroup' i hi
  let f := QuotientGroup.mk' N
  let S := T.mapSurjective (QuotientGroup.mk'_surjective N)
  rw [S.primeRank_eq]
  exact gl2_twoGroup_image_twoRank_le_three hF h2 T.isPGroup' j hj
    (f.subgroupMap (T : Subgroup P)) (f.subgroupMap_surjective _)

open BenderSuzuki.MatrixGroups in
private def unitary_to_sl {F : Type*} [Field F] (J : HermitianForm 3 F) :
    J.specialSubgroup →* SL(3,F) where
  toFun x := ⟨x.val.val, congrArg Units.val x.property.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

open BenderSuzuki.MatrixGroups in
private theorem unitary_to_sl_injective {F : Type*} [Field F] (J : HermitianForm 3 F) :
    Function.Injective (unitary_to_sl J) := by
  intro x y h
  exact Subtype.ext (Units.ext (congrArg Subtype.val h))

private theorem odd_field_prime_power
    (F : Type*) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    GorensteinWalter.IsOddPrimePower (Nat.card F) := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hc : Nat.card F = ringChar F ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hn
  refine ⟨ringChar F, n, hp, ?_, n.pos, hc⟩
  apply hp.odd_of_ne_two
  intro heq
  rw [heq] at hc
  have heven : Even (Nat.card F) := by
    rw [hc]
    exact Nat.even_pow.mpr ⟨by decide, n.pos.ne'⟩
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- Every subgroup quotient of odd-field PSL₃ has two-rank at most three. -/
theorem psl3_subgroup_quotient_twoRank_le_three
    {F : Type*} [Field F] [Finite F] (ho : Odd (Nat.card F))
    (P : Subgroup PSL(3,F)) (N : Subgroup P) [N.Normal] :
    primeRank 2 (P ⧸ N) ≤ 3 := by
  apply cover_subgroup_quotient_rank (odd_field_prime_power F ho)
    (Field.two_ne_zero_of_odd_card F ho) (MonoidHom.id SL(3,F)) Function.injective_id
    (PSL3.projection F) (PSL3.projection_surjective F)
  rw [PSL3.projection_ker]
  exact (SL3.odd_card_center F).coprime_two_left

open BenderSuzuki.MatrixGroups in
/-- Every subgroup quotient of odd-field PSU₃ has two-rank at most three. -/
theorem psu3_subgroup_quotient_twoRank_le_three
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (ho : Odd (Nat.card F))
    (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (N : Subgroup P) [N.Normal] : primeRank 2 (P ⧸ N) ≤ 3 := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  exact cover_subgroup_quotient_rank (odd_field_prime_power F ho)
    (Field.two_ne_zero_of_odd_card F ho) (unitary_to_sl J) (unitary_to_sl_injective J)
    J.specialToProjective J.specialToProjective_surjective
    J.odd_card_specialToProjective_ker.coprime_two_left P N

end Theory.SpecificGroups.OddThreeSectionRank
