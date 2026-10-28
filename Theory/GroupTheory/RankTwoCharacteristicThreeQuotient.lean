module

public import Theory.GroupTheory.RankTwoCentralInvolutionQuotient
public import Theory.GroupTheory.RankTwoOddQuotient
public import Theory.GroupTheory.PCorePreimageCentralizer
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.ThreeSectionReducibility.Reduction
public import CFSG.Quasithin.ChapterA.Section01.RankActions.AutomorphismQuotient
public import Theory.SpecificGroups.GL2.ThreeScalarOrNormalSylow
public import Theory.SpecificGroups.GL2.ThreeResidualAutomorphisms

/-!
# Noncyclic abelian cubic quotients in characteristic three

A finite group of characteristic three and three-rank at most two has a
three-group kernel in its small automorphism representation. Thus its
quotient by the full three-core embeds in GL₂(3). A nontrivial subgroup
of GL₂(3) with trivial three-core has a central involution: otherwise its
order divides six and its normal Sylow three-subgroup is trivial.

Lift this central involution through the three-core. It moves that core
by characteristic three, so the central-involution quotient theorem makes
every abelian three-group quotient cyclic. Consequently a noncyclic such
quotient forces the original group to be a three-group.

The final theorem retains rank on an arbitrary finite covering group.
Reduction to a three-group covering kernel preserves that rank, and
characteristic three lifts through the resulting surjection.
-/

public noncomputable section
open Subgroup Matrix
open scoped IsMulCommutative
namespace Theory.GroupTheory

private theorem central_involution_of_core_free_linear_embedding
    {X : Type*} [Group X] [Finite X] [Nontrivial X]
    (g : X →* GL (Fin 2) (ZMod 3)) (hg : Function.Injective g)
    (hcore : pCore 3 X = ⊥) :
    ∃ z : X, orderOf z = 2 ∧ z ∈ center X := by
  let e : X ≃* g.range := MonoidHom.ofInjective hg
  have hRcore : pCore 3 g.range = ⊥ := by
    rw [←pCore_map_iso 3 e,hcore,Subgroup.map_bot]
  have hex : ∃ z : g.range, orderOf z = 2 ∧ z ∈ center g.range := by
    by_cases hz : GeneralLinearGroup.threeCentral ∈ g.range
    · let z : g.range := ⟨GeneralLinearGroup.threeCentral,hz⟩
      refine ⟨z,(orderOf_injective g.range.subtype g.range.subtype_injective z).symm.trans
        GeneralLinearGroup.threeCentral_order,?_⟩
      apply mem_center_iff.mpr
      intro x
      apply Subtype.ext
      apply Units.ext
      have hh : ∀ a : Matrix (Fin 2) (Fin 2) (ZMod 3),
          a * GeneralLinearGroup.threeCentral.val =
            GeneralLinearGroup.threeCentral.val * a := by decide +kernel
      exact hh x.val.val
    · obtain ⟨P,hP⟩ := (GeneralLinearGroup.three_scalar_or_normal_sylow g.range).resolve_left hz
      let : (P : Subgroup g.range).Normal := hP
      have hPle : (P : Subgroup g.range) ≤ pCore 3 g.range := le_sSup ⟨hP,P.isPGroup'⟩
      have hPbot : (P : Subgroup g.range) = ⊥ := bot_unique (hPle.trans_eq hRcore)
      have hnd : ¬3 ∣ Nat.card g.range := by
        simpa only [hPbot,index_bot] using P.not_dvd_index
      have hd := GeneralLinearGroup.three_card_dvd_six_of_scalar_not_mem g.range hz
      have hcases : Nat.card g.range = 1 ∨ Nat.card g.range = 2 := by
        have hh : Nat.card g.range ∈ Nat.divisors 6 := Nat.mem_divisors.mpr ⟨hd,by decide⟩
        have he : Nat.divisors 6 = {1,2,3,6} := by decide
        rw [he] at hh
        simp only [Finset.mem_insert,Finset.mem_singleton] at hh
        rcases hh with h | h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact (hnd (by rw [h])).elim
        · exact (hnd (by rw [h]; decide)).elim
      have hc : Nat.card g.range = 2 := hcases.resolve_left (fun h => by
        have hx := Finite.one_lt_card (α := X)
        rw [Nat.card_congr e.toEquiv,h] at hx
        omega)
      let : IsCyclic g.range := isCyclic_of_prime_card hc
      obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := g.range) 2 (by rw [hc])
      exact ⟨z,hz,mem_center_iff.mpr (fun x => mul_comm' x z)⟩
  obtain ⟨z,hz,hzc⟩ := hex
  refine ⟨e.symm z,(orderOf_injective e.toMonoidHom e.injective (e.symm z)).symm.trans
    (by change orderOf (e (e.symm z)) = 2; rwa [e.apply_symm_apply]),?_⟩
  apply mem_center_iff.mpr
  intro x
  apply e.injective
  simpa only [map_mul,e.apply_symm_apply] using mem_center_iff.mp hzc (e x)

private theorem three_group_of_characteristic_three_of_rank_two
    {A D : Type*} [Group A] [Finite A] [Group D] [IsMulCommutative D]
    (hrank : primeRank 3 A ≤ 2)
    (hself : centralizer (pCore 3 A : Set A) ≤ pCore 3 A)
    (q : A →* D) (hq : Function.Surjective q) (hD : IsPGroup 3 D)
    (hnoncyclic : ¬IsCyclic D) : IsPGroup 3 A := by
  classical
  let Q := pCore 3 A
  by_contra hn
  have hQtop : Q ≠ ⊤ := by
    intro he
    have hp : IsPGroup 3 (⊤ : Subgroup A) := he ▸ pCore_isPGroup
    exact hn (hp.of_equiv topEquiv)
  let : Nontrivial (A ⧸ Q) := QuotientGroup.nontrivial_iff.mpr hQtop
  let a : A →* MulAut Q := MulAut.conjNormal
  have ha : IsPGroup 3 a.ker := by
    rw [show a.ker = centralizer (Q : Set A) from MulAut.conjNormal_ker_eq_centralizer Q]
    exact (pCore_isPGroup (p := 3) (G := A)).to_le hself
  obtain ⟨r,hr⟩ := CFSG.Quasithin.ChapterA.RankActions.smallRankAutomorphismRepresentation
    3 (by decide) Q pCore_isPGroup ((primeRank_subgroup_le 3 Q).trans hrank)
  have hker : IsPGroup 3 (r.comp a).ker := by
    rw [←MonoidHom.comap_ker]
    exact hr.comap_of_ker_isPGroup a ha
  obtain ⟨g,hg⟩ := (r.comp a).exists_injective_pCore_quotient_of_not_sq_dvd hker
    GeneralLinearGroup.prime_sq_not_dvd_card
  let π := QuotientGroup.mk' Q
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have hπker : IsPGroup 3 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hcore : pCore 3 (A ⧸ Q) = ⊥ := by
    have hh := congrArg (Subgroup.map π) (π.comap_pCore_of_ker_isPGroup hπ hπker)
    rw [map_comap_eq_self_of_surjective hπ] at hh
    exact hh.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))
  obtain ⟨z,hz,hzc⟩ := central_involution_of_core_free_linear_embedding g hg hcore
  have hodd : Nat.Coprime 2 (Nat.card Q) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := A)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_right n
  let S : Sylow 2 A := Classical.choice inferInstance
  obtain ⟨t,ht,_,_,htz,_⟩ :=
    exists_sylow_central_involution_supplement_of_odd_quotient Q hodd S z hz hzc
  have hmove : t ∉ centralizer (Q : Set A) := by
    intro hc
    have htQ : t ∈ Q := hself hc
    have ho := (pCore_isPGroup (p := 3) (G := A)).orderOf_coprime
      (by decide : Nat.Coprime 3 2) (⟨t,htQ⟩ : Q)
    rw [←Subgroup.orderOf_coe (⟨t,htQ⟩ : Q),ht] at ho
    norm_num at ho
  exact hnoncyclic (cyclic_abelian_three_quotient_of_central_involution
    (MonoidHom.id A) Function.surjective_id hrank q hq hD Q pCore_isPGroup t ht
      (htz ▸ hzc) hmove)

/-- A characteristic-three image of a rank-two cover with a noncyclic
abelian three-group quotient is itself a three-group. -/
theorem isThreeGroup_of_characteristic_three_of_noncyclic_abelian_quotient
    {B A D : Type*} [Group B] [Finite B] [Group A] [Finite A]
    [Group D] [IsMulCommutative D]
    (cover : B →* A) (hcover : Function.Surjective cover) (hrank : primeRank 3 B ≤ 2)
    (hself : centralizer (pCore 3 A : Set A) ≤ pCore 3 A)
    (q : A →* D) (hq : Function.Surjective q) (hD : IsPGroup 3 D)
    (hnoncyclic : ¬IsCyclic D) : IsPGroup 3 A := by
  obtain ⟨C,_,_,g,hg,hr,hker⟩ := ThreeSection.exists_three_kernel_cover hrank cover hcover
  have hc := g.centralizer_pCore_le_of_surjective_pKernel hg hker hself
  exact (three_group_of_characteristic_three_of_rank_two hr hc
    (q.comp g) (hq.comp hg) hD hnoncyclic).of_surjective g hg

end Theory.GroupTheory
