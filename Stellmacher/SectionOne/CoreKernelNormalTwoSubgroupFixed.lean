module
public import Stellmacher.SectionOne.CoreKernelTransvectionFactor
public import Stellmacher.SectionOne.OneSevenTwoGroupSupportMove
public import Theory.GroupAction.FixedCoatomDisplacement

/-!
# A normal subgroup of a large two-group fixes at most four vectors

For a core-kernel action of a finite solvable group on an elementary group
of order sixteen, a nontrivial subgroup N normal in a two-subgroup S of
order greater than four has at most four fixed vectors. The literal range
of the supplied action and all its inherited actions are retained.

Otherwise its proper fixed subgroup is an S-invariant hyperplane. Any
nonidentity element of N then is a transvection with exactly this fixed
hyperplane. Its canonical factor has a complementary support fixed by the
transvection. A support-exchanging element of S puts both complementary
supports in the invariant hyperplane, contradicting their full span.

This is the normal fixed-space obstruction used in the contained-center
case of Stellmacher (9.10), printed p.59. It does not require a separately
chosen wreath model or an invariant lift of a barred coprime support.
-/
namespace Stellmacher.SectionOne
open scoped IsMulCommutative
universe u

public theorem core_kernel_normal_two_subgroup_fixed_card_le_four
    {P V : Type u} [Group P] [Finite P] [Group V] [Finite V]
    [IsElementaryAbelian 2 V]
    (hsolvable : Group.IsSolvable P) (action : P →* MulAut V)
    (hkernel : action.ker = pCore 2 P) (hV : Nat.card V=16)
    (S N : Subgroup action.range) (hS : IsPGroup 2 S) (hlarge : 4<Nat.card S)
    (_hNS : N≤S) (hnormal : S≤Subgroup.normalizer (N:Set action.range))
    (hN : N≠⊥) : Nat.card (FixedPoints.subgroup N V)≤4 := by
  let X := action.range
  let F := FixedPoints.subgroup N V
  have hFinv : IsInvariant S V F := fixedPoints_isInvariant_of_normalizing_actor S N hnormal
  obtain ⟨n,hn,hnne⟩ := N.bot_or_exists_ne_one.resolve_left hN
  obtain ⟨actor,hactor⟩ := action.rangeRestrict_surjective n
  have hane : action actor≠1 := by
    intro heq
    apply hnne
    rw [←hactor]
    exact Subtype.ext heq
  have hFproper : F≠⊤ := by
    intro htop
    apply hane
    ext point
    have hp : point∈F := htop ▸ Subgroup.mem_top point
    have hh := hp ⟨n,hn⟩
    change (n:MulAut V) point=point at hh
    rw [←hactor] at hh
    exact hh
  by_contra! hnot
  change 4<Nat.card F at hnot
  have hproperCard (J:Subgroup V) (hJ:J≠⊤) : Nat.card J<16 := by
    have htopCard : Nat.card (⊤:Subgroup V)=16 :=
      (Nat.card_congr (Subgroup.topEquiv : (⊤:Subgroup V)≃*V).toEquiv).trans hV
    have hle := Subgroup.card_le_of_le (show J≤⊤ from le_top)
    have hne : Nat.card J≠16 := by
      intro heq
      apply hJ
      apply Subgroup.eq_of_le_of_card_ge le_top
      rw [htopCard,heq]
    rw [htopCard] at hle
    omega
  have hFcard : Nat.card F=8 := by
    have hdvd := F.card_subgroup_dvd_card
    rw [hV] at hdvd
    have hupper : Nat.card F<16 := hproperCard F hFproper
    obtain ⟨power,hpower,heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card F ∣ 2^4 from hdvd)
    have hcases : Nat.card F=1 ∨ Nat.card F=2 ∨ Nat.card F=4 ∨
        Nat.card F=8 ∨ Nat.card F=16 := by
      interval_cases power
      · exact Or.inl heq
      · exact Or.inr (Or.inl heq)
      · exact Or.inr (Or.inr (Or.inl heq))
      · exact Or.inr (Or.inr (Or.inr (Or.inl heq)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr heq)))
    omega
  let A := Subgroup.zpowers (action actor)
  let Fa := FixedPoints.subgroup A V
  have hFFa : F≤Fa := by
    intro point hpoint mover
    obtain ⟨power,hpower⟩ := mover.property
    change (mover:MulAut V) point=point
    rw [←hpower]
    have hh := hpoint ⟨n^power,N.zpow_mem hn power⟩
    change ((n:MulAut V)^power) point=point at hh
    rw [←hactor] at hh
    exact hh
  have hFindex : F.index=2 := by
    have hh := F.card_mul_index
    rw [hFcard,hV] at hh
    omega
  have hindex : Fa.index∣2 := hFindex ▸ Subgroup.index_dvd_of_le hFFa
  have hbound := MulAut.commutatorAction_card_le_two_of_fixed_index_dvd_two
    (action actor) hindex
  have hdispNe : commutatorAction A V≠⊥ := by
    intro hbot
    apply hane
    ext point
    have hh : point⁻¹*(action actor) point∈commutatorAction A V :=
      Subgroup.subset_closure ⟨⟨action actor,Subgroup.mem_zpowers _⟩,point,
        Subgroup.mem_top point,rfl⟩
    rw [hbot,Subgroup.mem_bot] at hh
    exact (inv_mul_eq_one.mp hh).symm
  change Nat.card (commutatorAction A V)≤2 at hbound
  have hrank : Nat.card (commutatorAction A V)=2 := by
    have hh := (Subgroup.one_lt_card_iff_ne_bot _).mpr hdispNe
    omega
  have hFaProper : Fa≠⊤ := by
    intro htop
    apply hane
    ext point
    exact (htop ▸ Subgroup.mem_top point : point∈Fa) ⟨action actor,Subgroup.mem_zpowers _⟩
  have hFaF : Fa=F := by
    apply (Subgroup.eq_of_le_of_card_ge hFFa ?_).symm
    have hidx : Fa.index=2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hindex with hone|htwo
      · exact (hFaProper (Subgroup.index_eq_one.mp hone)).elim
      · exact htwo
    have hh := Fa.card_mul_index
    rw [hidx,hV] at hh
    rw [hFcard]
    omega
  obtain ⟨hyp,hD⟩ := core_kernel_transvection_factor hsolvable action hkernel actor hrank
  let D := ⁅oddCore X,Subgroup.zpowers (action.rangeRestrict actor)⁆ ⊔
    Subgroup.zpowers (action.rangeRestrict actor)
  have haD : action.rangeRestrict actor∈D := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  obtain ⟨b,hmove,hspan⟩ := oneSevenFactor_exists_complementary_two_group_conjugate
    hyp D S hD hS hV hlarge
  let E := D.conjBy (b:X)
  let U := commutatorAction D V
  let U' := commutatorAction E V
  have hE := hD.conjBy D (b:X)
  have hUmap : U.map (MulDistribMulAction.toMulAut X V (b:X)).toMonoidHom=U' :=
    RankOneThreeGroupAssembly.commutatorAction_conjBy D (b:X)
  have hDE : D≠E := by
    intro heq
    apply hmove
    rw [hUmap]
    exact congrArg (fun K:Subgroup X => commutatorAction K V) heq
  have hU'fixed : U'≤FixedPoints.subgroup D V :=
    oneSevenFactor_commutatorAction_le_fixedPoints hyp D E hD hE hDE
  have hU'F : U'≤F := by
    rw [←hFaF]
    intro point hpoint mover
    obtain ⟨power,hpower⟩ := mover.property
    change (mover:MulAut V) point=point
    rw [←hpower]
    exact hU'fixed hpoint ⟨(action.rangeRestrict actor)^power,D.zpow_mem haD power⟩
  have hUF : U≤F := by
    intro point hpoint
    apply (hFinv.invariant b point).mpr
    apply hU'F
    rw [←hUmap]
    exact Subgroup.mem_map_of_mem _ hpoint
  have hspan' : U⊔U'=⊤ := by
    change U ⊔ U.map (MulDistribMulAction.toMulAut X V (b:X)).toMonoidHom=⊤ at hspan
    rwa [hUmap] at hspan
  apply hFproper
  exact top_unique (hspan' ▸ sup_le hUF hU'F)

end Stellmacher.SectionOne
