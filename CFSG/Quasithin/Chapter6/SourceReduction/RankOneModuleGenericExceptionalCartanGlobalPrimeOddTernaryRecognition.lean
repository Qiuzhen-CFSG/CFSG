module
public import CFSG.Quasithin.ChapterF.Section01.RankOneOddPrime
public import CFSG.Quasithin.ChapterF.Section01.SourceStarredParabolic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeFiveSection
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import Theory.SpecificGroups.SL2.SmallOddComparisons
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.OddBenderOdd
public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.SpecificGroups.SU3.EvenInvolutionResidual
public import Theory.SpecificGroups.PSL2.RootTwoRank
public import Theory.SpecificGroups.Suzuki.TwoRank
public import Theory.SpecificGroups.PSL2.PrimePerfectCore

/-!
# Rank-one sections in odd ternary containers

A perfect subgroup normalized by a full Sylow in prime-field PSL₃ or PSU₃,
with simple source rank-one two-core quotient, has quotient PSL₂(4).
If the subgroup's two-core is nontrivial, the rank-two bound supplies a
central involution; its literal centralizer lifts the perfect subgroup to
SL₂ over the prime field. Dickson recognition and the odd-prime overlap of
the source rank-one models give PSL₂(4). If the two-core is trivial, the
ambient two-rank and cyclic Sylow commutator exclude all other Bender models.

For SL₃ and SU₃, the actual projective kernel is a three-group. Its
intersection with the perfect subgroup is also a two-group, so projection
is injective on that subgroup. No scalar kernel or special-unitary carrier
is silently identified with its projective quotient.

Source: Aschbacher–Smith A.3.12(9), A.3.21(a), F.1.1 and 5.2.2,
printed pp.47–48,55,259,648–649 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime.OddTernary

private theorem no_unitary_cyclic_derived
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hcyc : ∀ S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      IsCyclic (commutator S)) : False := by
  let S := HermitianForm.EvenTwoRank.rootSylow J hJ (by omega) hcard hfixed
  let e := HermitianForm.SylowOmega.projectiveSylowEquivCoords J hn hcard hfixed hJ S
  let : IsCyclic (commutator (BenderSuzuki.External.hermitianUnipotentCoord J)) :=
    derived_cyclic_of_surjective e.toMonoidHom e.surjective (hcyc S)
  let : IsCyclic (center (BenderSuzuki.External.hermitianUnipotentCoord J)) :=
    isCyclic_of_le (_root_.SU3.EvenInvolutionResidual.root_structure J (2^n) hcard hfixed hJ).2.2
  let : IsCyclic (center S) := isCyclic_of_injective (centerCongr e).toMonoidHom (centerCongr e).injective
  obtain ⟨he,hE,hc⟩ := HermitianForm.SylowOmega.projective_sylow_omega J hn hcard hfixed hJ S
  let := hE
  have hcy : IsCyclic (omegaOneAmbient (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) := by
    rw [he]
    exact isCyclic_of_surjective ((S : Subgroup _).subtype.subgroupMap (center S))
      ((S : Subgroup _).subtype.subgroupMap_surjective _)
  have hd := IsElementaryAbelian.exponent_dvd_p 2
    (omegaOneAmbient (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)))
  rw [hcy.exponent_eq_card,hc] at hd
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
  have hge := Nat.pow_le_pow_right (by decide : 0 < 2) hn
  norm_num at hge
  omega

private theorem four_of_rank_two_cyclic_derived
    {Y : Type*} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hm : ChapterF.Source.IsRankOneModel Y) (hns : ¬ Group.IsSolvable Y)
    (hr : primeRank 2 Y ≤ 2)
    (hcyc : ∀ S : Sylow 2 Y, IsCyclic (commutator S)) :
    ClassicalGroup.IsPSL Y 2 4 := by
  rcases hm.simple_bender hns with ⟨n,hn,⟨e⟩⟩ | ⟨m,hm,⟨e⟩⟩ |
      ⟨n,hn,E,_,_,J,hJ,hcard,hfixed,⟨e⟩⟩
  · have hc : Nat.card (GaloisField 2 n) = 2^n := GaloisField.card 2 n (by omega)
    have hrn : n ≤ 2 := by
      rw [primeRank_equiv 2 e] at hr
      exact (Theory.PSL2.root_two_rank_ge _ hc).trans hr
    have he : n = 2 := by omega
    exact ⟨GaloisField 2 n,inferInstance,inferInstance,by simpa [he] using hc,⟨e⟩⟩
  · rw [primeRank_equiv 2 e,suzuki_two_rank m (by omega)] at hr
    omega
  · exact (no_unitary_cyclic_derived J hn hJ hcard hfixed
      (sylow_derived_cyclic_of_surjective e.toMonoidHom e.surjective hcyc)).elim

private theorem four_of_five {Y : Type*} [Group Y]
    (e : Y ≃* alternatingGroup (Fin 5)) : ClassicalGroup.IsPSL Y 2 4 := by
  have hc : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]; norm_num
  exact ⟨GaloisField 2 2,inferInstance,inferInstance,hc,
    ⟨e.trans (ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc).some.symm⟩⟩

private theorem four_of_prime_sl2
    {Y : Type*} {F : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    [IsSimpleGroup (Y ⧸ pCore 2 Y)] [Field F] [Finite F]
    (hm : ChapterF.Source.IsRankOneModel (Y ⧸ pCore 2 Y))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hF : Nat.card F = p)
    (i : Y →* SL(2,F)) (hi : Function.Injective i) :
    ClassicalGroup.IsPSL (Y ⧸ pCore 2 Y) 2 4 := by
  let g := (GorensteinWalter.sl2ProjectiveProjection F).comp i
  have hk : IsPGroup 2 g.ker := by
    change IsPGroup 2 ((GorensteinWalter.sl2ProjectiveProjection F).ker.comap i)
    exact (GorensteinWalter.sl2ProjectiveProjection_ker_isPGroup F (hF.symm ▸ ho)).comap_of_injective i hi
  let : Group.IsNilpotent g.ker := hk.isNilpotent
  let : Group.IsSolvable g.rangeRestrict.ker := by rw [MonoidHom.ker_rangeRestrict]; infer_instance
  let : Group.IsPerfect g.range := Group.IsPerfect.range g
  let a := PerfectCoreTwoExtension.solvableKernelQuotientEquiv g.rangeRestrict g.rangeRestrict_surjective
  let e : (Y ⧸ pCore 2 Y) ≃* g.range := a.trans
    ((QuotientGroup.quotientMulEquivOfEq (Theory.PSL2.prime_perfect_subgroup_twoCore_eq_bot ho hF g.range)).trans
      QuotientGroup.quotientBot)
  let : Nontrivial g.range := e.symm.nontrivial
  have hns := Group.IsPerfect.not_isSolvable g.range
  by_cases ht : g.range = ⊤
  · let b := e.trans ((MulEquiv.subgroupCongr ht).trans topEquiv)
    have hnsF : ¬ Group.IsSolvable PSL(2,F) := by
      intro hh; let := hh; exact hns inferInstance
    have hlarge := ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
      (hF.symm ▸ ho) hnsF
    have hp5 := hm.odd_prime_parameter (by
      intro hh; let := hh
      exact hns (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective))
      Fact.out ho (by omega)
      ⟨F,inferInstance,inferInstance,hF,⟨b⟩⟩
    exact ⟨GaloisField 2 2,inferInstance,inferInstance,by
      rw [GaloisField.card 2 2 (by decide)]; norm_num,
      ⟨b.trans (ProjectiveSpecialLinearGroup.cardFiveEquivFour (hF.trans hp5))⟩⟩
  · exact four_of_five (e.trans
      (Theory.PSL2.prime_nonsolvable_proper_is_alternating_five ho hF g.range ht hns).2.2.some)

private theorem four_of_cubic_centralizer
    {Y V H F : Type*} {E : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    [IsSimpleGroup (Y ⧸ pCore 2 Y)] [Group V] [Group H] [Field F] [Field E] [Finite E]
    (hm : ChapterF.Source.IsRankOneModel (Y ⧸ pCore 2 Y))
    (ρ : V →* GL (Fin 2) F) (hρ : Function.Injective ρ)
    (f : V →* H) (hf : Function.Surjective f) (hk : f.ker ≤ center V)
    (h3 : ∀ v ∈ f.ker, v ^ 3 = 1)
    (d : (GeneralLinearGroup.det.comp ρ).ker ≃* SL(2,E))
    (j : Y →* H) (hj : Function.Injective j)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hE : Nat.card E = p) :
    ClassicalGroup.IsPSL (Y ⧸ pCore 2 Y) 2 4 := by
  let : Nontrivial Y := (QuotientGroup.mk'_surjective (pCore 2 Y)).nontrivial
  let e : Y ≃* j.range := MonoidHom.ofInjective hj
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  have hn : ¬ IsMulCommutative V := by
    intro ha
    have hh : IsMulCommutative H := IsMulCommutative.of_comm (fun x y => by
      obtain ⟨x,rfl⟩ := hf x
      obtain ⟨y,rfl⟩ := hf y
      rw [←map_mul,←map_mul,ha.is_comm.comm x y])
    exact Group.IsPerfect.not_isMulCommutative Y (IsMulCommutative.of_comm
      (fun x y => hj (by rw [map_mul,map_mul,hh.is_comm.comm])))
  let D := (GeneralLinearGroup.det.comp ρ).ker
  let a : D ≃* D.map f := MulEquiv.ofBijective (f.subgroupMap D)
    ⟨Theory.SpecificGroups.OddThreeLevi.determinant_kernel_injective ρ hρ hn f hk h3,
      f.subgroupMap_surjective D⟩
  have hB : j.range ≤ D.map f :=
    Theory.SpecificGroups.OddThreeLevi.perfect_subgroup_le_det_kernel_image ρ f hf j.range
  let i := d.toMonoidHom.comp (a.symm.toMonoidHom.comp ((inclusion hB).comp e.toMonoidHom))
  exact four_of_prime_sl2 hm ho hE i
    (d.injective.comp (a.symm.injective.comp ((inclusion_injective hB).comp e.injective)))

private def centralizer_embedding {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (B : Subgroup G) (z : G)
    (hz : B ≤ centralizer ({z} : Set G)) :
    B →* centralizer ({e z} : Set H) :=
  (e.toMonoidHom.comp B.subtype).codRestrict _ (by
    intro b
    apply mem_centralizer_singleton_iff.mpr
    simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,Subgroup.coe_subtype,
      ←map_mul] using congrArg e (mem_centralizer_singleton_iff.mp (hz b.property)))

private theorem centralizer_embedding_injective {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (B : Subgroup G) (z : G) (hz : B ≤ centralizer ({z} : Set G)) :
    Function.Injective (centralizer_embedding e B z hz) := by
  intro a b h
  exact Subtype.ext (e.injective (congrArg Subtype.val h))

private theorem projective_four
    {Y : Type*} [Group Y] [Finite Y] (S : Sylow 2 Y) (B : Subgroup Y)
    [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hn : (S : Subgroup Y) ≤ normalizer (B : Set Y))
    (hmodel : ChapterF.Source.IsRankOneModel (B ⧸ pCore 2 B))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hm : ClassicalGroup.IsPSL Y 3 p ∨ ClassicalGroup.IsPSU Y 3 p) :
    ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4 := by
  have hr : primeRank 2 Y ≤ 2 := by
    rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,J,hF,hc,⟨e⟩⟩
    · rw [primeRank_congr 2 e]
      exact Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le Fact.out ho hF
    · rw [primeRank_congr 2 e]
      exact Theory.SpecificGroups.OddThreeRank.psu3_primeRank_two_le J Fact.out ho hF hc
  by_cases hcore : pCore 2 B = ⊥
  · let e : B ≃* (B ⧸ pCore 2 B) :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hcore).symm
    let : IsSimpleGroup B := e.isSimpleGroup
    have hcyc : ∀ P : Sylow 2 Y, IsCyclic (commutator P) := by
      apply ChapterA.Section03.SourceEmbeddings.AlternatingEight.odd_model_sylow_derived_cyclic
      rcases hm with hh | hh
      · exact .linear_three p Fact.out ho hh
      · exact .unitary_three p Fact.out ho hh
    exact (four_of_rank_two_cyclic_derived (hmodel.of_equiv e)
      (Group.IsPerfect.not_isSolvable B)
      ((_root_.primeRank_le_of_injective 2 B.subtype B.subtype_injective).trans hr)
      (sylow_derived_cyclic_of_injective B.subtype B.subtype_injective hcyc)).of_mulEquiv e.symm
  · obtain ⟨z,_,hz,hBz⟩ := exists_involution_centralized_by_perfect_sup_sylow S B hr hn hcore
    have hBz := le_sup_left.trans hBz
    rcases hm with hm | hm
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      have h2 := Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho
        (k := 1) (by simpa using hF)
      obtain ⟨f,hf,hk,h3⟩ := PSL3.OddInvolutionFixed.exists_gl2_cubic_central_surjection
        (e z) ((e.orderOf_eq z).trans hz) h2
      exact four_of_cubic_centralizer hmodel (MonoidHom.id _) Function.injective_id
        f hf hk h3 (SpecialLinearGroup.determinantKernelEquiv (Fin 2) F).symm
        (centralizer_embedding e B z hBz) (centralizer_embedding_injective e B z hBz) ho hF
    · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
      obtain ⟨f,hf,hk,h3⟩ := SU3.OddCubicCentralizer.surjection p ho F J hF hc
        (e z) ((e.orderOf_eq z).trans hz)
      let J2 := ABG.unitaryForm 2 p 1 one_ne_zero
      let d : J2.unitaryDet.ker ≃* SL(2,GaloisField p 1) :=
        J2.unitaryDetKernelEquiv.trans (ABG.specialUnitaryTwo_equiv_sl2 p 1 ho one_ne_zero)
      exact four_of_cubic_centralizer hmodel J2.unitarySubgroup.subtype Subtype.val_injective
        f hf hk h3 d (centralizer_embedding e B z hBz)
        (centralizer_embedding_injective e B z hBz) ho
        (by simpa using GaloisField.card p 1 one_ne_zero)

private theorem four_through_cubic_kernel
    {Y Z : Type*} [Group Y] [Finite Y] [Group Z] [Finite Z]
    (S : Sylow 2 Y) (B : Subgroup Y) [Group.IsPerfect B]
    [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hn : (S : Subgroup Y) ≤ normalizer (B : Set Y))
    (hmodel : ChapterF.Source.IsRankOneModel (B ⧸ pCore 2 B))
    (f : Y →* Z) (hf : Function.Surjective f) (hk : IsPGroup 3 f.ker)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hm : ClassicalGroup.IsPSL Z 3 p ∨ ClassicalGroup.IsPSU Z 3 p) :
    ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4 := by
  let r := f.subgroupMap B
  have h3 : IsPGroup 3 r.ker := by rw [ker_subgroupMap]; exact hk.comap_subtype
  let : Group.IsNilpotent r.ker := h3.isNilpotent
  have h2 := PerfectCoreTwoExtension.ker_isTwoGroup r
  have hi : Function.Injective r := (MonoidHom.ker_eq_bot_iff r).mp
    (disjoint_self.mp (h2.disjoint_of_coprime h3 (by decide)))
  let e : B ≃* B.map f := MulEquiv.ofBijective r ⟨hi,f.subgroupMap_surjective B⟩
  let eq := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let : Group.IsPerfect (B.map f) := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  let : IsSimpleGroup (B.map f ⧸ pCore 2 (B.map f)) := eq.symm.isSimpleGroup
  exact (projective_four (S.mapSurjective hf) (B.map f)
    ((map_mono (f := f) hn).trans (le_normalizer_map f))
    (hmodel.of_equiv eq.symm) ho hm).of_mulEquiv eq

/-- A perfect rank-one local section normalized by the full Sylow in an odd
prime ternary carrier has PSL₂(4) quotient. The actual cubic kernels are retained. -/
theorem right_quotient_four
    {Y : Type*} [Group Y] [Finite Y] (S : Sylow 2 Y) (B : Subgroup Y)
    [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hn : (S : Subgroup Y) ≤ normalizer (B : Set Y))
    (hmodel : ChapterF.Source.IsRankOneModel (B ⧸ pCore 2 B))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL Y 3 p ∨ ClassicalGroup.IsPSU Y 3 p ∨
      Chapter1.Section02.LocalModels.IsSL Y 3 p ∨ Chapter1.Section02.LocalModels.IsSU Y 3 p) :
    ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4 := by
  let : Fact p.Prime := ⟨hp⟩
  rcases hm with hm | hm | hm | hm
  · exact projective_four S B hn hmodel ho (.inl hm)
  · exact projective_four S B hn hmodel ho (.inr hm)
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let f := (Matrix.PSL3.projection F).comp e.toMonoidHom
    have hf : Function.Surjective f := (Matrix.PSL3.projection_surjective F).comp e.surjective
    have hk : IsPGroup 3 f.ker := by
      have hz : IsPGroup 3 (center SL(3,F)) := by
        intro x
        refine ⟨1,?_⟩
        exact orderOf_dvd_iff_pow_eq_one.mp
          ((orderOf_dvd_natCard x).trans (Matrix.SL3.card_center_dvd_three F))
      rw [show f.ker = (Matrix.PSL3.projection F).ker.comap e.toMonoidHom from rfl,
        Matrix.PSL3.projection_ker]
      exact hz.comap_of_injective e.toMonoidHom e.injective
    exact four_through_cubic_kernel S B hn hmodel f hf hk ho
      (.inl ⟨F,inferInstance,inferInstance,hF,⟨MulEquiv.refl _⟩⟩)
  · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
    let f := J.specialToProjective.comp e.toMonoidHom
    have hf : Function.Surjective f := J.specialToProjective_surjective.comp e.surjective
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_surjective f hf
    have hk : IsPGroup 3 f.ker := by
      have hz : IsPGroup 3 J.specialToProjective.ker :=
        fun x => ⟨1,by simpa using J.specialToProjective_ker_cube x⟩
      exact hz.comap_of_injective e.toMonoidHom e.injective
    exact four_through_cubic_kernel S B hn hmodel f hf hk ho
      (.inr ⟨F,inferInstance,inferInstance,J,hF,hc,⟨MulEquiv.refl _⟩⟩)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime.OddTernary
