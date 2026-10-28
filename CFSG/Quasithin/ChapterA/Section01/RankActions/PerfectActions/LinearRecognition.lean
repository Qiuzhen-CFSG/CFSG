module

public import CFSG.Quasithin.ChapterA.Section01.RankActions.PerfectActions.RecognitionInput
public import CFSG.Quasithin.ChapterA.Section01.Linear.Dickson
public import GorensteinWalter.SL2ProjectiveCover
public import Theory.GroupTheory.Commutator.TwoCoverComparison
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.SpecificGroups.SL2.OddCoreAndRank
public import Theory.SpecificGroups.SL2.EvenSubgroup
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.SpecificGroups.DihedralSolvable

/-!
# Perfect subgroups of prime-field SL₂

The projective image of a nontrivial perfect subgroup is nontrivial and
perfect. Corrected Dickson eliminates the solvable alternatives; over a
prime field its subfield alternative is the whole projective group. A
subgroup surjecting onto PSL₂ supplements the center and contains the
commutator of SL₂, hence is the whole group.

In the exceptional A₅ case, even order forces the subgroup to contain
minus identity. Its actual projective kernel is central, is a two-group,
and meets the commutator nontrivially because the subgroup is perfect.
The proved central two-cover comparison with SL₂(5) therefore gives an
actual special-linear equivalence. Characteristic five is assigned to
the full-group alternative; the remaining exceptional primes are ±1
modulo five.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
A.1.29(1), printed p.27, using corrected A.1.3. The two-cover comparison
is the independently proved ABG II.3 Proposition 2 argument; no
prime-field universal-cover rigidity premise is used here.
-/

open Matrix Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.RankActions

private theorem projective_card {F : Type*} [Field F] [Finite F]
    (hF : (2 : F) ≠ 0) :
    Nat.card PSL(2,F) = Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
  have hn : (-1 : F) ≠ 1 := by
    intro h
    exact hF (by linear_combination -h)
  have h := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_ne_one hn] at h
  exact Nat.eq_div_of_mul_eq_right (by decide : 2 ≠ 0) (by simpa [mul_comm] using h)

private theorem congruence_five {p : ℕ} (hp : 3 < p)
    (h : 5 ∣ p ^ 2 - 1) : p % 5 = 1 ∨ p % 5 = 4 := by
  have hpos : 1 ≤ p ^ 2 := by nlinarith
  have hm : p ^ 2 % 5 = 1 := by
    conv_lhs => rw [show p ^ 2 = (p ^ 2 - 1) + 1 by omega]
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd h]
  rw [Nat.pow_mod] at hm
  have hb := Nat.mod_lt p (by decide : 0 < 5)
  interval_cases hrem : p % 5 <;> simp_all

private theorem projective_alternatives {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (H : Subgroup PSL(2,ZMod p)) [Group.IsPerfect H] [Nontrivial H] :
    H = ⊤ ∨ ((p % 5 = 1 ∨ p % 5 = 4) ∧
      Nonempty (H ≃* alternatingGroup (Fin 5))) := by
  have hn := Group.IsPerfect.not_isSolvable H
  have hF : (2 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (p := p) (ZMod p) Nat.prime_two
      (ne_of_gt (lt_trans (by decide : 2 < 3) hp))
  rcases lemma_A_1_3_corrected (F := ZMod p) (p := p) (f := 1)
      (by simp) H with he | hc | hd | ha4 | hs4 | ha5 | haff | hpsl | hpgl
  · let : IsElementaryAbelian p H := he.1
    exact (hn (Group.isSolvable_of_comm (fun x y => mul_comm' x y))).elim
  · obtain ⟨z, _, _, hcyc, _⟩ := hc
    let : IsCyclic H := hcyc
    exact (hn (Group.isSolvable_of_comm (fun x y => mul_comm' x y))).elim
  · obtain ⟨z, _, _, ⟨e⟩⟩ := hd
    let : Group.IsSolvable (DihedralGroup z) := GLS3.Chapter5.dihedralGroup_isSolvable z
    exact (hn (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
  · obtain ⟨_, ⟨e⟩⟩ := ha4
    let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
    exact (hn (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
  · obtain ⟨_, ⟨e⟩⟩ := hs4
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    exact (hn (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
  · obtain ⟨hcong, ⟨e⟩⟩ := ha5
    rcases hcong with rfl | hcong
    · left
      obtain ⟨e5⟩ := ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
      exact H.eq_top_of_card_eq (Nat.card_congr (e.trans e5.symm).toEquiv)
    · exact Or.inr ⟨congruence_five hp (by simpa using hcong), ⟨e⟩⟩
  · obtain ⟨m, t, _, _, _, N, C, _, hN, _, hC, _, _, _, φ, ⟨e⟩⟩ := haff
    let : IsElementaryAbelian p N := hN
    let : IsCyclic C := hC
    let : Group.IsSolvable N := Group.isSolvable_of_comm (fun x y => mul_comm' x y)
    let : Group.IsSolvable C := Group.isSolvable_of_comm (fun x y => mul_comm' x y)
    let : Group.IsSolvable (N ⋊[φ] C) := Group.isSolvable_of_ker_le_range
      SemidirectProduct.inl SemidirectProduct.rightHom
      SemidirectProduct.range_inl_eq_ker_rightHom.ge
    exact (hn (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
  · obtain ⟨m, _, hm, ⟨e⟩⟩ := hpsl
    have hm1 : m = 1 := Nat.dvd_one.mp hm
    subst m
    left
    apply H.eq_top_of_card_eq
    calc
      Nat.card H = Nat.card PSL(2,GaloisField p 1) := Nat.card_congr e.toEquiv
      _ = Nat.card PSL(2,ZMod p) := by
        rw [projective_card (CharP.cast_ne_zero_of_ne_of_prime (p := p)
          (GaloisField p 1) Nat.prime_two
          (ne_of_gt (lt_trans (by decide : 2 < 3) hp))), projective_card hF,
          GaloisField.card p 1 (by decide)]
        simp
  · obtain ⟨m, hm, hdiv, _⟩ := hpgl
    have := Nat.dvd_one.mp hdiv
    omega

private theorem eq_top_of_projective_image_eq_top {F : Type*} [Field F]
    [Group.IsPerfect SL(2,F)] (K : Subgroup SL(2,F))
    (hK : K.map (GorensteinWalter.sl2ProjectiveProjection F) = ⊤) : K = ⊤ := by
  let Z := center SL(2,F)
  let q := GorensteinWalter.sl2ProjectiveProjection F
  have hsup : K ⊔ Z = ⊤ := by
    apply top_unique
    intro g _
    have hg : q g ∈ K.map q := by rw [hK]; trivial
    obtain ⟨k, hk, he⟩ := hg
    have hz : k / g ∈ Z := QuotientGroup.eq_iff_div_mem.mp he
    have hzsup : (k / g)⁻¹ ∈ K ⊔ Z :=
      (K ⊔ Z).inv_mem ((le_sup_right : Z ≤ K ⊔ Z) hz)
    have hksup : k ∈ K ⊔ Z := (le_sup_left : K ≤ K ⊔ Z) hk
    rw [show g = (k / g)⁻¹ * k by simp [div_eq_mul_inv]]
    exact (K ⊔ Z).mul_mem hzsup hksup
  have hnormalizer : Subgroup.normalizer (K : Set SL(2,F)) = ⊤ := by
    apply top_unique
    rw [← hsup]
    exact sup_le K.le_normalizer (Subgroup.center_le_normalizer (K : Set SL(2,F)))
  let : K.Normal := Subgroup.normalizer_eq_top_iff.mp hnormalizer
  have hc := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup
    (inferInstance : IsMulCommutative Z)
  apply top_unique
  simpa using hc

private theorem exceptional_lift {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (K : Subgroup SL(2,ZMod p)) [Group.IsPerfect K]
    (eA : K.map (GorensteinWalter.sl2ProjectiveProjection (ZMod p)) ≃*
      alternatingGroup (Fin 5)) : Nonempty (K ≃* SL(2,ZMod 5)) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let q := GorensteinWalter.sl2ProjectiveProjection (ZMod p)
  let H := K.map q
  let qK : K →* H := q.subgroupMap K
  have hqK : Function.Surjective qK := q.subgroupMap_surjective K
  have hodd : Odd (Nat.card (ZMod p)) := by
    simpa using (Fact.out : p.Prime).odd_of_ne_two
      (ne_of_gt (lt_trans (by decide : 2 < 3) hp))
  have hF : (2 : ZMod p) ≠ 0 := GorensteinWalter.two_ne_zero_of_odd_card _ hodd
  have hHcard : Nat.card H = 60 := by
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hKtwo : 2 ∣ Nat.card K := (show 2 ∣ Nat.card H by rw [hHcard]; decide).trans
    (Subgroup.card_dvd_of_surjective qK hqK)
  have hneg := SpecialLinearGroup.neg_one_mem_of_even_card hF K hKtwo
  obtain ⟨e5⟩ := ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  let e : H ≃* PSL(2,ZMod 5) := eA.trans e5.symm
  let f : K →* PSL(2,ZMod 5) := e.toMonoidHom.comp qK
  have hf : Function.Surjective f := e.surjective.comp hqK
  have hker : f.ker = (q.comp K.subtype).ker := by
    ext x
    change e (qK x) = 1 ↔ q x = 1
    rw [← e.map_one, e.injective.eq_iff]
    exact Subtype.ext_iff
  have hcentral : f.ker ≤ center K := by
    intro x hx
    have hxq : (x : SL(2,ZMod p)) ∈ q.ker := by
      rw [hker] at hx
      exact hx
    have hxc : (x : SL(2,ZMod p)) ∈ center SL(2,ZMod p) := by
      rwa [GorensteinWalter.sl2ProjectiveProjection_ker] at hxq
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxc (y : SL(2,ZMod p)))
  let i : f.ker →* q.ker := (K.subtype.comp f.ker.subtype).codRestrict q.ker (by
    intro x
    have hx := x.property
    simp only [hker] at hx
    exact hx)
  have hi : Function.Injective i := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : q.ker => z.val) hxy
  have hf2 : IsPGroup 2 f.ker :=
    (GorensteinWalter.sl2ProjectiveProjection_ker_isPGroup (ZMod p) hodd).of_injective i hi
  have hfn : f.ker ⊓ _root_.commutator K ≠ ⊥ := by
    rw [Group.IsPerfect.commutator_eq_top, inf_top_eq]
    intro he
    let a : K := ⟨-1, hneg⟩
    have ha : a ∈ f.ker := by
      rw [hker]
      change q (-1) = 1
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [Subgroup.mem_center_iff]
      intro g
      simp
    have ha1 : a = 1 := by simpa [he] using ha
    have hn : (-1 : SL(2,ZMod p)) = 1 := congrArg Subtype.val ha1
    have ho := SpecialLinearGroup.orderOf_neg_one_eq_two hF
    rw [hn, orderOf_one] at ho
    contradiction
  obtain ⟨hg, hgcentral, hgcard, hg2, hperfect, hdihedral⟩ :=
    GorensteinWalter.sl2_projective_cover_model (ZMod 5) (by norm_num) (by norm_num)
  let : Group.IsPerfect SL(2,ZMod 5) := hperfect
  obtain ⟨ec⟩ := CentralExtension.commutator_mulEquiv_of_central_two_covers
    f (GorensteinWalter.sl2ProjectiveProjection (ZMod 5)) hf hg hcentral hgcentral
    hf2 hg2 hfn hgcard hdihedral
  exact ⟨(Subgroup.topEquiv.symm.trans
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm)).trans ec⟩

/-- The unconditional prime-field recognition used by A.1.29(1): every
nontrivial perfect SL₂ subgroup is the full group or an actual SL₂(5),
with the exceptional prime congruence. -/
public theorem primePerfectSL2Recognition : PrimePerfectSL2Recognition := by
  intro p _ hp K hperfect hnontrivial
  let : Group.IsPerfect K := hperfect
  let : Nontrivial K := hnontrivial
  let q := GorensteinWalter.sl2ProjectiveProjection (ZMod p)
  let H := K.map q
  let : Group.IsPerfect H := Group.IsPerfect.map q
  have hHne : H ≠ ⊥ := by
    intro h
    have hle : K ≤ center SL(2,ZMod p) := by
      have hk := K.map_eq_bot_iff.mp h
      rwa [GorensteinWalter.sl2ProjectiveProjection_ker] at hk
    apply Group.IsPerfect.not_isSolvable K
    apply Group.isSolvable_of_comm
    intro x y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hle y.property) (x : SL(2,ZMod p)))
  let : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hHne
  rcases projective_alternatives hp H with htop | ⟨hcong, ⟨eA⟩⟩
  · left
    let : Group.IsPerfect SL(2,ZMod p) :=
      GorensteinWalter.sl2_isPerfect_of_card_gt_three _ (by simpa using hp)
    have hKtop := eq_top_of_projective_image_eq_top K htop
    exact ⟨(MulEquiv.subgroupCongr hKtop).trans Subgroup.topEquiv⟩
  · exact Or.inr ⟨hcong, exceptional_lift hp K eA⟩

end CFSG.Quasithin.ChapterA.RankActions
