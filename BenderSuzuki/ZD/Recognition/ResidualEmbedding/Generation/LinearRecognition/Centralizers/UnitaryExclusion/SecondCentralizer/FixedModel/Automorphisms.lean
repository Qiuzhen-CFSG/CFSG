module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.BorelRecognition
public import BenderSuzuki.Converse.PSU3
public import BenderSuzuki.ZD.ProductClosedCentralFactor.ModelGeometry.Fusion
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.SpecificGroups.SU3.ProjectiveGraphFixed
public import Theory.AtlasPort.ExceptionalIsomorphisms.FieldTransportLaws
public import Mathlib.FieldTheory.Finite.GaloisField
public import Theory.GroupAction.FixedCentralizerRigidity
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison

/-!
# Nonsolvable fixed subgroups in the two unitary covers

In PSU₃, strong embedding in a solvable Borel makes the centralizer of every
involution solvable. Thus a nontrivial involutory automorphism with nonsolvable
fixed group is outer, and the proved outer-conjugacy theorem identifies its
fixed group with the graph-fixed PSL₂ over the Hermitian fixed field.

For SU₃, perfect central-cover descent detects nontriviality and innerness.
A solvable fixed group downstairs would give a solvable central extension
upstairs. The unitary matrix supplied by projective descent also conjugates
SU₃: faithful automorphism descent identifies its conjugated graph action
with the given automorphism. The graph-fixed equivalence therefore identifies
the entire special fixed group, without dropping its possible central kernel.
Finite-field uniqueness finally gives the prescribed binary PSL₂ carrier.

Source: GLS4, Chapter 4, Lemma 3.4(b,c), and the central-cover application in
Chapter 2, final paragraph of Lemma 13.2.
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion.FixedModel
open Subgroup _root_.BenderSuzuki.MatrixGroups HermitianForm
open PFAppendixIII PFchapter1section1
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  {n : ℕ} (hn : 2 ≤ n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hc : Nat.card E = (2 ^ n) ^ 2)
  (hf : Nat.card {x : E // J.conj x = x} = 2 ^ n)

private instance : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

include hn hJ hc hf in
private theorem exists_solvable_stronglyEmbedded :
    ∃ B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      IsStronglyEmbedded B ∧ Group.IsSolvable B := by
  obtain ⟨_, rho, _, _, happly, _⟩ := External.huppert_II_10_12 J (2 ^ n) hc hf hJ
  obtain ⟨H, D, Q, t, _, hA⟩ := Converse.hypothesisA_psu3_general J hJ (2 ^ n) hc hf
    (lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hn))
    ⟨n, rfl⟩ rho happly
  let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) (Converse.psuOmega J) :=
    MulAction.compHom _ rho
  have hB := hA.A1.isStronglyEmbedded
  exact ⟨H, hB, (RankOneModelGeometry.unitary_projective_borel_of_stronglyEmbedded
    J hn hc hf hJ H hB).1⟩

private theorem solvable_centralizer_of_stronglyEmbedded
    {H : Type*} [Group H] [Finite H] (B : Subgroup H) (hB : IsStronglyEmbedded B)
    (hs : Group.IsSolvable B) (x : H) (hx : PFAppendixIII.IsInvolution x) :
    Group.IsSolvable (centralizer ({x} : Set H)) := by
  obtain ⟨P, hPB⟩ := hB.containsSylowTwo
  obtain ⟨y, hy⟩ := P.exists_isConj_of_orderOf_eq_prime_pow
    (show orderOf x = 2 ^ 1 by simpa using orderOf_eq_prime hx.sq_eq_one hx.ne_one)
  obtain ⟨g, hg⟩ := isConj_iff.mp hy
  have hxB : MulAut.conj g x ∈ B := by
    change g * x * g⁻¹ ∈ B
    rw [hg]
    exact hPB y.property
  have hi := IsInvolution.map_of_injective hx (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  let f : centralizer ({x} : Set H) →* B :=
    ((MulAut.conj g).toMonoidHom.comp (centralizer ({x} : Set H)).subtype).codRestrict B (by
      intro c
      apply hB.centralizer_le hxB hi
      apply mem_centralizer_singleton_iff.mpr
      simpa only [map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        Subgroup.subtype_apply] using
        congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp c.property))
  let := hs
  apply Group.isSolvable_of_isSolvable_injective (f := f)
  intro c d he
  exact Subtype.ext ((MulAut.conj g).injective (congrArg Subtype.val he))

include hn hJ hc hf in
private theorem projective_inner_fixed_solvable
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (hne : a ≠ 1) (hi : ∃ x, a = MulAut.conj x) : Group.IsSolvable a.fixedSubgroup := by
  obtain ⟨x, rfl⟩ := hi
  have hx : x ≠ 1 := fun he => hne (he ▸ map_one MulAut.conj)
  have hz := EvenProjectiveComparison.center_eq_bot J (by omega) hc
    (External.huppert_II_10_4_conj_eq_frobenius J _ hc hf)
  have hxs : x ^ 2 = 1 := by
    have hconj : MulAut.conj (x ^ 2) = 1 := by rwa [map_pow]
    have hm : x ^ 2 ∈ center (ProjectiveSpecialUnitaryMatrixGroup J) := by
      apply mem_center_iff.mpr
      intro y
      have hh := congrArg (fun f : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) => f y) hconj
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    simpa only [hz, mem_bot] using hm
  obtain ⟨B, hB, hs⟩ := exists_solvable_stronglyEmbedded J hn hJ hc hf
  rw [MulAut.fixedSubgroup_conj]
  exact solvable_centralizer_of_stronglyEmbedded B hB hs x ⟨hx, hxs⟩

private theorem fixed_solvable_of_central_descent
    {H K : Type*} [Group H] [Group K]
    (f : H →* K) (hk : f.ker ≤ center H) (a : MulAut H) (b : MulAut K)
    (he : ∀ x, f (a x) = b (f x)) (hs : Group.IsSolvable b.fixedSubgroup) :
    Group.IsSolvable a.fixedSubgroup := by
  let g : a.fixedSubgroup →* b.fixedSubgroup :=
    (f.comp a.fixedSubgroup.subtype).codRestrict _ (by
      intro x
      exact (MulAut.mem_fixedSubgroup _ _).mpr
        ((he x).symm.trans (congrArg f ((MulAut.mem_fixedSubgroup _ _).mp x.property))))
  have hc (x : g.ker) : (x.val.val : H) ∈ center H :=
    hk (congrArg Subtype.val (MonoidHom.mem_ker.mp x.property))
  let : Group.IsSolvable g.ker := Group.isSolvable_of_comm (fun x y => by
    apply Subtype.ext
    apply Subtype.ext
    exact (mem_center_iff.mp (hc x) y.val.val).symm)
  let := hs
  exact Group.isSolvable_of_ker_le_range g.ker.subtype g (by simp)
end BenderSuzuki.ZD.UnitaryExclusion.FixedModel
end


noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion.FixedModel
open Subgroup _root_.BenderSuzuki.MatrixGroups HermitianForm PFAppendixIII
variable {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private def specialConjAut (v : J.unitarySubgroup) : MulAut J.specialSubgroup where
  toFun := J.specialUnitaryConj v
  invFun := J.specialUnitaryConj v⁻¹
  left_inv x := by apply Subtype.ext; simp [specialUnitaryConj_val, mul_assoc]
  right_inv x := by apply Subtype.ext; simp [specialUnitaryConj_val, mul_assoc]
  map_mul' x y := by apply Subtype.ext; simp [specialUnitaryConj_val, mul_assoc]

private def perfectCover {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card E = (2 ^ n) ^ 2)
    (hf : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    PerfectCentralCovering.Cover J.specialSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) where
  toMonoidHom := J.specialToProjective
  surjective := J.specialToProjective_surjective
  isPerfect := J.special_isPerfect_of_fixed_card
    (lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hn)) hc hf
  ker_le_center := J.specialToProjective_ker_le_center

omit [CharP E 2] in
private theorem kernel_center {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card E = (2 ^ n) ^ 2)
    (hf : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    J.specialToProjective.ker = center J.specialSubgroup :=
  J.specialToProjective_ker_eq_center
    (EvenProjectiveComparison.center_eq_bot J (by omega) hc
      (External.huppert_II_10_4_conj_eq_frobenius J _ hc hf))

include hJ in
private theorem special_outer_fixed_equiv {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card E = (2 ^ n) ^ 2)
    (hf : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (a : MulAut J.specialSubgroup) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ x, a = MulAut.conj x) :
    Nonempty (a.fixedSubgroup ≃* PSL2MatrixGroup (FixedBy.subfield E J.conj)) := by
  let f := perfectCover J hn hc hf
  have hk : f.toMonoidHom.ker = center J.specialSubgroup := kernel_center J hn hc hf
  let b := f.autMap hk a
  have hb : b ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  have hbo : ¬ ∃ x, b = MulAut.conj x := fun hi => houter ((f.autMap_inner_iff hk a).mp hi)
  let γ := projectiveGraphAut J hJ
  have hγ : J.IsEntrywiseConjugation γ := projectiveGraphAut_isEntrywiseConjugation J hJ
  obtain ⟨w, hw⟩ := J.outer_involution_normal_form n hn hJ hc hf hγ b hb hbo
  obtain ⟨v, hv⟩ := J.projective_descent n hn hJ hc hf hγ w (hw ▸ hb)
  have hconj : MulAut.congr (J.unitaryConj v) γ = b :=
    (J.congr_unitaryConj_of_projective_coboundary hγ w v hv).trans hw.symm
  let c := specialConjAut J v
  let γs := specialGraphAut J hJ
  have hdc : f.autMap hk c = J.unitaryConj v := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    rw [f.autMap_apply]
    exact (J.unitaryConj_specialToProjective v x).symm
  have hdg : f.autMap hk γs = γ := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    rw [f.autMap_apply]
    exact (projectiveGraphAut_specialToProjective J hJ x).symm
  have hs : MulAut.congr c γs = a := by
    apply f.autMap_injective hk
    calc
      f.autMap hk (MulAut.congr c γs) =
          f.autMap hk (c * γs * c⁻¹) := congrArg _ (by ext x; rfl)
      _ = J.unitaryConj v * γ * (J.unitaryConj v)⁻¹ := by
        rw [map_mul, map_mul, map_inv, hdc, hdg]
      _ = MulAut.congr (J.unitaryConj v) γ := by ext x; rfl
      _ = f.autMap hk a := hconj
  exact ⟨(MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup hs.symm)).trans
    ((MulAut.fixedSubgroupCongr c γs).symm.trans
      ((projectiveGraphFixedEquivSpecial J hJ).symm.trans (projectiveGraphFixedEquiv J hJ)))⟩

include hJ in
private theorem projective_outer_fixed_equiv {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card E = (2 ^ n) ^ 2)
    (hf : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ x, a = MulAut.conj x) :
    Nonempty (a.fixedSubgroup ≃* PSL2MatrixGroup (FixedBy.subfield E J.conj)) := by
  obtain ⟨c, hc⟩ := J.outer_involution_conjugate n hn hJ hc hf
    (projectiveGraphAut_isEntrywiseConjugation J hJ) a ha houter
  exact ⟨(MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup hc.symm)).trans
    ((MulAut.fixedSubgroupCongr c _).symm.trans (projectiveGraphFixedEquiv J hJ))⟩

omit [CharP E 2] in
private theorem fixed_field_linear_equiv {n : ℕ} (hn : 2 ≤ n)
    (hf : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    Nonempty (PSL2MatrixGroup (FixedBy.subfield E J.conj) ≃* PSL2BinaryMatrixGroup n) := by
  let F := FixedBy.subfield E J.conj
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (BinaryGaloisField n) := Fintype.ofFinite _
  let e : F ≃+* BinaryGaloisField n := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hf.trans (GaloisField.card 2 n (by omega)).symm)
  exact ⟨Atlas.fieldEquivPSL 2 e⟩
end BenderSuzuki.ZD.UnitaryExclusion.FixedModel
end

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion.FixedModel
open Subgroup _root_.BenderSuzuki.MatrixGroups HermitianForm

private theorem not_solvable_fixed_congr
    {H K : Type*} [Group H] [Group K] (e : H ≃* K) (a : MulAut H)
    (hs : ¬ Group.IsSolvable a.fixedSubgroup) :
    ¬ Group.IsSolvable (MulAut.congr e a).fixedSubgroup := by
  intro hh
  let := hh
  let c := MulAut.fixedSubgroupCongr e a
  exact hs (Group.isSolvable_of_isSolvable_injective (f := c.toMonoidHom) c.injective)

/-- A nonidentity automorphism squaring to one on either actual unitary cover
has PSL₂(2ⁿ) as its fixed group whenever that group is nonsolvable. For SU₃,
faithful perfect-cover descent lifts conjugacy of the automorphism itself,
so the special central kernel is retained throughout the identification. -/
public theorem unitary_cover_nonsolvable_fixed
    {H : Type*} [Group H] [Finite H] {n : ℕ} (hn : 2 ≤ n)
    (hcover : IsUnitaryCentralizerCoverAt n H)
    (a : MulAut H) (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (hns : ¬ Group.IsSolvable a.fixedSubgroup) :
    Nonempty (a.fixedSubgroup ≃* PSL2BinaryMatrixGroup n) := by
  obtain ⟨E, _, _, J, hJ, hc, hf, hm⟩ := hcover
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card, pow_mul] using hc)
  obtain ⟨eF⟩ := fixed_field_linear_equiv J hn hf
  rcases hm with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · let b := MulAut.congr e a
    have hb : b ^ 2 = 1 := by rw [← map_pow, ha, map_one]
    have hbn : b ≠ 1 := fun he => hne ((MulAut.congr e).injective (he.trans (map_one _).symm))
    have hbs := not_solvable_fixed_congr e a hns
    have hbo : ¬ ∃ x, b = MulAut.conj x :=
      fun hi => hbs (projective_inner_fixed_solvable J hn hJ hc hf b hb hbn hi)
    obtain ⟨eb⟩ := projective_outer_fixed_equiv J hJ hn hc hf b hb hbo
    exact ⟨(MulAut.fixedSubgroupCongr e a).trans (eb.trans eF)⟩
  · let b := MulAut.congr e a
    have hb : b ^ 2 = 1 := by rw [← map_pow, ha, map_one]
    have hbn : b ≠ 1 := fun he => hne ((MulAut.congr e).injective (he.trans (map_one _).symm))
    have hbs := not_solvable_fixed_congr e a hns
    let f := perfectCover J hn hc hf
    have hk : f.toMonoidHom.ker = center J.specialSubgroup := kernel_center J hn hc hf
    let d := f.autMap hk b
    have hd : d ^ 2 = 1 := by rw [← map_pow, hb, map_one]
    have hdn : d ≠ 1 := fun he => hbn (f.autMap_injective hk (he.trans (map_one _).symm))
    have hds : ¬ Group.IsSolvable d.fixedSubgroup := by
      intro hs
      exact hbs (fixed_solvable_of_central_descent f.toMonoidHom f.ker_le_center b d
        (fun x => (f.autMap_apply hk b x).symm) hs)
    have hdo : ¬ ∃ x, d = MulAut.conj x :=
      fun hi => hds (projective_inner_fixed_solvable J hn hJ hc hf d hd hdn hi)
    have hbo : ¬ ∃ x, b = MulAut.conj x := fun hi => hdo ((f.autMap_inner_iff hk b).mpr hi)
    obtain ⟨eb⟩ := special_outer_fixed_equiv J hJ hn hc hf b hb hbo
    exact ⟨(MulAut.fixedSubgroupCongr e a).trans (eb.trans eF)⟩
end BenderSuzuki.ZD.UnitaryExclusion.FixedModel
end
