module
public import Theory.GroupTheory.SylowCentralSeedFusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupKernelFusion
public import Theory.GroupTheory.PCoreNormalizerAction
public import Theory.SpecificGroups.PSL3Four.OuterThreeStructure.FieldTransport

/-!
# Residual fusion through the normalizer of C_K H

Write K = O²(H), N = N_G(K), and let C be the literal kernel of N's
action on K/O₂(K). Nonfaithfulness makes H centralize Ω₁Z(T). Hence
fusion by C H on every subgroup of this omega-center reduces to the
proved C T fusion. The central-seed Frattini lemma extends this to
N_G(C H), since the actual Baumann bound places N_G(T) in N_G(L).
The unchanged natural point therefore has TI under N_G(C H) in every
odd field degree, without an assumption about its Sylow-prime actor.

The inner-action kernel is exactly K C. Out(PSL₃(4)) has order dividing
twelve, and H contains T, so [N : C H] divides three. The Chapter12
consumer uses these conclusions to finish parity if C H is normal in N
and isolate the self-normalizing index-three case otherwise.

The remaining index-three fusion and original parity assembly belong to
qt-d-1222-linear-field-parity. Solvability of the actual quotient-action
kernel remains the independent Suzuki consequence, whose source discharge
is retained by qt-f112-linear-suzuki-containment. No unrestricted residual
TI or unconditional parity is asserted here.
Source: Aschbacher–Smith 5.1.16–17, printed pp.639–642
(refs/quasithin.pdf); the outer-order bound is GLS3, Theorem 2.5.12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}

/-- The centralizing residual adds no new fusion on any subgroup of Ω₁Z(T). -/
theorem residual_kernel_overgroup_fusion
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (Z : Subgroup G) (hZ : Z ≤ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    {g : G} (hg : g ∈
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
        (normalizer (residual H : Set G)).subtype ⊔ H) :
    ∃ b ∈ normalizer (L : Set G),
      Z.map (MulAut.conj g).toMonoidHom = Z.map (MulAut.conj b).toMonoidHom := by
  let N := normalizer (residual H : Set G)
  let f := normalizerQuotientAction (residual H) (pCore 2 (residual H))
  let C := f.ker.map N.subtype
  have hNC : N ≤ normalizer (C : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      f.ker.le_normalizer_map N.subtype
  have hp : g ∈ (C : Set G) * (H : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left C H ((le_normalizer_residual H).trans hNC)]
    exact hg
  obtain ⟨c,hc,d,hd,rfl⟩ := hp
  have hHC : H ≤ omegaCentralizer T :=
    (residual_le_omegaCentralizer_iff hH.1.1.2).mp
      (residual_centralizes_omega_of_nonfaithful h.qtke hH.1.1 hK.1 hnf)
  have he : Z.map (MulAut.conj d).toMonoidHom = Z := by
    apply le_antisymm
    · rintro _ ⟨z,hz,rfl⟩
      have hh : (MulAut.conj d) z = z :=
        mul_inv_eq_iff_eq_mul.mpr ((hHC hd) z (hZ hz)).symm
      change (MulAut.conj d) z ∈ Z
      rwa [hh]
    · intro z hz
      refine ⟨z,hz,?_⟩
      exact mul_inv_eq_iff_eq_mul.mpr ((hHC hd) z (hZ hz)).symm
  obtain ⟨b,hb,heq⟩ := residual_kernel_sylow_fusion h hH hK hnf hm hsolv Z hZ (mem_sup_left hc)
  refine ⟨b,hb,?_⟩
  have hcomp : (MulAut.conj (c*d)).toMonoidHom =
      (MulAut.conj c).toMonoidHom.comp (MulAut.conj d).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [hcomp,←map_map,he,heq]

/-- Actual conjugation fusion under the normalizer of C_K H. -/
theorem residual_kernel_overgroup_normalizer_fusion
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (Z : Subgroup G) (hZ : Z ≤ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    {g : G} (hg : g ∈ normalizer
      (((normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
        (normalizer (residual H : Set G)).subtype ⊔ H : Subgroup G) : Set G)) :
    ∃ b ∈ normalizer (L : Set G),
      Z.map (MulAut.conj g).toMonoidHom = Z.map (MulAut.conj b).toMonoidHom := by
  exact normalizer_fusion_on_omegaCenter T _ _ (fun _ hx => mem_sup_right (hH.1.1.2 hx))
    ((Stellmacher.normalizer_le_normalizer_baumann _).trans
      (baumann_normalizer_le_of_nonfaithful_residual h hH hK hnf))
    (fun Z hZ _ hg => residual_kernel_overgroup_fusion h hH hK hnf hm hsolv Z hZ hg) Z hZ hg

/-- The natural point is TI under the full normalizer of the actual C_K H. -/
theorem fundamental_point_ti_under_kernel_overgroup_normalizer
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hodd : Odd n) (hnat : IsNaturalModule L D.moduleSubgroup n)
    {g : G} (hg : g ∈ normalizer
      (((normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
        (normalizer (residual H : Set G)).subtype ⊔ H : Subgroup G) : Set G)) :
    let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ D.moduleSubgroup
    Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      Z.map (MulAut.conj g).toMonoidHom = Z := by
  obtain ⟨b,hb,he⟩ := residual_kernel_overgroup_normalizer_fusion h hH hK hnf hm hsolv
    (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ D.moduleSubgroup) inf_le_left hg
  dsimp only
  rw [he]
  exact fundamental_point_ti_under_normalizer D h.sylow_normalizes h.linear hodd hnat hb

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {H : Subgroup G}

/-- C_K H has index dividing three in the actual residual normalizer.
The original residual supplies all inner automorphisms and H contains T. -/
theorem residual_kernel_overgroup_index_dvd_three
    (hTH : (T : Subgroup G) ≤ H)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    let N := normalizer (residual H : Set G)
    let C := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map N.subtype
    (C ⊔ H).relIndex N ∣ 3 := by
  let K := residual H
  let N := normalizer (K : Set G)
  let C := (normalizerQuotientAction K (pCore 2 K)).ker.map N.subtype
  let J := C ⊔ H
  let a := pCoreNormalizerOuterAction 2 K
  have hHN : H ≤ N := le_normalizer_residual H
  have hTN : (T : Subgroup G) ≤ N := hTH.trans hHN
  have hker : a.ker.map N.subtype = K ⊔ C := by
    rw [pCoreNormalizerOuterAction_ker,Subgroup.map_sup,
      map_subgroupOf_eq_of_le K.le_normalizer]
    rfl
  have hkJ : a.ker ≤ J.subgroupOf N := by
    intro x hx
    have hh : (x : G) ∈ K ⊔ C := hker ▸ mem_map_of_mem N.subtype hx
    exact (sup_le ((show K ≤ H from map_subtype_le _).trans le_sup_right) le_sup_left) hh
  have hout : Nat.card (MulAut.Outer (K ⧸ pCore 2 K)) ∣ 12 := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := linear_residual_quotient hm
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact Matrix.PSL3Four.OuterThreeStructure.outer_card_dvd_twelve_of_card_four hF
  have hd : (J.subgroupOf N).index ∣ 12 :=
    (index_dvd_of_le hkJ).trans (by
      rw [index_ker]
      exact (card_subgroup_dvd_card a.range).trans hout)
  have h2 : ¬ 2 ∣ (J.subgroupOf N).index := by
    intro hh
    exact (T.subtype hTN).not_dvd_index
      (hh.trans (index_dvd_of_le (show ((T.subtype hTN) : Subgroup N) ≤ J.subgroupOf N from
        fun _ hx => mem_sup_right (hTH hx))))
  have hc : Nat.Coprime (J.subgroupOf N).index 4 :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm.pow_right 2
  exact hc.dvd_of_dvd_mul_left hd
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
