module
public import Theory.SpecificGroups.DihedralProduct.CenterAction
public import CFSG.Quasithin.ChapterB.Section02.BaumannCenter
public import Stellmacher.BaumannNormalizer
public import CFSG.Quasithin.Chapter10.SourceA5ZeroNormalizerOrder
/-!
# The original Sylow image on the four central enlargements

The factor-action kernel fixes the center of Baum(T). It therefore centralizes
its central omega subgroup, which is the Thompson alpha subgroup; inside T
this is precisely Baum(T). The original orders 2¹⁵ and 2¹² then give image
order eight, with the literal normalizer action and the selected coordinates.

Source: Aschbacher–Smith 10.2.1, printed p.743.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]
theorem baumann_dihedral_factorAction_kernel (T : Subgroup G) (e : baumann T ≃* (Fin 4 → DihedralGroup 4)) :
    let S := baumann T
    let N := normalizer (S : Set G)
    let f := (DihedralProductCanonical.transportedFactorAction e).comp S.normalizerMonoidHom
    T.subgroupOf N ⊓ f.ker = S.subgroupOf N := by
  let S := baumann T
  let N := normalizer (S : Set G)
  let f := (DihedralProductCanonical.transportedFactorAction e).comp S.normalizerMonoidHom
  change T.subgroupOf N ⊓ f.ker = S.subgroupOf N
  ext n
  change ((n:G) ∈ T ∧ f n = 1) ↔ (n:G) ∈ S
  constructor
  · rintro ⟨hnT,hnf⟩
    refine ⟨hnT,?_⟩
    change (n:G) ∈ centralizer (thompsonAlpha T : Set G)
    rw [←omegaCenter_baumann_eq_thompsonAlpha]
    apply mem_centralizer_iff.mpr
    intro z hz
    obtain ⟨hzS,_,hzC⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hz
    have hzcenter : (⟨z,hzS⟩ : S) ∈ center S :=
      mem_center_iff.mpr fun s => Subtype.ext (hzC s s.property)
    have hh := (DihedralProductCanonical.transportedFactorAction_eq_one_iff
      e (S.normalizerMonoidHom n)).mp hnf ⟨z,hzS⟩ hzcenter
    have he := congrArg S.subtype hh
    change (n:G) * z * (n:G)⁻¹ = z at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hnS
    refine ⟨hnS.1,?_⟩
    apply (DihedralProductCanonical.transportedFactorAction_eq_one_iff
      e (S.normalizerMonoidHom n)).mpr
    intro z hz
    apply Subtype.ext
    change (n:G) * (z:G) * (n:G)⁻¹ = (z:G)
    have hh := congrArg S.subtype (mem_center_iff.mp hz ⟨n,hnS⟩)
    change (n:G) * (z:G) = (z:G) * (n:G) at hh
    rw [hh,mul_inv_cancel_right]
end CFSG.Quasithin.ChapterB

namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false
/-- The actual source Sylow image on Γ has order eight for any four-factor marking. -/
theorem source_a5_zero_factorAction_image_card
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (eR : ChapterB.baumann (T : Subgroup G) ≃* (Fin 4 → DihedralGroup 4)) :
    let S := ChapterB.baumann (T : Subgroup G)
    let N := normalizer (S : Set G)
    let f := (DihedralProductCanonical.transportedFactorAction eR).comp S.normalizerMonoidHom
    Nat.card (((T : Subgroup G).subgroupOf N).map f) = 8 := by
  let S := ChapterB.baumann (T : Subgroup G)
  let N := normalizer (S : Set G)
  let f := (DihedralProductCanonical.transportedFactorAction eR).comp S.normalizerMonoidHom
  let Tn := (T : Subgroup G).subgroupOf N
  let Sn := S.subgroupOf N
  have hker : Tn ⊓ f.ker = Sn := ChapterB.baumann_dihedral_factorAction_kernel _ eR
  have hTN : (T : Subgroup G) ≤ N :=
    (T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)
  have hST : Sn ≤ Tn := subgroupOf_mono N inf_le_left
  have hcT : Nat.card Tn = 32768 :=
    (Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv).trans
      (source_a5_zero_sylow_card D e hn hout hz)
  have hcS : Nat.card Sn = 4096 :=
    (Nat.card_congr (subgroupOfEquivOfLe S.le_normalizer).toEquiv).trans
      (source_a5_zero_baumann_card D e hn hout hz)
  have hi : Sn.relIndex Tn = Nat.card (Tn.map f) := by
    rw [←hker,inf_relIndex_left,relIndex_ker]
  have hh := relIndex_mul_relIndex (⊥ : Subgroup N) Sn Tn bot_le hST
  rw [relIndex_bot_left,relIndex_bot_left,hcT,hcS,hi] at hh
  change Nat.card (Tn.map f) = 8
  omega
end CFSG.Quasithin.Chapter10
