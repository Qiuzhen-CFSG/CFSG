module
public import Theory.SpecificGroups.Triality.BinaryLocalResidual
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.GroupTheory.SolvableSylowControl

/-!
# Sylow control in the binary triality endpoint away from three

A solvable subgroup containing the full positive Sylow lies in one of
its two root parabolics. In the arms parabolic, the PSL₂(8) quotient
forces normalization of that Sylow. In the central parabolic, the normal
local factor has order 2¹²·3. If the subgroup has order prime to three,
its intersection with that factor is precisely the prescribed Sylow,
which is therefore normal.

Sylow conjugacy transports this result to any genuine model equivalence.
The relative version identifies the Sylow as the two-core of the actual
intersection, so a solvable ambient subgroup preserving the triality
layer preserves that Sylow. This does not assert unrestricted solvable
Sylow control at q = 2.

Source: Aschbacher--Smith 5.1.13, printed p.636; GLS3 §§2.3--2.6 for
the genuine graph-field parabolics. The original local Cartan application
is in RankOneModuleGenericExceptionalCartanLocalBinaryParity.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Triality.Standard.BinaryThreeFreeSylow
open Parabolics
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "M" => BinaryCarrier 1 Nat.zero_lt_one

private theorem central_local_card : Nat.card (localFactor P .central) = 12288 := by
  let e := (localFactorCentralQuotientEquivPSL2 P rfl).trans
    (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 1)).symm
  have hq : Nat.card (localFactor P .central ⧸ pCore 2 (localFactor P .central)) = 6 := by
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.sl2_card_formula,
      GaloisField.card 2 1 (by decide)]
    norm_num
  have hc := (pCore 2 (localFactor P .central)).card_mul_index
  rw [index_eq_card, hq, localFactor_central_twoCore_card P rfl] at hc
  exact hc.symm

private theorem central_normalizes (J : Subgroup M)
    (hU : unipotent P ≤ J) (hJ : J ≤ parabolic P .central)
    (hthree : ¬ 3 ∣ Nat.card J) : J ≤ normalizer (unipotent P : Set M) := by
  let K := localFactor P .central
  have hUK : unipotent P ≤ K :=
    sylow_le_localFactor P .central (unipotentSylow P rfl)
      ((unipotent_le_borel P).trans (borel_le_parabolic P .central))
  have htwo : IsPGroup 2 (J ⊓ K : Subgroup M) := by
    apply isPGroup_iff_card_dvd_pow.mpr
    refine ⟨12, ?_⟩
    have hd : Nat.card (J ⊓ K : Subgroup M) ∣ 2 ^ 12 * 3 := by
      have hh := card_dvd_of_le (show J ⊓ K ≤ K from inf_le_right)
      rwa [show Nat.card K = 12288 from central_local_card] at hh
    have hcop : Nat.Coprime (Nat.card (J ⊓ K : Subgroup M)) 3 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        (fun hd => hthree (hd.trans (card_dvd_of_le (show J ⊓ K ≤ J from inf_le_left)))) |>.symm
    exact hcop.dvd_of_dvd_mul_right hd
  have he : J ⊓ K = unipotent P :=
    (unipotentSylow P rfl).is_maximal' htwo (le_inf hU hUK)
  rw [←he]
  apply (le_inf J.le_normalizer ?_).trans inf_normalizer_le_normalizer_inf
  exact hJ.trans ((normal_subgroupOf_iff_le_normalizer (localFactor_le_parabolic P .central)).mp
    inferInstance)

private theorem arms_normalizes (J : Subgroup M) [Group.IsSolvable J]
    (hU : unipotent P ≤ J) (hJ : J ≤ parabolic P .arms) :
    J ≤ normalizer (unipotent P : Set M) := by
  let K := localFactor P .arms
  have he : parabolic P .arms = K := parabolic_arms_eq_localFactor_at_two P rfl rfl
  have hJK : J ≤ K := hJ.trans_eq he
  have hUK : unipotent P ≤ K := hU.trans hJK
  let S := (unipotentSylow P rfl).subtype hUK
  let X := J.subgroupOf K
  let : Group.IsSolvable X := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hJK).toMonoidHom) (subgroupOfEquivOfLe hJK).injective
  let e := (localFactorArmsQuotientEquivPSL2 P rfl).trans
    (Theory.PSL2.sl2QuotientEquiv (ExtensionField P)).symm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hk : q.ker = pCore 2 K := by
    ext x
    exact e.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  have hX : X ≠ ⊤ := by
    intro ht
    have hh : J = K := le_antisymm hJK (subgroupOf_eq_top.mp ht)
    have hs : Group.IsSolvable K := hh ▸ inferInstanceAs (Group.IsSolvable J)
    let : Group.IsPerfect K := he ▸ parabolic_arms_isPerfect_at_two P rfl rfl
    have hn : Nontrivial K := by
      have hc : 1 < Nat.card K := by
        have hle := Nat.le_of_dvd Nat.card_pos (card_dvd_of_le hUK)
        rw [card_unipotent_binary P rfl] at hle
        change 4096 ≤ Nat.card K at hle
        omega
      exact Finite.one_lt_card_iff_nontrivial.mp hc
    exact Group.IsPerfect.not_isSolvable K hs
  have hn := Matrix.SpecialLinearGroup.proper_overgroup_le_sylow_normalizer_of_two_kernel
    q (e.surjective.comp (QuotientGroup.mk'_surjective _)) S
    (hk ▸ pCore_isPGroup.le_sylow_of_normal S) X (comap_mono hU) hX
  change X ≤ normalizer ((unipotent P).subgroupOf K : Set K) at hn
  rw [←subgroupOf_normalizer_eq hUK] at hn
  intro x hx
  exact hn (show (⟨x,hJK hx⟩ : K) ∈ X from hx)

/-- The binary endpoint admits Sylow control for solvable subgroups of order prime to three. -/
theorem standard_normalizes (J : Subgroup M) [Group.IsSolvable J]
    (hU : unipotent P ≤ J) (hthree : ¬ 3 ∣ Nat.card J) :
    J ≤ normalizer (unipotent P : Set M) := by
  have hproper : J ≠ ⊤ := by
    intro ht
    let : Group.IsSolvable (⊤ : Subgroup M) := ht ▸ inferInstanceAs (Group.IsSolvable J)
    let : Group.IsSolvable M := Group.isSolvable_of_surjective
      (f := (topEquiv (G := M)).toMonoidHom) (topEquiv (G := M)).surjective
    exact Group.IsPerfect.not_isSolvable M inferInstance
  obtain ⟨a,ha⟩ := OddSupplement.le_parabolic 1 Nat.zero_lt_one J hU hproper
  cases a with
  | arms => exact arms_normalizes J hU ha
  | central => exact central_normalizes J hU ha hthree

/-- The same result at an arbitrary supplied Sylow and an actual model equivalence. -/
theorem normalizes {G : Type*} [Group G] [Finite G]
    (e : G ≃* M) (S : Sylow 2 G) (J : Subgroup G) [Group.IsSolvable J]
    (hSJ : (S : Subgroup G) ≤ J) (hthree : ¬ 3 ∣ Nat.card J) :
    J ≤ normalizer (S : Set G) := by
  obtain ⟨_,a,_,ha⟩ := SolvableSylowControl.exists_aligned_equiv e S (unipotentSylow P rfl)
  change (S : Subgroup G).map a.toMonoidHom = unipotent P at ha
  let : Group.IsSolvable (J.map a.toMonoidHom) :=
    Group.isSolvable_of_surjective (a.toMonoidHom.subgroupMap_surjective J)
  have hn := standard_normalizes (J.map a.toMonoidHom) (ha ▸ map_mono hSJ)
    (by rw [card_map_of_injective a.injective]; exact hthree)
  rw [←ha,←map_equiv_normalizer_eq] at hn
  exact (map_le_map_iff_of_injective a.injective).mp hn

/-- A solvable subgroup of order prime to three which normalizes a binary
triality layer preserves that layer's prescribed full Sylow intersection. -/
theorem normalizes_layer_sylow {G : Type*} [Group G] [Finite G]
    (C J : Subgroup G) (e : C ≃* M) (S : Sylow 2 C) [Group.IsSolvable J]
    (hJC : J ≤ normalizer (C : Set G))
    (hSJ : (S : Subgroup C).map C.subtype ≤ J)
    (hthree : ¬ 3 ∣ Nat.card J) :
    J ≤ normalizer ((S : Subgroup C).map C.subtype : Set G) := by
  let X := J.subgroupOf C
  let f : X →* J := {
    toFun x := ⟨x.val.val, x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : J => (z : G)) he))
  let : Group.IsSolvable X := Group.isSolvable_of_isSolvable_injective hf
  have hSX : (S : Subgroup C) ≤ X := fun x hx => hSJ ⟨x,hx,rfl⟩
  have hn := normalizes e S X hSX
    (fun hd => hthree (hd.trans (card_dvd_of_injective f hf)))
  let U := (S : Subgroup C).map C.subtype
  have hUI : U ≤ J ⊓ C := le_inf hSJ (map_subtype_le _)
  have hIU : J ⊓ C ≤ normalizer (U : Set G) := by
    apply le_normalizer_iff.mpr
    intro j hj u hu
    obtain ⟨x,hx,rfl⟩ := hu
    exact ⟨(⟨j,hj.2⟩ : C) * x * (⟨j,hj.2⟩ : C)⁻¹,
      le_normalizer_iff.mp hn ⟨j,hj.2⟩ hj.1 x hx,rfl⟩
  have hcore : (J ⊓ C).pCoreIn 2 = U := by
    have hUC := le_pCoreIn_of_normalizes (S.isPGroup'.map C.subtype) hUI hIU
    have hIC : (J ⊓ C).pCoreIn 2 ≤ C := (pCoreIn_le 2 _).trans inf_le_right
    have hh := S.is_maximal' ((isPGroup_pCoreIn 2 (J ⊓ C : Subgroup G)).comap_subtype)
      (show (S : Subgroup C) ≤ ((J ⊓ C).pCoreIn 2).subgroupOf C from
        fun x hx => hUC ⟨x,hx,rfl⟩)
    have hm := congrArg (map C.subtype) hh
    change (((J ⊓ C).pCoreIn 2).subgroupOf C).map C.subtype = U at hm
    rwa [map_subgroupOf_eq_of_le hIC] at hm
  change J ≤ normalizer (U : Set G)
  rw [←hcore]
  exact ((le_inf J.le_normalizer hJC).trans inf_normalizer_le_normalizer_inf).trans
    (normalizer_le_normalizer_characteristic_image (J ⊓ C) (pCore 2 (J ⊓ C : Subgroup G)))

end Triality.Standard.BinaryThreeFreeSylow
