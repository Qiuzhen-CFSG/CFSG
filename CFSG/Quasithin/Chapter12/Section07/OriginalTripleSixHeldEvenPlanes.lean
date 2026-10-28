module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldSylowPlanes
public import Theory.GroupTheory.TwoElementaryPlanes

/-!
# Original plane normality in the even affine branch

If the given ambient Sylow lies in K, the actual quotient by O₂(K)=U gives
its order512. The component Sylow of order256 is therefore normal in T.
Since T normalizes U and the component Sylow has only two elementary64
planes, T normalizes the second plane too. All groups are the original
subgroups; no opposite-normalizer recognition is supplied as a premise.

Source: the even/full reduction preceding the missing comparison in
Aschbacher--Smith12.7.7, printed p.841.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The genuine even branch has order512 and an actual second elementary64
plane normalized by the entire original T. -/
theorem original_tripleSix_escaping_even_planes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬ centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (hTK : (T : Subgroup G)≤K) :
    Nat.card T=512 ∧ ∃ R W : Subgroup G,
      U≤R ∧ W≤R ∧ R≤(T : Subgroup G) ∧ Nat.card R=256 ∧
      IsElementaryAbelian 2 W ∧ Nat.card W=64 ∧ W≠U ∧
      U⊔W=R ∧ U⊓W=centerIn R ∧ Nat.card (centerIn R)=16 ∧
      (T : Subgroup G)≤normalizer (R : Set G) ⊓ normalizer (W : Set G) := by
  have hUcore := (original_tripleSix_escaping_core h structural D a t ht heven hout).1
  have hUc : Nat.card U=64 :=
    (Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans Atlas.Codes.hexacode_card
  have hcore : Nat.card (pCore 2 K)=64 := by
    have hh := congrArg (fun A : Subgroup G => Nat.card A) hUcore
    rw [pCoreIn,card_map_of_injective K.subtype_injective,hUc] at hh
    exact hh
  have hquot : Nat.card (K ⧸ pCore 2 K)=1080 :=
    (Nat.card_congr a.groupEquiv.toEquiv).trans Atlas.Codes.hexEven_card
  have hKc : Nat.card K=69120 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 K),hquot,hcore]
  have hTc : Nat.card T=512 := by
    have hh := (T.subtype hTK).card_eq_multiplicity
    change Nat.card ((T : Subgroup G).subgroupOf K)=2^(Nat.card K).factorization 2 at hh
    rw [Nat.card_congr (subgroupOfEquivOfLe hTK).toEquiv,hKc] at hh
    exact hh.trans (by decide +kernel)
  obtain ⟨k,hk,S,W,hUR,hWR,hRT,_,hRc,hWe,hWc,hne,hgen,hint,hZc,_,hcover⟩ :=
    original_tripleSix_escaping_sylow_planes h structural D a t ht heven hout
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  let R := ((S : Subgroup B).map B.subtype).map (MulAut.conj k).toMonoidHom
  have hidx : (R.subgroupOf (T : Subgroup G)).index=2 := by
    have hh := (R.subgroupOf (T : Subgroup G)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hRT).toEquiv,hRc,hTc] at hh
    omega
  have hRn : (R.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hidx
  have hTR : (T : Subgroup G)≤normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hRT).mp hRn
  have hTU : (T : Subgroup G)≤normalizer (U : Set G) :=
    hTK.trans D.normalizes
  have hTW : (T : Subgroup G)≤normalizer (W : Set G) :=
    normalizes_other_elementary_plane R U W (T : Subgroup G) hWR hWe
      (hUc.trans hWc.symm) hne hcover hTR hTU
  exact ⟨hTc,R,W,hUR,hWR,hRT,hRc,hWe,hWc,hne,hgen,hint,hZc,le_inf hTR hTW⟩

end CFSG.Quasithin.Chapter12.Section07
