module
public import Theory.SpecificGroups.Triality.BinaryThreeFreeSylow
public import Theory.SpecificGroups.Triality.SylowParabolicExtensions
public import Theory.SpecificGroups.Triality.BinaryParabolicThreeRank
import all Theory.SpecificGroups.Triality.BinaryThreeFreeSylow

/-!
# Solvable Sylow movement in the binary triality endpoint

A solvable subgroup containing the full positive Sylow and moving it lies
in the central root parabolic: the arms parabolic already has Sylow control.
Its intersection with the central local factor contains the Sylow with index
three. Failure to normalize the Sylow forces that intersection to be the
whole local factor. The remaining full-parabolic quotient has order dividing
seven, so there are exactly two possibilities: the central local factor or
the full central parabolic.

The relative theorem applies to the literal intersection with a normalized
triality layer and retains any supplied Sylow marking. If this intersection
normalized the Sylow, that Sylow would be its characteristic two-core and
would also be normalized by the ambient solvable subgroup.

The internal import shares the elementary arms and central-order calculations
with BinaryThreeFreeSylow without changing that module's public boundary.
Source: Aschbacher--Smith 5.1.13, printed p.636; GLS3 §§2.3--2.6 for the
actual graph-field parabolics. The original local Cartan application is in
RankOneModuleGenericExceptionalCartanLocalBinaryCentral.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Triality.Standard.BinarySolvableEscape
open Parabolics
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "M" => BinaryCarrier 1 Nat.zero_lt_one

private theorem central_local_le (J : Subgroup M)
    (hU : unipotent P ≤ J) (hJ : J ≤ parabolic P .central)
    (hn : ¬ J ≤ normalizer (unipotent P : Set M)) : localFactor P .central ≤ J := by
  let K := localFactor P .central
  let X := J ⊓ K
  have hUK : unipotent P ≤ K :=
    sylow_le_localFactor P .central (unipotentSylow P rfl)
      ((unipotent_le_borel P).trans (borel_le_parabolic P .central))
  have hUX : unipotent P ≤ X := le_inf hU hUK
  have hcU : Nat.card (unipotent P) = 4096 := card_unipotent_binary P rfl
  have hcK : Nat.card K = 12288 := BinaryThreeFreeSylow.central_local_card
  have hi : (unipotent P).relIndex K = 3 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup M) (unipotent P) K bot_le hUK
    rw [relIndex_bot_left,relIndex_bot_left,hcU,hcK] at hh
    omega
  have hmul := relIndex_mul_relIndex (unipotent P) X K hUX inf_le_right
  rw [hi] at hmul
  have hd : (unipotent P).relIndex X ∣ 3 := dvd_of_mul_right_eq _ hmul
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with he | he
  · have hXU : X = unipotent P := le_antisymm (relIndex_eq_one.mp he) hUX
    apply (hn ?_).elim
    rw [←hXU]
    exact (le_inf J.le_normalizer (hJ.trans
      ((normal_subgroupOf_iff_le_normalizer (localFactor_le_parabolic P .central)).mp
        inferInstance))).trans inf_normalizer_le_normalizer_inf
  · have hXK : X.relIndex K = 1 := by rw [he] at hmul; omega
    exact (relIndex_eq_one.mp hXK).trans inf_le_left

/-- A solvable positive-Sylow overgroup which moves that Sylow contains
exactly the central local factor or the full central parabolic. -/
theorem standard_cases (J : Subgroup M) [Group.IsSolvable J]
    (hU : unipotent P ≤ J) (hn : ¬ J ≤ normalizer (unipotent P : Set M)) :
    J = localFactor P .central ∨ J = parabolic P .central := by
  have hproper : J ≠ ⊤ := by
    intro ht
    let : Group.IsSolvable (⊤ : Subgroup M) := ht ▸ inferInstanceAs (Group.IsSolvable J)
    exact Group.IsPerfect.not_isSolvable M (Group.isSolvable_of_surjective
      (f := (topEquiv (G := M)).toMonoidHom) (topEquiv (G := M)).surjective)
  obtain ⟨a,ha⟩ := OddSupplement.le_parabolic 1 Nat.zero_lt_one J hU hproper
  cases a with
  | arms => exact (hn (BinaryThreeFreeSylow.arms_normalizes J hU ha)).elim
  | central =>
    have hKJ := central_local_le J hU ha hn
    have hd := localFactor_relIndex_dvd_seven P rfl .central
    have hmul := relIndex_mul_relIndex (localFactor P .central) J (parabolic P .central) hKJ ha
    have hj : (localFactor P .central).relIndex J ∣ 7 :=
      (dvd_of_mul_right_eq _ hmul).trans hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hj with he | he
    · exact Or.inl (le_antisymm (relIndex_eq_one.mp he) hKJ)
    · have hi : J.relIndex (parabolic P .central) = 1 := by
        rw [he] at hmul
        have hp := Nat.le_of_dvd (by decide : 0 < 7) hd
        have hpos : 0 < J.relIndex (parabolic P .central) :=
          Nat.card_pos
        omega
      exact Or.inr (le_antisymm ha (relIndex_eq_one.mp hi))

/-- Failure to preserve the layer Sylow occurs already in the literal
intersection with that layer. -/
private theorem intersection_not_normalizes {G : Type*} [Group G] [Finite G]
    (C J : Subgroup G) (S : Sylow 2 C)
    (hJC : J ≤ normalizer (C : Set G))
    (hSJ : (S : Subgroup C).map C.subtype ≤ J)
    (hnot : ¬ J ≤ normalizer ((S : Subgroup C).map C.subtype : Set G)) :
    ¬ J.subgroupOf C ≤ normalizer (S : Set C) := by
  intro hn
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
  apply hnot
  change J ≤ normalizer (U : Set G)
  rw [←hcore]
  exact ((le_inf J.le_normalizer hJC).trans inf_normalizer_le_normalizer_inf).trans
    (normalizer_le_normalizer_characteristic_image (J ⊓ C) (pCore 2 (J ⊓ C : Subgroup G)))

/-- On an actual binary-triality layer, a solvable Sylow-moving overgroup
has central local factor or full central parabolic as its literal intersection. -/
theorem layer_cases {G : Type*} [Group G] [Finite G]
    (C J : Subgroup G) [Group.IsSolvable J] (S : Sylow 2 C)
    (e : C ≃* M) (hmark : (S : Subgroup C).map e.toMonoidHom = unipotent P)
    (hJC : J ≤ normalizer (C : Set G))
    (hSJ : (S : Subgroup C).map C.subtype ≤ J)
    (hnot : ¬ J ≤ normalizer ((S : Subgroup C).map C.subtype : Set G)) :
    (J.subgroupOf C).map e.toMonoidHom = localFactor P .central ∨
      (J.subgroupOf C).map e.toMonoidHom = parabolic P .central := by
  let X := J.subgroupOf C
  let : Group.IsSolvable X := Group.isSolvable_of_isSolvable_injective
    (f := C.subtype.subgroupComap J) (by
      intro x y he
      exact Subtype.ext (Subtype.ext (congrArg (fun z : J => (z : G)) he)))
  let : Group.IsSolvable (X.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective X)
  apply standard_cases (X.map e.toMonoidHom)
  · rw [←hmark]
    exact map_mono (fun x hx => hSJ (mem_map_of_mem C.subtype hx))
  · intro hn
    rw [←hmark,←map_equiv_normalizer_eq] at hn
    exact intersection_not_normalizes C J S hJC hSJ hnot
      ((map_le_map_iff_of_injective e.injective).mp hn)

end Triality.Standard.BinarySolvableEscape
