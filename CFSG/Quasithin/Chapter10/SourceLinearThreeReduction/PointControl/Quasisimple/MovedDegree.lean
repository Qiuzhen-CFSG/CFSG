module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.CentralQuotient
public import Theory.Representation.SL2.MovedElementaryDegree
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import GorensteinWalter.PSL2Cardinality

/-!
# The size of the actual moved image in a containing central quotient

The literal quotient map preserves the original L/O₂(L). Its nonzero
fully moved elementary image contains a noncentral chief factor, so an
original PSL₂(2ⁿ) quotient forces image size at least 2²ⁿ. That image lies
in the intrinsic two-core of the local image, giving the stronger divisor
2³ⁿ(2²ⁿ−1) of the containing central quotient. Fixed vectors are retained;
no irreducibility or splitting premise is added. The degree-two exception
is recognized through the actual PSL₂(4) isomorphism with A₅.

Source: Aschbacher–Smith E.2.13(4), p.225, and 10.2.9, pp.750–751.
Other.RankOne applies these bounds to the actual complementary carriers.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

theorem center_moved_card_of_binary_quotient [Group.IsPerfect I]
    {n : ℕ} (hn : 0 < n) (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    2 ^ (2 * n) ≤ Nat.card (((⁅D.fullModule,L⁆).subgroupOf I).map
      (QuotientGroup.mk' (center I))) := by
  obtain ⟨F,hfield,hfinite,hF,⟨eL⟩⟩ := hL
  let := hfield
  let := hfinite
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨S,_,hB,_,_,_,_,hE,hEB,hne,hm⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let E := ((⁅D.fullModule,L⁆).subgroupOf I).map q
  let := hB.perfect
  let e := subgroupOfEquivOfLe
    (show B ≤ B ⊔ (S.mapSurjective (QuotientGroup.mk'_surjective (center I)) :
      Subgroup (I ⧸ center I)) from le_sup_left)
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : IsElementaryAbelian 2 E := hE
  let d : (B ⧸ pCore 2 B) ≃* SL(2,F) :=
    ((markedCoreQuotientEquiv D c.strict.le (MulEquiv.refl _)).symm.trans eL).trans
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  exact Representation.SL2.moved_subgroup_card_bound B E hEB hne hm d (by omega) hF

/-- The marked central quotient has rank at least twice the original binary degree. -/
theorem center_quotient_rank_of_binary_quotient [Group.IsPerfect I]
    {n : ℕ} (hn : 0 < n) (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    2 * n ≤ primeRank 2 (I ⧸ center I) := by
  obtain ⟨_,_,_,_,_,_,_,hE,_⟩ := center_quotient_data D c
  have hu := (primeRank_le_iff_elementary_card_le (I ⧸ center I)).mp le_rfl _ hE
  have hl := center_moved_card_of_binary_quotient D c hn hL
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hl.trans hu)

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple

namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}
omit [Finite G] in
theorem two_lt_binary_degree_of_not_alternating_five
    {n : ℕ} (hn : 1 < n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) : 2 < n := by
  by_contra! hsmall
  have he : n = 2 := by omega
  subst n
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hL
  exact hna ⟨e.trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (by simpa using hF)).some⟩
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple

namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

theorem binary_quotient_moved_order_dvd [Group.IsPerfect I]
    {n : ℕ} (hn : 0 < n) (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    2 ^ (3 * n) * ((2 ^ n) ^ 2 - 1) ∣ Nat.card (I ⧸ center I) := by
  obtain ⟨F,hfield,hfinite,hF,⟨eL⟩⟩ := hL
  let := hfield
  let := hfinite
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨S,_,hB,_,_,_,_,hE,hEB,hne,hm⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let E := ((⁅D.fullModule,L⁆).subgroupOf I).map q
  let := hB.perfect
  let e := subgroupOfEquivOfLe
    (show B ≤ B ⊔ (S.mapSurjective (QuotientGroup.mk'_surjective (center I)) :
      Subgroup (I ⧸ center I)) from le_sup_left)
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : IsElementaryAbelian 2 E := hE
  let d : (B ⧸ pCore 2 B) ≃* SL(2,F) :=
    ((markedCoreQuotientEquiv D c.strict.le (MulEquiv.refl _)).symm.trans eL).trans
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  let U := E.subgroupOf B
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_iff_commutator_le_left.mpr hm.le)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hEB
  have hu : U ≠ ⊥ := by
    intro hz
    have hh := congrArg (map B.subtype) hz
    rw [map_subgroupOf_eq_of_le hEB,Subgroup.map_bot] at hh
    exact hne hh
  have hmU : ⁅U,(⊤ : Subgroup B)⁆ = U := by
    apply map_injective B.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hEB,← MonoidHom.range_eq_map,range_subtype]
    exact hm
  have hd := (Representation.SL2.moved_elementary_order_dvd U hu hmU d
    (by omega) hF).trans B.card_subgroup_dvd_card
  rw [Nat.card_congr d.toEquiv,GorensteinWalter.sl2_card_formula,hF,
    ←mul_assoc,←pow_add,show 2*n+n=3*n by omega] at hd
  exact hd
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple
