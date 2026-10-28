module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.CarrierReduction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.NormalElementaryBound
public import Theory.Mathieu.M11.Properties.SylowTwo
public import Theory.GroupTheory.SemidihedralNormalElementary
public import Theory.Mathieu.M12.SylowOvergroups.RankTwoCoverage
public import Theory.GroupTheory.TwoThreeSolvable

/-!
# Three small sporadic exclusions on the original moved subgroup

The elementary image in the central quotient has at least eight elements:
it is a nontrivial commutator under a perfect action. Its normalization by
an actual full Sylow excludes J₂ and M₁₁, whose normal elementary subgroups
have order at most four and two. For M₁₂, every proper full-Sylow overgroup
has order dividing 192 and is solvable. Thus the original proper local
C-component cannot occur.

These arguments use neither the A₅-specific sixteen-element bound nor a
recognition of an irreducible module. The literal quotient images and full
Sylow from `Preparation` are used throughout.
Source: Aschbacher--Smith A.3.12 and 10.2.9, pp.47--48,750--751;
the native Sylow calculations cite GLS3 Tables 5.3a,b,g.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02 ChapterA.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- The nonzero fully moved elementary image has at least eight elements. -/
theorem center_moved_card [Group.IsPerfect I] :
    8 ≤ Nat.card (((⁅D.fullModule,L⁆).subgroupOf I).map
      (QuotientGroup.mk' (center I))) := by
  obtain ⟨S,_,hB,_,_,_,_,hE,hEB,hne,hm⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let E := ((⁅D.fullModule,L⁆).subgroupOf I).map q
  let := hB.perfect
  let e := subgroupOfEquivOfLe
    (show B ≤ B ⊔ (S.mapSurjective (QuotientGroup.mk'_surjective (center I)) :
      Subgroup (I ⧸ center I)) from le_sup_left)
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  let : IsElementaryAbelian 2 E := hE
  let W := E.subgroupOf B
  let : W.Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_iff_commutator_le_left.mpr hm.le)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hEB
  let : Group.IsPerfect (⊤ : Subgroup B) := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := B)).symm.toMonoidHom) (topEquiv (G := B)).symm.surjective
  have hmove : ⁅W,(⊤ : Subgroup B)⁆ = W := by
    apply map_injective B.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hEB,← MonoidHom.range_eq_map,
      range_subtype]
    exact hm
  have hW : W ≠ ⊥ := by
    intro hz
    have hh := congrArg (map B.subtype) hz
    rw [map_subgroupOf_eq_of_le hEB,Subgroup.map_bot] at hh
    exact hne hh
  have hc := commutator_card_ge_eight_of_isPerfect (⊤ : Subgroup B) W
    (IsElementaryAbelian.isPGroup 2 W) (by rwa [hmove])
  rw [hmove,Nat.card_congr (subgroupOfEquivOfLe hEB).toEquiv] at hc
  exact hc

omit D c in
private theorem elementary_le_sylow {H : Type*} [Group H]
    (S : Sylow 2 H) (E : Subgroup H) (hE : IsElementaryAbelian 2 E)
    (hn : (S : Subgroup H) ≤ normalizer (E : Set H)) : E ≤ S := by
  let := hE
  exact sup_eq_left.mp (S.is_maximal'
    (S.isPGroup'.to_sup_of_normal_right' (IsElementaryAbelian.isPGroup 2 E) hn)
    le_sup_left)

omit D c in
private theorem normalized_bound_of_equiv {H K : Type*} [Group H] [Group K]
    [Finite H] [Finite K] (e : H ≃* K) {n : ℕ}
    (hb : ∀ (S : Sylow 2 K) (E : Subgroup K), IsElementaryAbelian 2 E →
      (S : Subgroup K) ≤ normalizer (E : Set K) → Nat.card E ≤ n)
    (S : Sylow 2 H) (E : Subgroup H) (hE : IsElementaryAbelian 2 E)
    (hn : (S : Subgroup H) ≤ normalizer (E : Set H)) : Nat.card E ≤ n := by
  let := hE
  have hh := hb (S.mapSurjective (f := e.toMonoidHom) e.surjective)
    (E.map e.toMonoidHom) (IsElementaryAbelian.map e.toMonoidHom)
    ((map_mono hn).trans (E.le_normalizer_map e.toMonoidHom))
  rwa [card_map_of_injective e.injective] at hh

omit D c in
private theorem j2_bound (S : Sylow 2 Sporadic.LeechRelated.J2.Carrier)
    (E : Subgroup Sporadic.LeechRelated.J2.Carrier) (hE : IsElementaryAbelian 2 E)
    (hn : (S : Subgroup Sporadic.LeechRelated.J2.Carrier) ≤
      normalizer (E : Set Sporadic.LeechRelated.J2.Carrier)) : Nat.card E ≤ 4 := by
  let := hE
  have hES := elementary_le_sylow S E hE hn
  have hh := Sporadic.LeechRelated.J2.sylow_normal_elementary_card_le_four S
    (E.subgroupOf S) ((normal_subgroupOf_iff_le_normalizer hES).mpr hn)
    (IsElementaryAbelian.subgroupOf hES)
  rwa [Nat.card_congr (subgroupOfEquivOfLe hES).toEquiv] at hh

/-- J₂ cannot contain the actual normalized, fully moved elementary image. -/
theorem not_jankoTwo [Group.IsPerfect I]
    (e : (I ⧸ center I) ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  obtain ⟨S,_,_,_,hn,_,_,hE,_⟩ := center_quotient_data D c
  have hu := normalized_bound_of_equiv e j2_bound
    (S.mapSurjective (QuotientGroup.mk'_surjective (center I))) _ hE hn
  have hl := center_moved_card D c
  omega

omit D c in
private theorem m11_bound (S : Sylow 2 Sporadic.Mathieu.M11)
    (E : Subgroup Sporadic.Mathieu.M11) (hE : IsElementaryAbelian 2 E)
    (hn : (S : Subgroup Sporadic.Mathieu.M11) ≤
      normalizer (E : Set Sporadic.Mathieu.M11)) : Nat.card E ≤ 2 := by
  let := hE
  have hES := elementary_le_sylow S E hE hn
  obtain ⟨P,a,b,ha,hb,hc,hg⟩ := Sporadic.Mathieu.m11_exists_semidihedral_sylow
  let e := S.equiv P
  let R := (E.subgroupOf S).map e.toMonoidHom
  let : (E.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer hES).mpr hn
  let : IsElementaryAbelian 2 (E.subgroupOf S) := IsElementaryAbelian.subgroupOf hES
  let : R.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.map e.toMonoidHom
  have hcard : Nat.card R = Nat.card E :=
    (card_map_of_injective e.injective).trans
      (Nat.card_congr (subgroupOfEquivOfLe hES).toEquiv)
  rw [←hcard]
  by_cases hR : R = ⊥
  · rw [hR,card_bot]
    decide
  · rw [Semidihedral.normal_elementary_eq_of_order_sixteen a b ha hb hc hg R hR,
      Nat.card_zpowers,orderOf_pow,ha]
    decide

/-- M₁₁ cannot contain the original normalized elementary image. -/
theorem not_mathieuEleven [Group.IsPerfect I]
    (e : (I ⧸ center I) ≃* Sporadic.Mathieu.M11) : False := by
  obtain ⟨S,_,_,_,hn,_,_,hE,_⟩ := center_quotient_data D c
  have hu := normalized_bound_of_equiv e m11_bound
    (S.mapSurjective (QuotientGroup.mk'_surjective (center I))) _ hE hn
  have hl := center_moved_card D c
  omega

omit D c in
private theorem m12_solvable (S : Sylow 2 Sporadic.Mathieu.M12)
    (P : Subgroup Sporadic.Mathieu.M12) (hSP : (S : Subgroup Sporadic.Mathieu.M12) ≤ P)
    (hne : P ≠ ⊤) : Group.IsSolvable P := by
  have hd := Sporadic.Mathieu.M12SmallPair.SylowOvergroups.card_dvd_192_of_ne_top P hne ⟨S,hSP⟩
  apply isSolvable_of_prime_dvd_card_eq_two_or_three P
  intro p hp hpd
  have hh : p ∣ 2*2*2*2*2*2*3 := hpd.trans hd
  simpa only [hp.dvd_mul,or_self,
    Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
    Nat.prime_dvd_prime_iff_eq hp Nat.prime_three] using hh

/-- Every proper full-Sylow overgroup in M₁₂ is solvable, excluding the
literal proper local C-component. -/
theorem not_mathieuTwelve [IsQuasisimple I]
    (e : (I ⧸ center I) ≃* Sporadic.Mathieu.M12) : False := by
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  let : IsQuasisimple (I ⧸ center I) := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center I)) (QuotientGroup.mk'_surjective (center I))
  obtain ⟨S,_,hB,_,_,hproper,_⟩ := center_quotient_data D c
  have ht : (⊤ : Subgroup (I ⧸ center I)).IsCComponent :=
    (show IsComponent (I ⧸ center I) ⊤ from
      ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  apply hproper
  apply SourceEmbeddings.eq_of_solvable_sylow_overgroups
    (S.mapSurjective (QuotientGroup.mk'_surjective (center I))) hB ht le_top
  exact isSolvable_proper_sylow_overgroup_of_equiv (topEquiv.trans e) m12_solvable

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
