module
public import Theory.SpecificGroups.Triality.BinaryCentralResidual
public import Theory.SpecificGroups.Triality.BinaryLocalResidual
public import Theory.SpecificGroups.Triality.BinarySolvableEscape
public import Theory.GroupTheory.PResidual.NormalSubgroup
import all Theory.SpecificGroups.Triality.BinaryCentralResidual

/-!
# Fixed subgroups in the binary triality central parabolic

A subgroup of the positive Sylow normalized by that Sylow and centralized
by an escaping solvable supplement is trivial. The action of their join
on this subgroup factors through a two-group. Its three-residual therefore
acts trivially, whereas the central rank-one cubic has no nonidentity fixed
point in the highest-root center. Normality inside the Sylow completes the
argument. Both possible central parabolic sections are retained.

The marked form keeps the actual perfect arms subgroup and transports the
supplied Sylow. The internal import shares the cubic and highest-root
calculation with BinaryCentralResidual without changing its public API.
Source: Aschbacher--Smith 5.1.13, printed pp.635--638, refs/quasithin.pdf;
GLS3 §§2.4 and 2.6 for the concrete root conventions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Triality.Standard.BinaryCentralFixedSubgroup
open Parabolics Parabolics.BinaryCentralResidual
open RadicalCoordinates.Centers RadicalCoordinates.Centers.UnipotentMatrices
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "M" => BinaryCarrier 1 Nat.zero_lt_one

private theorem cubic_mem_local :
    toCarrier P (cubicElementary P rfl) ∈ localFactor P .central := by
  let J := parabolic P .central
  let N := (localFactor P .central).subgroupOf J
  let x : J := ⟨_,cubicElementary_mem P rfl⟩
  let q := QuotientGroup.mk' N
  have hc : q x ^ 3 = 1 := by
    rw [←map_pow]
    have hh : x ^ 3 = 1 := Subtype.ext (carrier_cube P rfl)
    rw [hh,map_one]
  have hd : orderOf (q x) ∣ 7 :=
    (orderOf_dvd_natCard (q x)).trans (localFactor_relIndex_dvd_seven P rfl .central)
  have he : q x = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 3 7)
      (orderOf_dvd_of_pow_eq_one hc) hd)
  exact (QuotientGroup.eq_one_iff x).mp he

/-- A Sylow-normalized subgroup fixed by the supplement vanishes when their
join is either actual central parabolic section in binary triality. -/
theorem fixed_subgroup_eq_bot (A V : Subgroup M)
    (hV : V ≤ unipotent P)
    (hn : unipotent P ≤ normalizer (V : Set M))
    (hf : A ≤ centralizer (V : Set M))
    (hJ : A ⊔ unipotent P = localFactor P .central ∨
      A ⊔ unipotent P = parabolic P .central) : V = ⊥ := by
  let J := A ⊔ unipotent P
  have hUJ : unipotent P ≤ J := le_sup_right
  have hJN : J ≤ normalizer (V : Set M) :=
    sup_le (hf.trans (Subgroup.centralizer_le_normalizer _)) hn
  let D := (centralizer (V : Set M)).subgroupOf J
  let : D.Normal := normal_subgroupOf_of_le_normalizer
    (hJN.trans (normalizer_le_normalizer_centralizer V))
  have hgen : D ⊔ (unipotent P).subgroupOf J = ⊤ := by
    apply top_unique
    intro x _
    have hx : (x : M) ∈ J := x.property
    have hle : J ≤ (D ⊔ (unipotent P).subgroupOf J).map J.subtype := by
      apply sup_le
      · intro a ha
        exact mem_map_of_mem J.subtype
          (mem_sup_left (show (⟨a,mem_sup_left ha⟩ : J) ∈ D from hf ha))
      · intro s hs
        exact mem_map_of_mem J.subtype
          (mem_sup_right (show (⟨s,mem_sup_right hs⟩ : J) ∈ (unipotent P).subgroupOf J from hs))
    obtain ⟨y,hy,he⟩ := hle hx
    exact (show y = x from Subtype.ext he) ▸ hy
  have htwo : IsPGroup 2 (J ⧸ D) := isPGroup_quotient_of_sup_eq_top D
    ((unipotent P).subgroupOf J) (unipotent_isPGroup_binary P rfl).comap_subtype hgen
  have hthree : (primePowerGenerated 3 J).map J.subtype ≤ centralizer (V : Set M) := by
    rw [map_le_iff_le_comap,primePowerGenerated_le_iff]
    intro j k hk
    let q := QuotientGroup.mk' D
    have hpow : q j ^ (3 ^ k) = 1 := by rw [←map_pow,hk,map_one]
    obtain ⟨l,hl⟩ := (isPGroup_iff_orderOf_dvd_pow.mp htwo) (q j)
    have he : q j = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 2 3).pow l k)
        hl (orderOf_dvd_of_pow_eq_one hpow))
    change j ∈ D
    exact (QuotientGroup.eq_one_iff j).mp he
  have hzero : unipotent P ⊓ centralizer
      ((primePowerGenerated 3 J).map J.subtype : Set M) = ⊥ := by
    apply centralizer_eq_bot_of_center (unipotent P) J hUJ
      (unipotent_isPGroup_binary P rfl)
    intro z hz hc
    have hzH : z.val ∈ highestRoot P := by
      rw [←embedded_center_unipotent P rfl]
      exact ⟨z,hz,rfl⟩
    rw [←highestHom_range P rfl] at hzH
    obtain ⟨t,ht⟩ := hzH
    have hxJ : toCarrier P (cubicElementary P rfl) ∈ J := by
      rcases hJ with he | he
      · rw [show J = localFactor P .central from he]
        exact cubic_mem_local
      · rw [show J = parabolic P .central from he]
        exact cubicElementary_mem P rfl
    have hx : (⟨_,hxJ⟩ : J) ∈ primePowerGenerated 3 J :=
      mem_primePowerGenerated_of_pow (n := 1) (Subtype.ext (carrier_cube P rfl))
    have hcomm := hc _ hx
    have ht0 := highest_commuting_cubic P rfl t.toAdd (commute_congr rfl ht.symm hcomm)
    have ht1 : t = 1 := congrArg Multiplicative.ofAdd ht0
    apply Subtype.ext
    exact ht.symm.trans ((congrArg (highestHom P rfl) ht1).trans (map_one _))
  exact bot_unique ((le_inf hV (le_centralizer_iff.mp hthree)).trans_eq hzero)

/-- With the actual arms subgroup retained, an escaping solvable supplement
cannot fix a nontrivial Sylow-normalized subgroup. -/
theorem marked_fixed_subgroup_eq_bot {G : Type*} [Group G] [Finite G]
    (e : G ≃* M) (S : Sylow 2 G) (R A V : Subgroup G)
    [Group.IsPerfect R] [Group.IsSolvable (A ⊔ (S : Subgroup G) : Subgroup G)]
    (hR : R ≠ ⊤) (hns : ¬ Group.IsSolvable R)
    (hSR : (S : Subgroup G) ≤ normalizer (R : Set G))
    (hAR : ¬ A ≤ normalizer (R : Set G))
    (hVS : V ≤ (S : Subgroup G))
    (hSV : (S : Subgroup G) ≤ normalizer (V : Set G))
    (hAV : A ≤ centralizer (V : Set G)) : V = ⊥ := by
  obtain ⟨a,ha,hr⟩ := BinaryLocalSections.marked_arms e S R hR hns hSR
  let D := A.map a.toMonoidHom
  let W := V.map a.toMonoidHom
  have hj : (A ⊔ (S : Subgroup G)).map a.toMonoidHom = D ⊔ unipotent P := by
    rw [Subgroup.map_sup,ha]
  let : Group.IsSolvable (D ⊔ unipotent P : Subgroup M) := hj ▸
    Group.isSolvable_of_surjective (a.toMonoidHom.subgroupMap_surjective
      (A ⊔ (S : Subgroup G)))
  have hn : ¬ D ⊔ unipotent P ≤ normalizer (unipotent P : Set M) := by
    intro hn
    have hDR : D ≤ R.map a.toMonoidHom := by
      rw [hr]
      exact ((show D ≤ D ⊔ unipotent P from le_sup_left).trans hn).trans
        ((ConcreteBruhat.normalizer_unipotent_eq_borel P rfl).le.trans
          (borel_le_parabolic P .arms))
    exact hAR (((map_le_map_iff_of_injective a.injective).mp hDR).trans R.le_normalizer)
  have hz := fixed_subgroup_eq_bot D W
    ((map_mono hVS).trans_eq ha)
    (ha ▸ (map_mono hSV).trans (le_normalizer_map a.toMonoidHom))
    ((map_mono hAV).trans (map_centralizer_le_centralizer_image V a.toMonoidHom))
    (BinarySolvableEscape.standard_cases _ le_sup_right hn)
  apply (map_injective (f := a.toMonoidHom) a.injective)
  simpa only [Subgroup.map_bot] using hz

end Triality.Standard.BinaryCentralFixedSubgroup
