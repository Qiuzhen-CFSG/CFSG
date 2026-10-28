module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreRecognition.SylowInputs.CubicPlane
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreRecognition.SylowInputs.TwoPart.CoreFixed
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreRecognition.SylowInputs.TwoPart.RootBound

/-!
# Sylow two-subgroups of the first cubic centralizer

The actual fixed subgroup C_Q(X) has order eight. For the upper bound,
choose an involution in the center of an arbitrary nontrivial two-subgroup
of C_G(X). Transport that involution, the cubic subgroup, and the
two-subgroup together to one of the two known involution centralizers.
The extraspecial-core calculation bounds the order by eight in the z-class;
the E₄ × A₅ model bounds it by four in the other class. A Sylow subgroup
containing C_Q(X) supplies the matching lower bound for every Sylow.

The transported cubic subgroup is kept literally as the image of X.
The cubic normal form applies to that seed as well, so no choice of a
normalizing Sylow subgroup or later three-local recognition is needed.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.3, printed p.262,
the assertion C_Q(X) ∈ Syl₂(C_G(X)).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreSylowInputs
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

omit [Finite G] in
private theorem map_centralizes (e : G ≃* G) {U Y : Subgroup G}
    (h : U ≤ centralizer (Y : Set G)) :
    U.map e.toMonoidHom ≤ centralizer (Y.map e.toMonoidHom : Set G) := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨y, hy, rfl⟩
  change e y * e u = e u * e y
  rw [← map_mul, ← map_mul, h hu y hy]

omit [Finite G] in
private theorem map_le_involutionCentralizer (e : G ≃* G) {U : Subgroup G} {u v : G}
    (he : e u = v) (h : U ≤ involutionCentralizer u) :
    U.map e.toMonoidHom ≤ involutionCentralizer v := by
  rintro _ ⟨a, ha, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  change e a * v = v * e a
  rw [← he, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp (h ha)]

/-- The two involution-centralizer models bound every two-subgroup of C_G(X). -/
theorem two_subgroup_card_le (E : EarlierConclusions D)
    (U : Subgroup G) (hU : IsPGroup 2 U) (hUC : U ≤ C D) : Nat.card U ≤ 8 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hn : Nat.card U = 1
  · omega
  let : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp
    (lt_of_le_of_ne Nat.card_pos (Ne.symm hn))
  let : Nontrivial (center U) := hU.center_nontrivial
  have hpZ : IsPGroup 2 (center U) := hU.to_subgroup (center U)
  obtain ⟨a, ha⟩ := exists_ne (1 : center U)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := center U) 2
    ((hpZ.dvd_orderOf ha).trans (_root_.orderOf_dvd_natCard a))
  let v : G := (u.val : G)
  have hv : orderOf v = 2 := (orderOf_coe u.val).trans ((orderOf_coe u).trans hu)
  have hUv : U ≤ involutionCentralizer v := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg (fun b : U => (b : G)) (mem_center_iff.mp u.property ⟨a, ha⟩)
  have hXv : D.X ≤ involutionCentralizer v := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (hUC u.val.property x hx)
  rcases E.geometry.other.classes v hv with hz | ht
  · obtain ⟨g, hg⟩ := isConj_iff.mp hz.symm
    let e := MulAut.conj g
    have he : e v = D.z := hg
    let D' : Seed G := {
      z := D.z
      localType := D.localType
      classes := D.classes
      X := D.X.map e.toMonoidHom
      card_X := (card_map_of_injective e.injective).trans D.card_X
      X_le := map_le_involutionCentralizer e he hXv }
    have hb := local_two_card_le D' (U.map e.toMonoidHom) (hU.map e.toMonoidHom)
      (map_le_involutionCentralizer e he hUv) (map_centralizes e hUC)
    rwa [card_map_of_injective e.injective] at hb
  · obtain ⟨g, hg⟩ := isConj_iff.mp ht.symm
    let e := MulAut.conj g
    have he : e v = E.geometry.t := hg
    have hb := root_two_card_le E.geometry.model
      (D.X.map e.toMonoidHom) (U.map e.toMonoidHom)
      ((card_map_of_injective e.injective).trans D.card_X) (hU.map e.toMonoidHom)
      (map_le_involutionCentralizer e he hXv)
      (map_le_involutionCentralizer e he hUv) (map_centralizes e hUC)
    rw [card_map_of_injective e.injective] at hb
    omega

/-- The source Sylow two-order, independent of second-cubic alternatives
and of all later recognition conclusions. -/
theorem two_card (E : EarlierConclusions D) (T : Sylow 2 (C D)) : Nat.card T = 8 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hhi : Nat.card T ≤ 8 := by
    have h := two_subgroup_card_le E ((T : Subgroup (C D)).map (C D).subtype)
      (T.isPGroup'.map (C D).subtype) (map_subtype_le _)
    rwa [card_map_of_injective (C D).subtype_injective] at h
  let R := ambientCore D.z ⊓ C D
  have hRC : R ≤ C D := inf_le_right
  have hR : Nat.card R = 8 := core_centralizer_card D
  have hpR : IsPGroup 2 R := IsPGroup.of_card (n := 3) hR
  have hp : IsPGroup 2 (R.subgroupOf (C D)) :=
    hpR.of_equiv (subgroupOfEquivOfLe hRC).symm
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have hlo := card_le_of_le hS
  rw [Nat.card_congr (subgroupOfEquivOfLe hRC).toEquiv, hR,
    Nat.card_congr (S.equiv T).toEquiv] at hlo
  omega

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreSylowInputs
