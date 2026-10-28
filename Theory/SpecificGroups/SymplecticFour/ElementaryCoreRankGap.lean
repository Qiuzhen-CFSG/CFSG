module
public import Theory.SpecificGroups.SymplecticFour.ElementaryCoreRankGap.Contracts
public import Theory.SpecificGroups.SymplecticFour.ElementaryCoreRankGap.PlaneImage
public import Theory.SpecificGroups.SymplecticFour.ElementaryCoreRankGap.RankOne
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.Parabolics
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.GroupTheory.PrimeRankElementary

/-!
# The intrinsic symplectic two-core rank gap

Let A have the maximum elementary order q³ in a faithfully represented
subgroup H of Sp₄(q). When O₂(H) is trivial, A retains its whole rank 3f.
Otherwise the two-local cover embeds H into a point or plane parabolic;
the actual exceptional graph automorphism converts the point case to the
plane case without changing H or its intrinsic quotient.

Inside the full plane parabolic, every element of A has determinant one.
Normal restriction therefore preserves its two-core quotient rank. The
plane-local projection has a two-group kernel, so the intrinsic core and
quotient rank transfer to its actual SL₂ image. The plane image bound and
rank-one core control then finish the implication. The conditional reductions
remain available, while `le_core_of_rank_lt` discharges both local inputs
using their concrete matrix proofs. The argument also works over the binary
field; only the later comparison with the derived group needs q > 2.

Source: Aschbacher--Smith, E.1.1--6 and E.1.14(1), printed pp.209--211,
214, citing Aschbacher [Asc82a], Lemma 4.7. The parabolic coordinates are
those used in F.1.12(I)(2).
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.ElementaryCoreRankGap

private theorem rank_range_eq {D X Y : Type*} [Group D] [Finite D]
    [Group X] [Group Y] (f : D →* X) (g : D →* Y) (h : f.ker = g.ker) :
    Group.rank f.range = Group.rank g.range :=
  Group.rank_congr ((QuotientGroup.quotientKerEquivRange f).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans
      (QuotientGroup.quotientKerEquivRange g)))

private theorem rank_core_map_eq {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (f : X →* Y) (hf : (pCore 2 Y).comap f = pCore 2 X) (A : Subgroup X) :
    Group.rank (A.map (QuotientGroup.mk' (pCore 2 X))) =
      Group.rank ((A.map f).map (QuotientGroup.mk' (pCore 2 Y))) := by
  let a := (QuotientGroup.mk' (pCore 2 X)).comp A.subtype
  let b := (QuotientGroup.mk' (pCore 2 Y)).comp (f.comp A.subtype)
  have hk : a.ker = b.ker := by
    ext x
    change (QuotientGroup.mk' (pCore 2 X)) x.val = 1 ↔
      (QuotientGroup.mk' (pCore 2 Y)) (f x.val) = 1
    simp only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Iff.of_eq (congrArg (fun S : Subgroup X => x.val ∈ S) hf.symm)
  have ha : a.range = A.map (QuotientGroup.mk' (pCore 2 X)) := by
    change ((QuotientGroup.mk' (pCore 2 X)).comp A.subtype).range = _
    rw [MonoidHom.range_comp, range_subtype]
  have hb : b.range = (A.map f).map (QuotientGroup.mk' (pCore 2 Y)) := by
    change ((QuotientGroup.mk' (pCore 2 Y)).comp (f.comp A.subtype)).range = _
    rw [MonoidHom.range_comp, MonoidHom.range_comp, range_subtype]
  exact (Group.rank_congr (MulEquiv.subgroupCongr ha)).symm.trans
    ((rank_range_eq a b hk).trans (Group.rank_congr (MulEquiv.subgroupCongr hb)))

private theorem rank_core_eq_of_bot {X : Type*} [Group X] [Finite X]
    (hc : pCore 2 X = ⊥) (A : Subgroup X) :
    Group.rank (A.map (QuotientGroup.mk' (pCore 2 X))) = Group.rank A := by
  have hi : Function.Injective (QuotientGroup.mk' (pCore 2 X)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rwa [QuotientGroup.ker_mk']
  exact (Group.rank_congr (equivMapOfInjective A _ hi)).symm

private theorem rank_ge_of_elementary_card {X : Type*} [Group X] [Finite X]
    [IsElementaryAbelian 2 X] {n : ℕ} (h : 2 ^ n ≤ Nat.card X) :
    n ≤ Group.rank X := by
  let _ : CommGroup X := IsMulCommutative.instCommGroup
  have hp : ∀ x : X, x ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 X)
  have hb : Nat.card X ≤ 2 ^ Group.rank X :=
    Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' X hp)
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (h.trans hb)

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The rank-one and plane image calculations imply the intrinsic rank gap
for every faithfully represented subgroup of the determinant-one plane local. -/
theorem planeLocal_le_core_of_local_facts
    (hplane : PlaneImageBound F) (hsl : RankOneCoreControl F)
    {f : ℕ} (hF : Nat.card F = 2 ^ f)
    {H : Type*} [Group H] [Finite H]
    (j : H →* planeLocal (F := F)) (hj : Function.Injective j)
    (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 2 ^ (3 * f))
    (hr : Group.rank (A.map (QuotientGroup.mk' (pCore 2 H))) < f) :
    A ≤ pCore 2 H := by
  let π := Plane.quotientMap.comp j
  let R := π.range
  let B := A.map π.rangeRestrict
  have hker : IsPGroup 2 π.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact (IsElementaryAbelian.isPGroup 2 (Plane.radical (F := F))).comap_of_injective j hj
  have hpre := π.rangeRestrict.comap_pCore_of_ker_isPGroup
    π.rangeRestrict_surjective hker
  by_cases hc : pCore 2 R = ⊥
  · have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
    let _ := hB
    have hrr : Group.rank B < f := by
      have he := rank_core_map_eq π.rangeRestrict hpre A
      rw [rank_core_eq_of_bot hc B] at he
      exact he ▸ hr
    have ha : Nat.card (A.map j) = Nat.card F ^ 3 := by
      rw [card_map_of_injective hj, hA, hF, ← pow_mul, Nat.mul_comm f 3]
    rcases hplane (A.map j) (IsElementaryAbelian.map _) ha with hle | hcard
    · have hk : A ≤ π.rangeRestrict.ker := by
        rw [MonoidHom.ker_rangeRestrict]
        intro a ha
        exact hle (mem_map_of_mem j ha)
      exact hk.trans (le_sSup ⟨inferInstance, hker⟩)
    · have hmap : B.map R.subtype = (A.map j).map Plane.quotientMap := by
        rw [map_map, MonoidHom.subtype_comp_rangeRestrict, map_map]
      have hBc : Nat.card F ≤ Nat.card B := by
        rw [← hmap, card_map_of_injective R.subtype_injective] at hcard
        exact hcard
      have hge := rank_ge_of_elementary_card (hF ▸ hBc)
      omega
  · have hBcore := hsl R hc B ((IsElementaryAbelian.isPGroup 2 A).map _)
    intro a ha
    rw [← hpre]
    exact hBcore (mem_map_of_mem π.rangeRestrict ha)

/-- Restricting to the determinant kernel preserves the intrinsic two-core rank.
Thus the plane-local calculation also treats the full plane parabolic. -/
theorem planeParabolic_le_core_of_local_facts
    (hplane : PlaneImageBound F) (hsl : RankOneCoreControl F)
    {f : ℕ} (hF : Nat.card F = 2 ^ f)
    {H : Type*} [Group H] [Finite H]
    (j : H →* planeParabolic (F := F)) (hj : Function.Injective j)
    (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 2 ^ (3 * f))
    (hr : Group.rank (A.map (QuotientGroup.mk' (pCore 2 H))) < f) :
    A ≤ pCore 2 H := by
  let χ := (determinantCharacter (plane F)).comp j
  let N := χ.ker
  have hAN : A ≤ N := by
    intro a ha
    have hs : a ^ 2 = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) ⟨a, ha⟩)
    have hu : χ a ^ 2 = 1 := by rw [← map_pow, hs, map_one]
    apply Units.ext
    apply CharTwo.sq_injective
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, one_pow] using
      congrArg Units.val hu
  let k : N →* planeLocal (F := F) := {
    toFun x := ⟨(j x.val).val, ⟨j x.val, x.property, rfl⟩⟩
    map_one' := by
      apply Subtype.ext
      change (j 1).val = (1 : planeParabolic (F := F)).val
      exact congrArg Subtype.val j.map_one
    map_mul' x y := by
      apply Subtype.ext
      change (j (x.val * y.val)).val = (j x.val * j y.val).val
      exact congrArg Subtype.val (j.map_mul x.val y.val) }
  have hk : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply hj
    apply Subtype.ext
    exact congrArg (fun z : planeLocal (F := F) => z.val) h
  let B := A.subgroupOf N
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAN
  have hcN : (pCore 2 H).comap N.subtype = pCore 2 N :=
    (inferInstance : N.Normal).isSubnormal.pCore_subgroupOf 2
  have hB : Nat.card B = 2 ^ (3 * f) :=
    (Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv).trans hA
  have hrB : Group.rank (B.map (QuotientGroup.mk' (pCore 2 N))) < f := by
    have he := rank_core_map_eq N.subtype hcN B
    rw [map_subgroupOf_eq_of_le hAN] at he
    omega
  have hBN := planeLocal_le_core_of_local_facts hplane hsl hF k hk B hB hrB
  intro a ha
  have hc := hBN (show (⟨a, hAN ha⟩ : N) ∈ B from ha)
  rw [← hcN] at hc
  exact hc

/-- A faithful symplectic subgroup with nontrivial intrinsic two-core embeds
in the full plane parabolic. The exceptional graph automorphism converts the
point case of the two-local cover into the plane case. -/
theorem exists_planeParabolic_embedding
    {H : Type*} [Group H] [Finite H]
    (j : H →* Sp F) (hj : Function.Injective j) (hc : pCore 2 H ≠ ⊥) :
    ∃ k : H →* planeParabolic (F := F), Function.Injective k := by
  let Q := (pCore 2 H).map j
  let M := normalizer (Q : Set (Sp F))
  have hQ : Q ≠ ⊥ := fun h => hc
    (((pCore 2 H).map_eq_bot_iff_of_injective hj).mp h)
  have hM : IsTwoLocal M := ⟨Q, hQ, pCore_isPGroup.map j, rfl⟩
  have hjM : j.range ≤ M := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map] using
      (pCore 2 H).le_normalizer_map j
  obtain ⟨g, hp | hp⟩ := twoLocal_parabolic_cover_of_charTwo M hM
  · let c := (MulAut.conj g).toMonoidHom.comp j
    let τ := DiagramAutomorphisms.ExceptionalGraph.graphAut (F := F)
    let d := τ.toMonoidHom.comp c
    have hd : ∀ x, d x ∈ planeParabolic (F := F) := by
      intro x
      rw [← DiagramAutomorphisms.ExceptionalGraph.graphAut_map_point]
      exact mem_map_of_mem τ.toMonoidHom (hp (mem_map_of_mem
        (MulAut.conj g).toMonoidHom (hjM ⟨x, rfl⟩)))
    refine ⟨d.codRestrict planeParabolic hd, ?_⟩
    intro x y h
    exact hj ((MulAut.conj g).injective (τ.injective (congrArg Subtype.val h)))
  · let c := (MulAut.conj g).toMonoidHom.comp j
    have hc : ∀ x, c x ∈ planeParabolic (F := F) := fun x =>
      hp (mem_map_of_mem (MulAut.conj g).toMonoidHom (hjM ⟨x, rfl⟩))
    refine ⟨c.codRestrict planeParabolic hc, ?_⟩
    intro x y h
    exact hj ((MulAut.conj g).injective (congrArg Subtype.val h))

omit [CharP F 2] in
/-- Conditional assembly of the exact intrinsic symplectic rank gap.
The two independent local calculations remain explicit. -/
theorem le_core_of_rank_lt_of_local_facts
    (hplane : PlaneImageBound F) (hsl : RankOneCoreControl F)
    {f : ℕ} (hF : Nat.card F = 2 ^ f)
    {H : Type*} [Group H] [Finite H]
    (j : H →* Sp F) (hj : Function.Injective j)
    (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 2 ^ (3 * f))
    (hr : Group.rank (A.map (QuotientGroup.mk' (pCore 2 H))) < f) :
    A ≤ pCore 2 H := by
  let _ : CharP F 2 := EvenProjective.charTwo_of_card hF
  by_cases hc : pCore 2 H = ⊥
  · have hrA := rank_core_eq_of_bot hc A
    have hge := rank_ge_of_elementary_card hA.ge
    omega
  · obtain ⟨k, hk⟩ := exists_planeParabolic_embedding j hj hc
    exact planeParabolic_le_core_of_local_facts hplane hsl hF k hk A hA hr

omit [CharP F 2] in
/-- A maximum elementary subgroup of a faithfully represented finite subgroup
of Sp₄(2^f) lies in its intrinsic two-core if its image modulo that core has
rank less than f. Both local matrix calculations are discharged, and the
field cardinality supplies characteristic two. -/
theorem le_core_of_rank_lt
    {f : ℕ} (hF : Nat.card F = 2 ^ f)
    {H : Type*} [Group H] [Finite H]
    (j : H →* Sp F) (hj : Function.Injective j)
    (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 2 ^ (3 * f))
    (hr : Group.rank (A.map (QuotientGroup.mk' (pCore 2 H))) < f) :
    A ≤ pCore 2 H := by
  let _ : CharP F 2 := EvenProjective.charTwo_of_card hF
  exact le_core_of_rank_lt_of_local_facts planeImageBound (rankOneCoreControl F)
    hF j hj A hA hr

end Theory.SpecificGroups.SymplecticFour.ElementaryCoreRankGap
