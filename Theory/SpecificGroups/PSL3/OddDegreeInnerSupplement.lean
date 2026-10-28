module
public import Theory.GroupTheory.RankOneInnerSylow
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.SpecificGroups.PSL3.BinaryCubicRankParity
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelStructure
public import Theory.SpecificGroups.Classical.EvenDerivedThree
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
/-!
# Odd binary PSL₃ cannot support an inner elementary-plane supplement

The original inner supplement has a component intersection of order
divisible by three. Its join with the actual Sylow intersection is solvable,
since the full Sylow normalizes the supplement. Transporting that join
through the supplied model equivalence places it in the Borel of the
supplied Sylow. In odd binary degree that Borel has order prime to three.

This proves the obstruction with the intrinsic two-core quotient, full
Sylow, original elementary nine and relative component normality. It
assumes inner action; Chapter12's AbelianNormalLinearThreeParity discharges
that premise using the original residual commutator and the proved abelian
outer group. No model order or simplicity assumption is added.

Source: Aschbacher--Smith 12.6.31, printed p.836, refs/quasithin.pdf.
-/
public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace Matrix.PSL3.BinaryCubicRankParity
variable {J : Type*} [Group J] [Finite J]
  {F : Type*} [Field F] [Finite F]

/-- The original kind of inner E₉ supplement cannot occur over an
odd-degree binary PSL₃ component. -/
theorem no_inner_elementary_plane_supplement
    (S : Sylow 2 J) (A B P : Subgroup J) [B.Normal]
    [IsElementaryAbelian 3 (A ⧸ pCore 2 A)] [IsElementaryAbelian 3 P]
    [(A ⊓ centralizer (B : Set J) : Subgroup J).Normal]
    (e : B ≃* PSL(3,F)) {n : ℕ} (hn : 2 ≤ n) (ho : Odd n)
    (hF : Nat.card F = 2^n) (hzero : pCore 2 J = ⊥) (hJ : primeRank 3 J ≤ 2)
    (hinner : A ≤ B ⊔ centralizer (B : Set J))
    (hnA : (S : Subgroup J) ≤ normalizer (A : Set J))
    (hgen : B ⊔ A ⊔ (S : Subgroup J) = ⊤)
    (hPA : P ≤ A) (hP : Nat.card P = 9) : False := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let := Atlas.sl_perfect (F := F) 3 (by decide)
  have hz : center B = ⊥ := by
    apply bot_unique
    intro x hx
    have he : e x = 1 := mem_bot.mp
      ((Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)).le
        ((centerCongr e) ⟨x,hx⟩).property)
    exact mem_bot.mpr (e.map_eq_one_iff.mp he)
  have hr : primeRank 3 B = 1 := by
    rw [primeRank_equiv 3 e]
    have hu := rank_le_one_of_odd hF ho
    have hd : 3 ∣ Nat.card PSL(3,F) :=
      (Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
        (F := F) (i := (0 : Fin 3)) (j := 1) (by decide)).trans
          (card_subgroup_dvd_card (commutator PSL(3,F)))
    have hh : primeRank 3 PSL(3,F) ≠ 0 := fun h => PrimeRank.eq_zero_iff_not_dvd_card.mp h hd
    omega
  have h3 := three_dvd_inner_supplement_intersection A B S P hzero hz hr hJ hinner hnA hgen hPA hP
  obtain ⟨Q,hQ⟩ := S.exists_subgroupOf_eq_of_normal B
  let C := A.subgroupOf B
  have hQC : (Q : Subgroup B) ≤ normalizer (C : Set B) := by
    intro x hx
    have hxS : (x : J) ∈ (S : Subgroup J) := hQ.le hx
    exact mem_normalizer_iff.mpr (fun c => mem_normalizer_iff.mp (hnA hxS) c.val)
  let : Group.IsNilpotent (pCore 2 A) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable A := Group.isSolvable_of_ker_le_range
    (pCore 2 A).subtype (QuotientGroup.mk' (pCore 2 A))
    (by rw [range_subtype,QuotientGroup.ker_mk'])
  let f : C →* A := (B.subtype.comp C.subtype).codRestrict A (fun x => x.property)
  let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective
    (f := f) (by
      intro x y h
      have hh : (x.val.val : J) = y.val.val := congrArg (fun a : A => a.val) h
      exact Subtype.ext (Subtype.ext hh))
  let : Group.IsNilpotent (Q : Subgroup B) := Q.isPGroup'.isNilpotent
  let N := C ⊔ (Q : Subgroup B)
  let : Group.IsSolvable N := Group.isSolvable_sup_of_normalizes C Q hQC
  let N' := N.map e.toMonoidHom
  have hsol : Group.IsSolvable N' := Group.isSolvable_of_surjective
    (e.toMonoidHom.subgroupMap_surjective N)
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hle := LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le
    F hn hF Q' N' hsol (map_mono le_sup_right)
  have hCN : 3 ∣ Nat.card N' := by
    rw [card_map_of_injective e.injective]
    have he : C.map B.subtype = A ⊓ B := subgroupOf_map_subtype A B
    rw [←he,card_map_of_injective B.subtype_injective] at h3
    exact h3.trans (card_dvd_of_le (le_sup_left : C ≤ N))
  exact LinearThree.BorelStructure.three_not_dvd_card_sylowNormalizer_of_odd F ho hF Q'
    (hCN.trans (card_dvd_of_le hle))
end Matrix.PSL3.BinaryCubicRankParity
