module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Kernel.Basic

/-!
# The unstarred midpoint index as an actual commutator order

The edge subgroup Z_beta has index two in Z_c and centralizes V_alpha.
Thus one outside element of Z_c produces all displacements of U_delta2.
Its commutator homomorphism has kernel X₁, proving the exact index/order
identity. The private group argument is adapted from the checked
index_two_displacement proof in Flags/RankOne/Consequences/Displacement/
Cardinalities/Reduction.lean, now applied to the smaller unstarred preimage.

Consequently the source's commutator-order upper bound of two, together
with clause (4)'s starred escape, implies |U_delta2/X₁| = 2. The order
upper bound remains an explicit premise here and is not asserted proved.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.12)(5), printed p.912.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension

/-- The two actor cosets have the same displacement image, and the kernel
of commutation by an outside element is the full actor centralizer. -/
private theorem index_two_displacement {G : Type*} [Group G]
    (V A C : Subgroup G)
    (hcentral : C ≤ centralizer (V : Set G))
    (hindex : C.relIndex A = 2)
    (hcommV : ⁅V, A⁆ ≤ V)
    (hcomm : ⁅V, A⁆ ≤ centralizer (V : Set G))
    (x : G) (hx : x ∈ A) (hxC : x ∉ C) :
    ⁅zpowers x, V⁆ = ⁅A, V⁆ ∧
    (centralizer (A : Set G)).relIndex V = Nat.card (⁅A, V⁆ : Subgroup G) := by
  have hvalue (v : G) (hv : v ∈ V) : ⁅v, x⁆ ∈ ⁅V, A⁆ :=
    commutator_mem_commutator hv hx
  let f : V →* G := {
    toFun := fun v => ⁅(v : G), x⁆
    map_one' := by simp
    map_mul' := by
      intro v w
      change ⁅(v : G) * (w : G), x⁆ = ⁅(v : G), x⁆ * ⁅(w : G), x⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hvw : (v : G) * ⁅(w : G), x⁆ = ⁅(w : G), x⁆ * v :=
        hcomm (hvalue w w.property) v v.property
      have hcc : ⁅(w : G), x⁆ * ⁅(v : G), x⁆ =
          ⁅(v : G), x⁆ * ⁅(w : G), x⁆ :=
        hcomm (hvalue v v.property) _ (hcommV (hvalue w w.property))
      rw [hvw, mul_inv_cancel_right, hcc] }
  have hsame (v : G) (hv : v ∈ V) (a : G) (ha : a ∈ A) (haC : a ∉ C) :
      ⁅v, a⁆ = ⁅v, x⁆ := by
    have hfactor : x⁻¹ * a ∈ C :=
      (C.subgroupOf A).mul_mem_iff_of_index_two hindex
        (a := ⟨x⁻¹, A.inv_mem hx⟩) (b := ⟨a, ha⟩) |>.mpr (by
          simp only [mem_subgroupOf, inv_mem_iff, hxC, haC])
    have hzero : ⁅v, x⁻¹ * a⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hcentral hfactor v hv)
    have hh := commutatorElement_mul_right_eq_mul_conj v x (x⁻¹ * a)
    simpa only [mul_inv_cancel_left, hzero, mul_one, mul_inv_cancel_right,
      mul_inv_cancel, mul_one] using hh
  have hrange : f.range = ⁅V, A⁆ := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact hvalue v v.property
    · apply commutator_le.mpr
      intro v hv a ha
      by_cases haC : a ∈ C
      · have hone : ⁅v, a⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.mpr (hcentral haC v hv)
        rw [hone]
        exact f.range.one_mem
      exact ⟨⟨v, hv⟩, (hsame v hv a ha haC).symm⟩
  constructor
  · rw [commutator_comm (zpowers x), commutator_comm A]
    apply le_antisymm (commutator_mono le_rfl (zpowers_le.mpr hx))
    rw [← hrange]
    rintro _ ⟨v, rfl⟩
    exact commutator_mem_commutator v.property (mem_zpowers x)
  · have hker : f.ker = (centralizer (A : Set G)).subgroupOf V := by
      ext v
      change ⁅(v : G), x⁆ = 1 ↔ (v : G) ∈ centralizer (A : Set G)
      constructor
      · intro hv a ha
        apply Eq.symm
        apply commutatorElement_eq_one_iff_mul_comm.mp
        by_cases haC : a ∈ C
        · exact commutatorElement_eq_one_iff_mul_comm.mpr
            (hcentral haC v v.property)
        · exact (hsame v v.property a ha haC).trans hv
      · intro hv
        exact commutatorElement_eq_one_iff_mul_comm.mpr (hv x hx).symm
    change ((centralizer (A : Set G)).subgroupOf V).index = _
    rw [← hker, index_ker, hrange, commutator_comm V]


variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The kernel index is exactly the order of the actual unstarred commutator. -/
theorem midpointKernel_relIndex_eq_commutator_card
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source) :
    (midpointKernel d f s.middle).relIndex (secondPreimage d f) =
      Nat.card (⁅secondPreimage d f, Z R s.middle⁆ : Subgroup (FreeAmalgam R)) := by
  have hVQ := Flags.V_le_Q geometry common.large_distance (alpha R) rfl
  have hZcentral : Z R (alpha R) ≤
      centralizer (V R (alpha R) : Set (FreeAmalgam R)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes _ rfl)).trans
      (centralizer_le hVQ)
  have hcentral : Z R (beta R) ≤
      centralizer (secondPreimage d f : Set (FreeAmalgam R)) :=
    ((Flags.edge_Z_le (alpha R) (beta R) rfl (base_adjacent R)).trans hZcentral).trans
      (centralizer_le (secondPreimage_le_radius d f))
  have hcomm : ⁅secondPreimage d f, Z R s.middle⁆ ≤ Z R (alpha R) :=
    ((commutator_mono (secondPreimage_le_radius d f) (Seed.midpoint_Z_le_radius s)).trans_eq
      (radius.radius_derived (alpha R) rfl)).trans (DistanceEight.U_le_Z R _)
  have hi := radius.edge_Z_index s.middle (beta R) s.middle_color (adjacent_symm R hbc)
  have hnot : ¬ Z R s.middle ≤ Z R (beta R) := by
    intro h
    have hh := relIndex_eq_one.mpr h
    rw [hi] at hh
    omega
  obtain ⟨x, hx, hxout⟩ := SetLike.not_le_iff_exists.mp hnot
  have he := (index_two_displacement (secondPreimage d f) (Z R s.middle) (Z R (beta R))
    hcentral hi (hcomm.trans (Z_le_secondPreimage d f))
    (hcomm.trans (hZcentral.trans (centralizer_le (secondPreimage_le_radius d f))))
    x hx hxout).2
  rw [midpointKernel_eq_centralizer common s d f, inf_relIndex_left,
    commutator_comm (secondPreimage d f)]
  exact he

/-- Clause (4)'s escape makes the commutator-order bound sharp. This is an
application to the literal unstarred kernel, not an assumed index. -/
theorem midpointKernel_relIndex_eq_two_of_commutator_card_le_two
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle)
    (hcard : Nat.card (⁅secondPreimage d f, Z R s.middle⁆ : Subgroup (FreeAmalgam R)) ≤ 2) :
    (midpointKernel d f s.middle).relIndex (secondPreimage d f) = 2 := by
  have hbound := (midpointKernel_relIndex_eq_commutator_card common radius s hbc d f).le.trans hcard
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite (secondPreimage d f) := Finite.of_injective
    (inclusion ((secondPreimage_le_radius d f).trans
      (geometry.V_local (alpha R) rfl common.large_distance))) (inclusion_injective _)
  have hpos : (midpointKernel d f s.middle).relIndex (secondPreimage d f) ≠ 0 :=
    index_ne_zero_of_finite
  have hne : (midpointKernel d f s.middle).relIndex (secondPreimage d f) ≠ 1 := by
    intro h
    apply hescape
    exact (secondStar_preimage_le_secondPreimage d f).trans
      ((relIndex_eq_one.mp h).trans inf_le_right)
  omega

omit [Finite M] in
/-- Index two in the unstarred layer leaves at least three dimensions inside
its four-dimensional starred sublayer. The quotient map and X₁ remain literal. -/
theorem starredMidpointKernel_finrank_ge_three
    (common : CommonFacts R source geometry) (s : CriticalSegment geometry)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (n : NaturalCopies (geometry := geometry) d f)
    (hindex : (midpointKernel d f s.middle).relIndex (secondPreimage d f) = 2) :
    3 ≤ Module.finrank (ZMod 2) (starredMidpointKernel (geometry := geometry) d f s.middle) := by
  let W := Seed.secondTildeStar (geometry := geometry) d f 1
  let T := d.preimage W
  let K := midpointKernel d f s.middle
  have hT : T ≤ V R (alpha R) := d.preimage_le W
  have he : K.relIndex T = 2 ^ Module.finrank (ZMod 2)
      ((d.subspace T) ⧸ (d.subspace K).comap (d.subspace T).subtype) := by
    change (K.subgroupOf T).index = _
    rw [← d.sectionMap_kernel T K hT (Z_le_midpointKernel common s d f), index_ker,
      MonoidHom.range_eq_top.mpr (d.sectionMap_surjective T K hT),
      Nat.card_congr (topEquiv).toEquiv]
    change Nat.card ((d.subspace T) ⧸ (d.subspace K).comap (d.subspace T).subtype) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hbound : K.relIndex T ≤ 2 := by
    exact (relIndex_le_of_le_right (secondStar_preimage_le_secondPreimage d f)
      (by rw [hindex]; decide)).trans_eq hindex
  have hW : d.subspace T = W := d.subspace_preimage W
  rw [he, hW] at hbound
  have hsmall : Module.finrank (ZMod 2)
      (W ⧸ (d.subspace K).comap W.subtype) ≤ 1 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (show 0 < (2 : ℕ) by decide)
      (show 2 ≤ Module.finrank (ZMod 2) (W ⧸ (d.subspace K).comap W.subtype) by omega)
    omega
  have hadd := ((d.subspace K).comap W.subtype).finrank_quotient_add_finrank
  have hfour : Module.finrank (ZMod 2) W = 4 := n.finrank_eq_four
  change 3 ≤ Module.finrank (ZMod 2) ((d.subspace K).comap W.subtype)
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
