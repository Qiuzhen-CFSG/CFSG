module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.LargeImage.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Edges

/-!
# The actual large image fills the edge displacement

The edge displacement has order four inside the natural group of order
eight, by the earlier (4.3.1) transport. If it centralizes V_c, evaluation
of commutators on a vector outside this subgroup identifies the image
order [V_c : V_c ∩ Q_alpha] with the natural commutator order. An image
order greater than two therefore fills the entire displacement.

The private index-two calculation is elementary group algebra, adapted
from the private index_two_displacement proof in
DistanceFour/Flags/RankOne/Consequences/Displacement/Cardinalities/Reduction.lean.
No result or hypothesis from that later source branch is imported or used.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2), printed p.884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : MS93.Geometry R}

variable [Finite M]

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


/-- A subgroup of index two in the natural eight centralizes the predecessor.
The evaluation homomorphism therefore identifies the actual kernel image
order with the order of the natural commutator. -/
theorem large_image_edge_eq_of_centralizes (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry) (path : FrontPath p)
    (hi : 2 < (Q R p.a).relIndex (V R p.c))
    (hcentral : edgeDisplacement p.a path.first ≤
      centralizer (V R p.c : Set (FreeAmalgam R))) :
    edgeDisplacement p.a path.first = ⁅Z R p.a, V R p.c⁆ := by
  let E := edgeDisplacement p.a path.first
  let A := U R p.a
  have hEA : E ≤ A := Initial.edge_le_natural source _ _ p.color_a path.start_first_adjacent
  have hEcard : Nat.card E = 4 := StepThree.edge_card p
    (by obtain ⟨ip⟩ := initial p; have := ip.six_le; omega) initial
    p.a path.first p.color_a path.start_first_adjacent
  have hAcard : Nat.card A = 8 := modules.natural.card_at p.a p.color_a
  let : Finite A := Nat.finite_of_card_ne_zero (by omega)
  let : Finite E := Finite.of_injective (inclusion hEA) (inclusion_injective _)
  have hindex : E.relIndex A = 2 := by
    have hm := (E.subgroupOf A).index_mul_card
    change E.relIndex A * Nat.card (E.subgroupOf A) = Nat.card A at hm
    rw [Nat.card_congr (subgroupOfEquivOfLe hEA).toEquiv, hEcard, hAcard] at hm
    omega
  have hnot : ¬ A ≤ E := by
    intro hh
    have heq := le_antisymm hEA hh
    have := congrArg (fun K : Subgroup (FreeAmalgam R) => Nat.card K) heq
    omega
  obtain ⟨x, hxA, hxE⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨ip⟩ := initial p
  have hactor := predecessor_V_le_path_kernel p path.first_before (by decide)
    (by have := ip.six_le; omega)
  have hcommE : ⁅V R p.c, A⁆ ≤ E := by
    rw [commutator_comm]
    exact commutator_mono (U_le_Z p.a) hactor
  have hcommV : ⁅V R p.c, A⁆ ≤ V R p.c :=
    le_normalizer_iff_commutator_le_left.mp
      ((((U_le_Z p.a).trans (Z_le_VBall R p.a 2)).trans p.trapped).trans
        ((show Q R p.c ≤ stabilizer R p.c from fun _ hx => hx.1).trans
          (V_normalized p.c)))
  have hdisplacement := (index_two_displacement (V R p.c) A E hcentral hindex
    hcommV (hcommE.trans hcentral) x hxA hxE).2
  have hindexeq : (Q R p.a).relIndex (V R p.c) =
      (centralizer (A : Set (FreeAmalgam R))).relIndex (V R p.c) := by
    rw [← modules.natural.centralizer p.a p.color_a, ← inf_relIndex_right]
    have heq : (stabilizer R p.a ⊓ centralizer (A : Set (FreeAmalgam R))) ⊓ V R p.c =
        centralizer (A : Set (FreeAmalgam R)) ⊓ V R p.c := by
      ext z
      exact ⟨fun hz => ⟨hz.1.2, hz.2⟩,
        fun hz => ⟨⟨predecessor_V_le_start_stabilizer p hz.2, hz.1⟩, hz.2⟩⟩
    change ((stabilizer R p.a ⊓ centralizer (A : Set (FreeAmalgam R))) ⊓ V R p.c).relIndex
      (V R p.c) = _
    rw [heq, inf_relIndex_right]
  have hcard : 2 < Nat.card (⁅A, V R p.c⁆ : Subgroup (FreeAmalgam R)) := by
    rwa [hindexeq, hdisplacement] at hi
  have hle : ⁅A, V R p.c⁆ ≤ E := by rw [commutator_comm]; exact hcommE
  have hdiv := card_dvd_of_le hle
  rw [hEcard] at hdiv
  have hd := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 4 ≠ 0)⟩
  rw [show Nat.divisors 4 = ({1, 2, 4} : Finset ℕ) by decide] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  have hfull : ⁅A, V R p.c⁆ = E := eq_of_le_of_card_ge hle (by omega)
  have hZe : ⁅Z R p.a, V R p.c⁆ ≤ E := commutator_mono le_rfl hactor
  exact le_antisymm
    (hfull.symm.le.trans (commutator_mono (U_le_Z p.a) le_rfl)) hZe


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases
