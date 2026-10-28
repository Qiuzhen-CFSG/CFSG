module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.Linear.Plane

/-!
# A fixed generating seed in two binary dual copies

Let an order-four subgroup of SL₃(2) fix a natural plane pointwise. A
subgroup of two dual copies fixed by that actor lies in the pair of
annihilator lines. If its SL₃(2)-orbit generates both copies, it fills those
lines: a proper subgroup would lie in one of the two coordinate axes or
the diagonal, each preserved by the componentwise action. Every actor
displacement therefore belongs to the original seed.

The final export uses literal componentwise inverse-transpose images and
subgroup generation, so it applies to the marked image of hat V_a in
hat W_c / hat V_c without introducing another action instance. The parent
NeighborAction theorem supplies the actual seed, actor and quotient map.

Source: Meierfrankenfeld--Stellmacher (1993), the doubled-dual model in
(4.5.4)(iii) and its use in (4.5.5), printed pp.898--899.
-/

@[expose] public section

open Matrix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Linear
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.Linear

abbrev Pair := Multiplicative (W × W)

/-- The literal componentwise contragredient action. -/
def dualPair (g : S) (v : Pair) : Pair :=
  Multiplicative.ofAdd (dual g v.toAdd.1, dual g v.toAdd.2)

/-- The pair of annihilator lines, as a subgroup in the consumer's convention. -/
def annihilatorPair (P : Submodule (ZMod 2) W) : Subgroup Pair where
  carrier := {v | v.toAdd.1 ∈ annihilator P ∧ v.toAdd.2 ∈ annihilator P}
  one_mem' := ⟨(annihilator P).zero_mem, (annihilator P).zero_mem⟩
  mul_mem' := by
    intro v w hv hw
    exact ⟨(annihilator P).add_mem hv.1 hw.1, (annihilator P).add_mem hv.2 hw.2⟩
  inv_mem' := by
    intro v hv
    exact ⟨(annihilator P).neg_mem hv.1, (annihilator P).neg_mem hv.2⟩

private def relation (a b : ZMod 2) : Subgroup Pair where
  carrier := {v | a • v.toAdd.1 + b • v.toAdd.2 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro v w hv hw
    change a • (v.toAdd.1 + w.toAdd.1) + b • (v.toAdd.2 + w.toAdd.2) = 0
    rw [smul_add, smul_add]
    calc
      _ = (a • v.toAdd.1 + b • v.toAdd.2) + (a • w.toAdd.1 + b • w.toAdd.2) := by abel
      _ = 0 := by rw [hv, hw, add_zero]
  inv_mem' := by
    intro v hv
    change a • (-v.toAdd.1) + b • (-v.toAdd.2) = 0
    rw [smul_neg, smul_neg, ← neg_add, hv, neg_zero]

private theorem relation_invariant (a b : ZMod 2) (g : S) (v : Pair)
    (hv : v ∈ relation a b) : dualPair g v ∈ relation a b := by
  change a • dual g v.toAdd.1 + b • dual g v.toAdd.2 = 0
  change a • v.toAdd.1 + b • v.toAdd.2 = 0 at hv
  simp only [dual]
  rw [← mulVec_smul, ← mulVec_smul, ← mulVec_add, hv, mulVec_zero]

/-- A seed fixed by the actor and generating under S fills both fixed lines. -/
theorem generating_seed_eq_annihilatorPair
    (K : Subgroup S) (P : Submodule (ZMod 2) W)
    (hK : Nat.card K = 4) (hP : Nat.card P = 4)
    (hfix : K ≤ planeFixer P) (E : Subgroup Pair)
    (hE : ∀ k ∈ K, ∀ v ∈ E, dualPair k v = v)
    (hgen : ∀ D : Subgroup Pair, E ≤ D →
      (∀ g : S, ∀ v ∈ D, dualPair g v ∈ D) → D = ⊤) :
    E = annihilatorPair P := by
  have hle : E ≤ annihilatorPair P := by
    intro v hv
    exact ⟨(dual_fixed_iff K P hK hP hfix v.toAdd.1).mp (fun k hk =>
      congrArg (fun x : Pair => x.toAdd.1) (hE k hk v hv)),
      (dual_fixed_iff K P hK hP hfix v.toAdd.2).mp (fun k hk =>
      congrArg (fun x : Pair => x.toAdd.2) (hE k hk v hv))⟩
  obtain ⟨n, hn, hline⟩ := annihilator_line P hP
  have hfirst : ∃ v ∈ E, v.toAdd.1 ≠ 0 := by
    by_contra hh
    push Not at hh
    have hd := hgen (relation 1 0) (fun v hv => by
      change (1 : ZMod 2) • v.toAdd.1 + (0 : ZMod 2) • v.toAdd.2 = 0
      simp only [one_smul, zero_smul, add_zero, hh v hv]) (relation_invariant 1 0)
    have he : Multiplicative.ofAdd (n, (0 : W)) ∈ relation 1 0 := by rw [hd]; trivial
    exact hn (by simpa [relation] using he)
  have hsecond : ∃ v ∈ E, v.toAdd.2 ≠ 0 := by
    by_contra hh
    push Not at hh
    have hd := hgen (relation 0 1) (fun v hv => by
      change (0 : ZMod 2) • v.toAdd.1 + (1 : ZMod 2) • v.toAdd.2 = 0
      simp only [one_smul, zero_smul, zero_add, hh v hv]) (relation_invariant 0 1)
    have he : Multiplicative.ofAdd ((0 : W), n) ∈ relation 0 1 := by rw [hd]; trivial
    exact hn (by simpa [relation] using he)
  have hdiagonal : ∃ v ∈ E, v.toAdd.1 ≠ v.toAdd.2 := by
    by_contra hh
    push Not at hh
    have hd := hgen (relation 1 (-1)) (fun v hv => by
      change (1 : ZMod 2) • v.toAdd.1 + (-1 : ZMod 2) • v.toAdd.2 = 0
      simp only [one_smul, neg_smul, hh v hv, add_neg_cancel]) (relation_invariant 1 (-1))
    have he : Multiplicative.ofAdd (n, (0 : W)) ∈ relation 1 (-1) := by rw [hd]; trivial
    exact hn (by simpa [relation] using he)
  let e : Pair := Multiplicative.ofAdd (n, (0 : W))
  let f : Pair := Multiplicative.ofAdd ((0 : W), n)
  have cases_pair {v : Pair} (hv : v ∈ E) : v = 1 ∨ v = e ∨ v = f ∨ v = e * f := by
    have hx := (hline _).mp (hle hv).1
    have hy := (hline _).mp (hle hv).2
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (by apply Multiplicative.toAdd.injective; exact Prod.ext hx hy)
    · exact Or.inr (Or.inr (Or.inl (by apply Multiplicative.toAdd.injective; exact Prod.ext hx hy)))
    · exact Or.inr (Or.inl (by apply Multiplicative.toAdd.injective; exact Prod.ext hx hy))
    · exact Or.inr (Or.inr (Or.inr (by
        apply Multiplicative.toAdd.injective
        change v.toAdd = (n + 0, 0 + n)
        simpa only [add_zero, zero_add] using Prod.ext hx hy)))
  have hneither : e ∈ E ∨ f ∈ E := by
    obtain ⟨v, hv, hneq⟩ := hdiagonal
    rcases cases_pair hv with rfl | rfl | rfl | rfl
    · exact (hneq rfl).elim
    · exact Or.inl hv
    · exact Or.inr hv
    · exact (hneq (by change n + 0 = 0 + n; simp)).elim
  have hef : e ∈ E ∧ f ∈ E := by
    rcases hneither with he | hf
    · refine ⟨he, ?_⟩
      obtain ⟨v, hv, hnonzero⟩ := hsecond
      rcases cases_pair hv with rfl | rfl | rfl | rfl
      · exact (hnonzero rfl).elim
      · exact (hnonzero rfl).elim
      · exact hv
      · simpa only [inv_mul_cancel_left] using E.mul_mem (E.inv_mem he) hv
    · refine ⟨?_, hf⟩
      obtain ⟨v, hv, hnonzero⟩ := hfirst
      rcases cases_pair hv with rfl | rfl | rfl | rfl
      · exact (hnonzero rfl).elim
      · exact hv
      · exact (hnonzero rfl).elim
      · simpa only [mul_inv_cancel_right] using E.mul_mem hv (E.inv_mem hf)
  apply le_antisymm hle
  intro v hv
  have hx := (hline _).mp hv.1
  have hy := (hline _).mp hv.2
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have he : v = 1 := by apply Multiplicative.toAdd.injective; exact Prod.ext hx hy
    rw [he]; exact E.one_mem
  · have he : v = f := by apply Multiplicative.toAdd.injective; exact Prod.ext hx hy
    rw [he]; exact hef.2
  · have he : v = e := by apply Multiplicative.toAdd.injective; exact Prod.ext hx hy
    rw [he]; exact hef.1
  · have he : v = e * f := by
      apply Multiplicative.toAdd.injective
      change v.toAdd = (n + 0, 0 + n)
      simpa only [add_zero, zero_add] using Prod.ext hx hy
    rw [he]; exact E.mul_mem hef.1 hef.2

/-- The subgroup-level displacement theorem used by the neighboring quotient. -/
theorem displacement_mem_of_fixed_generating_seed
    (K : Subgroup S) (P : Submodule (ZMod 2) W)
    (hK : Nat.card K = 4) (hP : Nat.card P = 4)
    (hfix : ∀ k ∈ K, ∀ p ∈ P, k.val.mulVec p = p)
    (E : Subgroup Pair)
    (hE : ∀ k ∈ K, ∀ v ∈ E, Multiplicative.ofAdd (dual k v.toAdd.1, dual k v.toAdd.2) = v)
    (hgen : ∀ D : Subgroup Pair, E ≤ D →
      (∀ g : S, ∀ v ∈ D, Multiplicative.ofAdd (dual g v.toAdd.1, dual g v.toAdd.2) ∈ D) → D = ⊤)
    {k : S} (hk : k ∈ K) (v : Pair) :
    v * (Multiplicative.ofAdd (dual k v.toAdd.1, dual k v.toAdd.2))⁻¹ ∈ E := by
  rw [generating_seed_eq_annihilatorPair K P hK hP hfix E hE hgen]
  change v.toAdd.1 + -(dual k v.toAdd.1) ∈ annihilator P ∧
    v.toAdd.2 + -(dual k v.toAdd.2) ∈ annihilator P
  simpa only [sub_eq_add_neg] using
    And.intro (dual_displacement_mem K P hfix hk v.toAdd.1)
      (dual_displacement_mem K P hfix hk v.toAdd.2)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.Linear
