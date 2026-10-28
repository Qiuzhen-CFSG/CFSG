module
public import Theory.GroupTheory.ThreeSectionReducibility.Fixed
public import Theory.GroupTheory.ThreeSectionReducibility.Kernel
public import Theory.GroupTheory.ThreeSectionReducibility.Reduction
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.PGroup.SupercriticalFourInversion

/-!
# The cubic reducibility assertion of A.1.31

Reduce the covering map to a three-group kernel while retaining the rank
bound on its source. A faithful four-group on a supercritical Frattini
plane contains an inverter. The inverter is central modulo the three-core;
its fixed subgroup in the target is a normal cubic line, by A.1.31(1) and
the Klein-four fixed-cardinality formula. This gives the exact p=3 input
used by the degree-six branch of G.9.4, without quotient-rank monotonicity.

Source: Aschbacher--Smith, Lemma A.1.31(3), printed pp.27--28.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA
open Theory.GroupTheory Theory.GroupTheory.ThreeSection
universe u v
variable {D : Type u} {E : Type v} [Group D] [Finite D] [Group E] [Finite E]

set_option maxHeartbeats 800000 in
 private theorem reducible_three_kernel
    (f : D →* E) (hf : Function.Surjective f) (hk : IsPGroup 3 f.ker)
    (hrank : primeRank 3 D ≤ 2) (hF : generalizedFitting E = pCore 3 E)
    [IsElementaryAbelian 3 (pCore 3 E)] (hV : Nat.card (pCore 3 E) = 27)
    (hr2 : 1 < primeRank 2 E) :
    ∃ R : Subgroup E, R.Normal ∧ R ≠ ⊥ ∧ R < pCore 3 E := by
  obtain ⟨T, hT, hTc⟩ := exists_elementary_four hr2
  let : IsElementaryAbelian 2 T := hT
  have hodd : Odd (Nat.card f.ker) := by
    obtain ⟨n, hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (by decide : Odd 3).pow
  obtain ⟨A, hA, hAT, hAc⟩ :=
    exists_elementaryAbelian_map_eq_of_surjective_coprime f hf hodd.coprime_two_left T
  let : IsElementaryAbelian 2 A := hA
  have hc := source_core_selfCentralizing f hf hk hF
  let c : D →* MulAut (pCore 3 D) := MulAut.conjNormal
  have hck : c.ker ≤ pCore 3 D := by
    intro x hx
    apply hc
    intro y hy
    have he := congrArg (fun b : MulAut (pCore 3 D) => (b ⟨y, hy⟩ : D)) hx
    change x * y * x⁻¹ = y at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hcko : Odd (Nat.card c.ker) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup.to_le hck).exists_card_eq
    rw [hn]
    exact (by decide : Odd 3).pow
  let action : A →* MulAut (pCore 3 D) := c.comp A.subtype
  have hfaith : Function.Injective action :=
    injective_comp_subtype_of_coprime_ker c hcko.coprime_two_left A
      (IsElementaryAbelian.isPGroup 2 A)
  obtain ⟨X, hX⟩ := (pCore_isPGroup (p := 3) (G := D)).exists_supercriticalPSubgroup
    (by decide : 3 ≠ 2)
  let : X.Characteristic := hX.characteristic
  obtain ⟨a, ha, hai⟩ := hX.exists_frattini_inverter pCore_isPGroup
    ((primeRank_subgroup_le 3 (pCore 3 D)).trans hrank) action hfaith (hAc.trans hTc)
  let α := ((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp c
  have hαk : α.ker ≤ pCore 3 D := supercritical_action_kernel_le_core hc X hX
  have hαa : α (a : D) ∈ center (MulAut (X ⧸ frattini X)) :=
    mem_center_mulAut_of_inverts _ hai
  let t : T := ⟨f a, hAT ▸ mem_map_of_mem f a.property⟩
  have ht : t ≠ 1 := by
    intro he
    apply ha
    apply injective_comp_subtype_of_coprime_ker f hodd.coprime_two_left A
      (IsElementaryAbelian.isPGroup 2 A)
    have hev : f (a : D) = 1 := congrArg Subtype.val he
    simpa only [MonoidHom.comp_apply, coe_subtype, OneMemClass.coe_one, map_one] using hev
  apply reducible_of_four_central_mod_core f hf hrank hF hV T hTc t ht
  intro g
  obtain ⟨d, rfl⟩ := hf g
  have hcomm : d * (a : D) * d⁻¹ * (a : D)⁻¹ ∈ pCore 3 D := by
    apply hαk
    change α (d * (a : D) * d⁻¹ * (a : D)⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [mem_center_iff.mp hαa (α d), mul_inv_cancel_right, mul_inv_cancel]
  have hpre := f.comap_pCore_of_ker_isPGroup hf hk
  rw [← hpre] at hcomm
  simpa only [mem_comap, map_mul, map_inv] using hcomm

/-- A.1.31(3) at p=3, on an arbitrary displayed finite cover. The target's
three-core has a proper nonzero normal subgroup. -/
theorem lemma_A_1_31_3_of_surjective
    (f : D →* E) (hf : Function.Surjective f) (hrank : primeRank 3 D ≤ 2)
    (hF : generalizedFitting E = pCore 3 E)
    (hEA : IsElementaryAbelian 3 (pCore 3 E)) (hV : Nat.card (pCore 3 E) = 27)
    (hr2 : 1 < primeRank 2 E) :
    ∃ R : Subgroup E, R.Normal ∧ R ≠ ⊥ ∧ R < pCore 3 E := by
  let : IsElementaryAbelian 3 (pCore 3 E) := hEA
  obtain ⟨B, hB, hBfin, g, hg, hrB, hk⟩ := exists_three_kernel_cover hrank f hf
  let : Group B := hB
  let : Finite B := hBfin
  exact reducible_three_kernel g hg hk hrB hF hV hr2

/-- Source A.1.31(3) at p=3 on the literal quotient by a normal subgroup. -/
theorem lemma_A_1_31_3 (N : Subgroup D) [N.Normal]
    (hrank : primeRank 3 D ≤ 2)
    (hF : generalizedFitting (D ⧸ N) = pCore 3 (D ⧸ N))
    (hEA : IsElementaryAbelian 3 (pCore 3 (D ⧸ N)))
    (hV : Nat.card (pCore 3 (D ⧸ N)) = 27) (hr2 : 1 < primeRank 2 (D ⧸ N)) :
    ∃ R : Subgroup (D ⧸ N), R.Normal ∧ R ≠ ⊥ ∧ R < pCore 3 (D ⧸ N) :=
  lemma_A_1_31_3_of_surjective (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) hrank hF hEA hV hr2

end CFSG.Quasithin.ChapterA
