module
public import Theory.SpecificGroups.ReeF4.SmallCompletion.Cartan
public import Theory.SpecificGroups.ReeF4.SmallCompletion.TorusAction
public import Theory.GroupAction.PerfectFixedCover

/-!
# Cartan-fixed cosets in both native Ree parabolics

The singleton standard parabolic has its two actual Bruhat cells. In the
nonidentity cell write a coset as u w B, with u in the full positive subgroup.
Cartan fixation gives a coprime displacement in U intersect w B w⁻¹.
Coprime fixed-coset lifting and the trivial positive Cartan centralizer force
u into this intersection, leaving the marked coset w B. This uses the full
positive subgroup, including the complete Suzuki radical, at every m > 0.

Source: the Cartan apartment argument of Aschbacher–Smith F.4.10,16,
printed pp.279,282 of `refs/quasithin.pdf`; GLS3 §§2.3–2.4 for the native
Bruhat and torus calculations. The smallest field q=8 is included.
-/

public noncomputable section
namespace ReeF4.SmallCompletion
open Subgroup Parabolics LargeLocalSeeds SectionGeometry.BNPair
open Parabolics.Binary.FixedGeometry
open Theory.AlgebraicGroup.TitsSystem
open scoped Pointwise
attribute [local instance] borel_inf_normalizerWords_normal

set_option backward.isDefEq.respectTransparency false in
private theorem rank_one_cells (m : ℕ) (hm : 0 < m) (s : Side)
    (g : Model m) (hg : g ∈ parabolic m s) :
    g ∈ borel m ∨ ∃ a ∈ borel m, ∃ b ∈ borel m,
      g = a * (reflection m s).val * b := by
  have hP := MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.standardParabolic_singleton_eq_parabolic m hm s
  rw [MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.parabolic_eq_rootParabolic] at hP
  rw [←hP] at hg
  obtain ⟨w,hw,hg⟩ := ((titsSystem m).mem_standardParabolic_iff
    (Set.singleton_subset_iff.mpr (simpleReflection_mem m s)) g).mp hg
  have hc : w = 1 ∨ w = simpleReflection m s := by
    clear hg
    induction hw using Subgroup.closure_induction with
    | mem x hx => exact Or.inr (Set.mem_singleton_iff.mp hx)
    | one => exact Or.inl rfl
    | mul a b ha hb iha ihb =>
      rcases iha with rfl | rfl <;> rcases ihb with rfl | rfl
      all_goals simp_all [←pow_two, simpleReflection_sq]
    | inv a ha ih =>
      rcases ih with rfl | rfl
      · exact Or.inl (inv_one)
      · exact Or.inr (inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using simpleReflection_sq m s))
  rcases hc with rfl | rfl
  · left
    rw [(titsSystem m).bruhatCell_one] at hg
    exact hg
  · right
    simp only [Theory.AlgebraicGroup.TitsSystem.bruhatCell] at hg
    change g ∈ (borel m : Set (Model m)) * representativeSet (borel m) (normalizerWords m)
      (simpleReflection m s) * (borel m : Set (Model m)) at hg
    rw [B_mul_representativeSet_mul_B (borel m) (normalizerWords m) (simpleReflection m s) (simpleLift m s) rfl] at hg
    obtain ⟨a,ha,b,hb,he⟩ := DoubleCoset.mem_doubleCoset.mp hg
    exact ⟨a,ha,b,hb,he⟩

private theorem fixed_coset_in_cell (m : ℕ) (hm : 0 < m) (s : Side)
    (u : Model m) (hu : u ∈ unipotent m)
    (hf : ∀ t ∈ fixedTorus m,
      (reflection m s).val⁻¹ * u⁻¹ * t * u * (reflection m s).val ∈ borel m) :
    (reflection m s).val⁻¹ * u * (reflection m s).val ∈ borel m := by
  let w := (reflection m s).val
  let T := fixedTorus m
  let U := unipotent m
  let B := borel m
  have hw : w ∈ normalizer (T : Set (Model m)) := reflection_mem_normalizer_fixedTorus m s
  have hTU : T ≤ normalizer (U : Set (Model m)) :=
    (fixedTorus_le_borel m).trans (borel_le_unipotent_normalizer m)
  have hTB : T ≤ B := fixedTorus_le_borel m
  have htw (t : Model m) (ht : t ∈ T) : w⁻¹*t*w ∈ B := by
    apply hTB
    simpa only [inv_inv] using (mem_normalizer_iff.mp (inv_mem hw) t).mp ht
  let N : Subgroup (Model m) := U ⊓ B.comap (MulAut.conj w⁻¹).toMonoidHom
  have hTN : T ≤ normalizer (N : Set (Model m)) := by
    rw [le_normalizer_iff]
    intro t ht x hx
    refine ⟨(mem_normalizer_iff.mp (hTU ht) x).mp hx.1,?_⟩
    change w⁻¹*(t*x*t⁻¹)*w ∈ B
    have hxB : w⁻¹*x*w ∈ B := hx.2
    convert B.mul_mem (B.mul_mem (htw t ht) hxB) (B.inv_mem (htw t ht)) using 1
    group
  let α : T →* MulAut (Model m) := MulAut.conj.comp T.subtype
  let act : MulDistribMulAction T (Model m) := MulDistribMulAction.compHom _ α
  let : SMul T (Model m) := act.toSMul
  let : MulDistribMulAction T (Model m) := act
  let : IsInvariant T (Model m) N := ⟨fun t x => by
    change x ∈ N ↔ t.val*x*t.val⁻¹ ∈ N
    exact mem_normalizer_iff.mp (hTN t.property) x⟩
  have hsolv : Group.IsSolvable N := by
    let : Group.IsNilpotent N := ((unipotent_isPGroup m).to_le (show N ≤ unipotent m from inf_le_left)).isNilpotent
    infer_instance
  have hcopU : (Nat.card T).Coprime (Nat.card U) := by
    change (Nat.card (fixedTorus m)).Coprime (Nat.card (unipotent m))
    rw [card_unipotent,←pow_mul]
    exact (Nat.coprime_two_right.mpr
      (fixedTorus_odd_card m (splitTorus_card_odd m))).pow_right _
  have hcop : (Nat.card T).Coprime (Nat.card N) :=
    hcopU.of_dvd_right (card_dvd_of_le (show N ≤ U from inf_le_left))
  obtain ⟨n,hn⟩ := Theory.GroupAction.exists_fixed_mul_of_solvable_coprime_displacement
    N hsolv hcop u (fun t => by
      refine ⟨U.mul_mem (U.inv_mem hu) ((mem_normalizer_iff.mp (hTU t.property) u).mp hu),?_⟩
      change w⁻¹*(u⁻¹*(t.val*u*t.val⁻¹))*w ∈ B
      convert B.mul_mem (hf t.val t.property) (htw t.val⁻¹ (inv_mem t.property)) using 1
      dsimp [w]
      group)
  have hcent : u*n.val ∈ centralizer (T : Set (Model m)) := by
    intro t ht
    have hh := hn (⟨t,ht⟩ : T)
    change t*(u*n.val)*t⁻¹=u*n.val at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh)
  have hone : u*n.val=1 := mem_bot.mp ((unipotent_inf_centralizer_fixedTorus m hm).le
    ⟨U.mul_mem hu n.property.1,hcent⟩)
  have huN : u ∈ N := by
    rw [eq_inv_of_mul_eq_one_left hone]
    exact N.inv_mem n.property
  exact huN.2

/-- The full Cartan fixes exactly the two marked Borel cosets in either full
native parabolic, for every positive parameter, including q=8. -/
theorem parabolic_fixed_coset (m : ℕ) (hm : 0 < m) (s : Side)
    (g : Model m) (hg : g ∈ parabolic m s)
    (hf : ∀ t ∈ fixedTorus m, g⁻¹*t*g ∈ borel m) :
    g ∈ borel m ∨ (reflection m s).val*g ∈ borel m := by
  rcases rank_one_cells m hm s g hg with h | ⟨a,ha,b,hb,rfl⟩
  · exact Or.inl h
  right
  have hprod : a ∈ (unipotent m : Set (Model m)) * (fixedTorus m : Set (Model m)) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _
      ((fixedTorus_le_borel m).trans (borel_le_unipotent_normalizer m)),
      ←SectionGeometry.BNPair.borel_eq_unipotent_sup_fixedTorus]
    exact ha
  obtain ⟨u,hu,t,ht,rfl⟩ := hprod
  let w := (reflection m s).val
  have hw2 : w*w=1 := by simpa only [w,Subgroup.coe_pow,Subgroup.coe_one,←pow_two] using congrArg Subtype.val (reflection_sq m s)
  have hwi : w⁻¹=w := inv_eq_of_mul_eq_one_right hw2
  have htw : w⁻¹*t*w ∈ borel m := by
    apply fixedTorus_le_borel m
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp (inv_mem (reflection_mem_normalizer_fixedTorus m s)) t).mp ht
  let b' := w⁻¹*t*w*b
  have hb' : b' ∈ borel m := mul_mem htw hb
  have he : u*t*w*b=u*w*b' := by dsimp [b']; group
  have hf' : ∀ z ∈ fixedTorus m, w⁻¹*u⁻¹*z*u*w ∈ borel m := by
    intro z hz
    have hh := hf z hz
    change (u*t*w*b)⁻¹*z*(u*t*w*b) ∈ borel m at hh
    rw [he] at hh
    convert (borel m).mul_mem ((borel m).mul_mem hb' hh) (inv_mem hb') using 1
    group
  have huB := fixed_coset_in_cell m hm s u hu hf'
  change w⁻¹*u*w ∈ borel m at huB
  change w*(u*t*w*b) ∈ borel m
  rw [he]
  convert (borel m).mul_mem huB hb' using 1
  rw [hwi]
  group
end ReeF4.SmallCompletion
