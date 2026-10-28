module

public import Theory.SpecificGroups.Suzuki.SplitNormalizerGeometry
public import Theory.GroupTheory.RightConjugation

/-!
# Suzuki Borel pair geometry

For an arbitrary involution outside the concrete Suzuki Borel, the intersection
of the Borel with its right conjugate is a cyclic complement to the root group,
of order `q - 1`, inverted by the given involution. The Borel is transitive on
its outside involutions.

Root regularity first moves the image of infinity to zero. The adjusted
involution then has the form torus times Weyl. Taking a square root in the
odd-order torus produces a Borel conjugator from Weyl to the original
involution. Transporting the standard pair intersection through this same
conjugator proves the assertions with the literal right-conjugation convention.

Sources: GLS, Volume 4, Chapter 4, Lemma 3.2(c–e,i), and its use in Chapter 2,
Lemma 12.2(d,f); the concrete ovoid and torus calculations are those of
Huppert–Blackburn, Finite Groups III, XI.3.3 and XI.3.10.
-/

noncomputable section
namespace BenderSuzuki.MatrixGroups
open PFAppendixIII PFchapter1section1
open scoped Pointwise

private theorem root_le_borel (m : ℕ) : SuzukiRootSubgroup m ≤ SuzukiBorelSubgroup m := by
  rw [suzukiBorelSubgroup_eq_sup]
  exact le_sup_left

private theorem torus_le_borel (m : ℕ) : SuzukiSplitTorus m ≤ SuzukiBorelSubgroup m := by
  rw [suzukiBorelSubgroup_eq_sup]
  exact le_sup_right

/-- Every outside involution is a Borel conjugate of the standard Weyl element. -/
public theorem suzukiBorel_conj_weyl (m : ℕ) (hm : 0 < m)
    (u : SuzukiMatrixGroup m) (hu : IsInvolution u) (huB : u ∉ SuzukiBorelSubgroup m) :
    ∃ b ∈ SuzukiBorelSubgroup m, MulAut.conj b (suzukiWeyl m) = u := by
  have hui : u • suzukiOvoidInfinity m ≠ suzukiOvoidInfinity m := by
    simpa only [suzukiBorelSubgroup_eq_stabilizer m hm, MulAction.mem_stabilizer_iff] using huB
  obtain ⟨r, hr, _⟩ := suzukiRootSubgroup_regular m (u • suzukiOvoidInfinity m)
    (suzukiOvoidZero m) hui (suzukiOvoidInfinity_ne_zero m).symm
  have hrii := suzukiRootSubgroup_fix_infinity m hm _
    ((SuzukiRootSubgroup m).inv_mem r.property)
  let y := MulAut.conj (r : SuzukiMatrixGroup m) u
  have hyi : y • suzukiOvoidInfinity m = suzukiOvoidZero m := by
    simpa only [y, MulAut.conj_apply, mul_smul, hrii] using hr
  have hyy : y * y = 1 := by
    rw [← pow_two, ← map_pow, hu.2, map_one]
  have hyz : y • suzukiOvoidZero m = suzukiOvoidInfinity m := by
    rw [← hyi, ← mul_smul, hyy, one_smul]
  have hyt : y * suzukiWeyl m ∈ SuzukiSplitTorus m := by
    rw [mem_suzukiSplitTorus_iff_fix_pair]
    simp only [mul_smul, suzukiWeyl_smul_infinity, suzukiWeyl_smul_zero, hyi, hyz, and_self]
  let t : SuzukiSplitTorus m := ⟨y * suzukiWeyl m, hyt⟩
  have hodd : Odd (Nat.card (SuzukiSplitTorus m)) := by
    rw [suzukiSplitTorus_card m hm]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero (by decide : Even (2 : ℕ)) (by omega)) odd_one
  obtain ⟨s, hs⟩ := (Nat.coprime_two_right.mpr hodd).pow_left_bijective.surjective t
  have hconj : MulAut.conj (s : SuzukiMatrixGroup m) (suzukiWeyl m) = y := by
    have hinv := suzukiWeyl_conj_splitTorus m s⁻¹
    change suzukiWeyl m * (s : SuzukiMatrixGroup m)⁻¹ * suzukiWeyl m =
      ((s : SuzukiMatrixGroup m)⁻¹)⁻¹ at hinv
    rw [inv_inv] at hinv
    have hs' : (s : SuzukiMatrixGroup m) * s = y * suzukiWeyl m := by
      simpa only [pow_two, Subgroup.coe_mul, t] using congrArg Subtype.val hs
    change (s : SuzukiMatrixGroup m) * suzukiWeyl m * (s : SuzukiMatrixGroup m)⁻¹ = y
    calc
      _ = s * (suzukiWeyl m * (s : SuzukiMatrixGroup m)⁻¹ * suzukiWeyl m) *
          suzukiWeyl m := by rw [mul_assoc, mul_assoc, mul_assoc, suzukiWeyl_sq, mul_one]
      _ = (s : SuzukiMatrixGroup m) * s * suzukiWeyl m := by rw [hinv]
      _ = y := by rw [hs', mul_assoc, suzukiWeyl_sq, mul_one]
  refine ⟨(r : SuzukiMatrixGroup m)⁻¹ * s,
    (SuzukiBorelSubgroup m).mul_mem
      ((SuzukiBorelSubgroup m).inv_mem (root_le_borel m r.property))
      (torus_le_borel m s.property), ?_⟩
  calc
    _ = (r : SuzukiMatrixGroup m)⁻¹ *
        (MulAut.conj (s : SuzukiMatrixGroup m) (suzukiWeyl m)) * r := by
      simp only [MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc]
    _ = u := by rw [hconj]; simp [y, MulAut.conj_apply, mul_assoc]

private theorem mem_rightConjugate_iff {G : Type*} [Group G]
    (H : Subgroup G) (g x : G) : x ∈ rightConjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hz
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩

private theorem map_rightConjugate {G H : Type*} [Group G] [Group H]
    (f : G →* H) (B : Subgroup G) (t : G) :
    (rightConjugate B t).map f = rightConjugate (B.map f) (f t) := by
  simp only [rightConjugate, Subgroup.conjBy, Subgroup.map_map]
  congr 1
  ext x
  simp

/-- The literal standard Borel intersection is the split torus. -/
public theorem suzukiBorel_pair_weyl (m : ℕ) (hm : 0 < m) :
    SuzukiBorelSubgroup m ⊓ rightConjugate (SuzukiBorelSubgroup m) (suzukiWeyl m) =
      SuzukiSplitTorus m := by
  ext x
  rw [Subgroup.mem_inf, mem_rightConjugate_iff, suzukiBorelSubgroup_eq_stabilizer m hm,
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    mem_suzukiSplitTorus_iff_fix_pair, suzukiWeyl_inv]
  simp only [mul_smul, suzukiWeyl_smul_infinity]
  constructor
  · rintro ⟨hi, hz⟩
    refine ⟨hi, ?_⟩
    apply MulAction.injective (suzukiWeyl m)
    simpa only [suzukiWeyl_smul_zero] using hz
  · rintro ⟨hi, hz⟩
    exact ⟨hi, by rw [hz, suzukiWeyl_smul_zero]⟩

/-- A Borel marking of an outside involution identifies its actual pair intersection. -/
public theorem suzukiBorel_pair_eq_map (m : ℕ) (hm : 0 < m)
    (b u : SuzukiMatrixGroup m) (hb : b ∈ SuzukiBorelSubgroup m)
    (hbu : MulAut.conj b (suzukiWeyl m) = u) :
    SuzukiBorelSubgroup m ⊓ rightConjugate (SuzukiBorelSubgroup m) u =
      (SuzukiSplitTorus m).map (MulAut.conj b).toMonoidHom := by
  have hB : (SuzukiBorelSubgroup m).map (MulAut.conj b).toMonoidHom =
      SuzukiBorelSubgroup m :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ((SuzukiBorelSubgroup m).le_normalizer hb)
  rw [← suzukiBorel_pair_weyl m hm,
    Subgroup.map_inf _ _ _ (MulAut.conj b).injective, map_rightConjugate, hB]
  exact congrArg (fun x => SuzukiBorelSubgroup m ⊓ rightConjugate (SuzukiBorelSubgroup m) x)
    hbu.symm

/-- The pair intersection for any outside involution is cyclic. -/
public theorem suzukiBorel_pair_isCyclic (m : ℕ) (hm : 0 < m)
    (u : SuzukiMatrixGroup m) (hu : IsInvolution u) (huB : u ∉ SuzukiBorelSubgroup m) :
    IsCyclic (SuzukiBorelSubgroup m ⊓ rightConjugate (SuzukiBorelSubgroup m) u :
      Subgroup (SuzukiMatrixGroup m)) := by
  obtain ⟨b, hb, hbu⟩ := suzukiBorel_conj_weyl m hm u hu huB
  rw [suzukiBorel_pair_eq_map m hm b u hb hbu]
  exact ((SuzukiSplitTorus m).equivMapOfInjective _ (MulAut.conj b).injective).isCyclic.mp
    (suzukiSplitTorus_isCyclic m hm)

/-- The pair intersection has order `q - 1`. -/
public theorem suzukiBorel_pair_card (m : ℕ) (hm : 0 < m)
    (u : SuzukiMatrixGroup m) (hu : IsInvolution u) (huB : u ∉ SuzukiBorelSubgroup m) :
    Nat.card (SuzukiBorelSubgroup m ⊓ rightConjugate (SuzukiBorelSubgroup m) u :
      Subgroup (SuzukiMatrixGroup m)) =
      2 ^ (2 * m + 1) - 1 := by
  obtain ⟨b, hb, hbu⟩ := suzukiBorel_conj_weyl m hm u hu huB
  rw [suzukiBorel_pair_eq_map m hm b u hb hbu,
    ← Nat.card_congr ((SuzukiSplitTorus m).equivMapOfInjective _
      (MulAut.conj b).injective).toEquiv]
  exact suzukiSplitTorus_card m hm

/-- The given involution inverts its pair intersection, in the right-conjugation convention. -/
public theorem suzukiBorel_pair_inverted (m : ℕ) (hm : 0 < m)
    (u : SuzukiMatrixGroup m) (hu : IsInvolution u) (huB : u ∉ SuzukiBorelSubgroup m)
    (x : SuzukiMatrixGroup m)
    (hx : x ∈ SuzukiBorelSubgroup m ⊓ rightConjugate (SuzukiBorelSubgroup m) u) :
    rightConjugateElem x u = x⁻¹ := by
  obtain ⟨b, hb, hbu⟩ := suzukiBorel_conj_weyl m hm u hu huB
  rw [suzukiBorel_pair_eq_map m hm b u hb hbu] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  rw [rightConjugateElem, hu.inv_eq_self]
  have hh := congrArg (MulAut.conj b) (suzukiWeyl_conj_splitTorus m ⟨t, ht⟩)
  simpa only [map_mul, map_inv, hbu, MulEquiv.coe_toMonoidHom] using hh

/-- The Borel acts transitively by conjugation on the involutions outside it. -/
public theorem suzukiBorel_outside_involutions_conjugate (m : ℕ) (hm : 0 < m)
    (u : SuzukiMatrixGroup m) (hu : IsInvolution u) (huB : u ∉ SuzukiBorelSubgroup m)
    (v : SuzukiMatrixGroup m) (hv : IsInvolution v) (hvB : v ∉ SuzukiBorelSubgroup m) :
    ∃ b ∈ SuzukiBorelSubgroup m, MulAut.conj b u = v := by
  obtain ⟨b, hb, hbu⟩ := suzukiBorel_conj_weyl m hm u hu huB
  obtain ⟨c, hc, hcv⟩ := suzukiBorel_conj_weyl m hm v hv hvB
  refine ⟨c * b⁻¹, (SuzukiBorelSubgroup m).mul_mem hc
    ((SuzukiBorelSubgroup m).inv_mem hb), ?_⟩
  rw [← hbu, ← hcv]
  simp [MulAut.conj_apply, mul_assoc]

/-- The root group and the actual pair intersection multiply to the Borel,
expressed as the literal product of sets. -/
public theorem suzukiBorel_pair_product (m : ℕ) (hm : 0 < m)
    (u : SuzukiMatrixGroup m) (hu : IsInvolution u) (huB : u ∉ SuzukiBorelSubgroup m) :
    (SuzukiBorelSubgroup m : Set (SuzukiMatrixGroup m)) =
      (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) *
        ((SuzukiBorelSubgroup m ⊓ rightConjugate (SuzukiBorelSubgroup m) u :
          Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m)) := by
  obtain ⟨b, hb, hbu⟩ := suzukiBorel_conj_weyl m hm u hu huB
  have hB : (SuzukiBorelSubgroup m).map (MulAut.conj b).toMonoidHom =
      SuzukiBorelSubgroup m := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((SuzukiBorelSubgroup m).le_normalizer hb)
  have hU : (SuzukiRootSubgroup m).map (MulAut.conj b).toMonoidHom =
      SuzukiRootSubgroup m := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (show b ∈ Subgroup.normalizer (SuzukiRootSubgroup m) by
      rw [suzukiRootSubgroup_normalizer m hm]; exact hb)
  have hstandard : (SuzukiBorelSubgroup m : Set (SuzukiMatrixGroup m)) =
      (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) *
        (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (suzukiSplitTorus_le_normalizer_root m), ← suzukiBorelSubgroup_eq_sup]
  rw [suzukiBorel_pair_eq_map m hm b u hb hbu]
  have himage := congrArg (Set.image (MulAut.conj b).toMonoidHom) hstandard
  rw [Set.image_mul, ← Subgroup.coe_map, ← Subgroup.coe_map, ← Subgroup.coe_map,
    hB, hU] at himage
  exact himage

end BenderSuzuki.MatrixGroups
