module
public import Theory.GroupTheory.ConjugationOrbitSize
public import Theory.GroupTheory.CentralizerSylowNormalizerFusion
public import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# Fusion on two odd orbits

An odd conjugacy orbit under a subgroup containing a Sylow two-subgroup has
an element fixed by that Sylow subgroup. Two ambient-conjugate such elements
have a common centralizer Sylow; fusion is therefore realized in its normalizer.
Consequently, on an invariant set consisting of at most two odd orbits of a
smaller subgroup, containment of the Sylow normalizer suffices for fusion.
If the larger subgroup merges the two orbits, fusion is already controlled.

Source: the six-letter case of Aschbacher–Smith 12.2.16, printed p.800.
-/

public noncomputable section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem odd_orbit_fixed (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (x : G)
    (hodd : Odd (conjugacyOrbit M x).ncard) :
    ∃ a ∈ conjugacyOrbit M x, (T : Subgroup G) ≤ centralizer ({a} : Set G) := by
  let : MulAction T G := MulAction.compHom G (MulAut.conj.comp (T : Subgroup G).subtype)
  let X : SubMulAction T G := {
    carrier := conjugacyOrbit M x
    smul_mem' := by
      rintro t y ⟨m,rfl⟩
      refine ⟨⟨(t : G) * m, M.mul_mem (hTM t.property) m.property⟩, ?_⟩
      change ((t : G) * m) * x * ((t : G) * m)⁻¹ =
        (t : G) * ((m : G) * x * (m : G)⁻¹) * (t : G)⁻¹
      simp only [mul_inv_rev, mul_assoc] }
  obtain ⟨a,ha⟩ := T.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card X
    (by change ¬ 2 ∣ (conjugacyOrbit M x).ncard
        rw [← even_iff_two_dvd]
        exact Nat.not_even_iff_odd.mpr hodd)
  refine ⟨a,a.property,?_⟩
  intro t ht
  exact mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (ha ⟨t,ht⟩)))

/-- Odd local orbits supply central Sylow representatives, so Sylow-normalizer
control suffices for their ambient fusion. -/
theorem fusion_of_odd_conjugacyOrbits (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hNT : normalizer (T : Set G) ≤ M) {x y : G}
    (hx : Odd (conjugacyOrbit M x).ncard) (hy : Odd (conjugacyOrbit M y).ncard)
    (hxy : IsConj x y) : y ∈ conjugacyOrbit M x := by
  obtain ⟨a,⟨m,hm⟩,ha⟩ := odd_orbit_fixed T M hTM x hx
  obtain ⟨b,⟨n,hn⟩,hb⟩ := odd_orbit_fixed T M hTM y hy
  have hab : IsConj a b :=
    (isConj_iff.mpr ⟨(m : G),hm⟩).symm.trans
      (hxy.trans (isConj_iff.mpr ⟨(n : G),hn⟩))
  let S := T.subtype ha
  have hS : (S : Subgroup (centralizer ({a} : Set G))).map
      (centralizer ({a} : Set G)).subtype = (T : Subgroup G) := by
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le ha]
  obtain ⟨g,hg,hgab⟩ := exists_normalizer_conjugator_of_centralizer_sylow a b S
    (by rw [hS]; exact hb) hab
  rw [hS] at hg
  refine ⟨⟨(n : G)⁻¹ * g * m, M.mul_mem (M.mul_mem (M.inv_mem n.property)
    (hNT hg)) m.property⟩, ?_⟩
  change MulAut.conj ((n : G)⁻¹ * g * m) x = y
  rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
  rw [show MulAut.conj (m : G) x = a from hm, hgab, ← hn]
  simp [mul_assoc]

/-- A subset covered by two odd subgroup-orbits has fusion controlled by M,
provided M contains the Sylow normalizer. M may merge the two orbits. -/
theorem fusion_of_two_odd_orbits (T : Sylow 2 G) (L M : Subgroup G)
    (hLM : L ≤ M) (hTM : (T : Subgroup G) ≤ M)
    (hNT : normalizer (T : Set G) ≤ M) (U : Set G)
    (hinv : ∀ m ∈ M, ∀ x ∈ U, m * x * m⁻¹ ∈ U)
    (hodd : ∀ x ∈ U, Odd (conjugacyOrbit L x).ncard)
    (hcover : ∀ x ∈ U, ∀ y ∈ U, y ∉ conjugacyOrbit L x →
      U ⊆ conjugacyOrbit L x ∪ conjugacyOrbit L y)
    {x y : G} (hx : x ∈ U) (hy : y ∈ U) (hxy : IsConj x y) :
    y ∈ conjugacyOrbit M x := by
  let : MulAction M G := MulAction.compHom G (MulAut.conj.comp M.subtype)
  have hsub (w : G) : conjugacyOrbit L w ⊆ conjugacyOrbit M w := by
    rintro _ ⟨l,rfl⟩
    exact ⟨⟨l,hLM l.property⟩,rfl⟩
  have heq {a b : G} (ha : a ∈ U) (hb : b ∈ U)
      (hne : b ∉ conjugacyOrbit M a) : conjugacyOrbit M a = conjugacyOrbit L a := by
    apply Set.Subset.antisymm ?_ (hsub a)
    intro w hw
    have hwU : w ∈ U := by
      obtain ⟨m,rfl⟩ := hw
      exact hinv m m.property a ha
    rcases hcover a ha b hb (fun h => hne (hsub a h)) hwU with hwL | hwL
    · exact hwL
    · exfalso
      apply hne
      have hb' : MulAction.orbit M w = MulAction.orbit M b :=
        MulAction.orbit_eq_iff.mpr (hsub b hwL)
      have ha' : MulAction.orbit M w = MulAction.orbit M a :=
        MulAction.orbit_eq_iff.mpr hw
      exact MulAction.orbit_eq_iff.mp (hb'.symm.trans ha')
  by_contra hnot
  have hnot' : x ∉ conjugacyOrbit M y := by
    intro hmem
    apply hnot
    exact MulAction.orbit_eq_iff.mp (MulAction.orbit_eq_iff.mpr hmem).symm
  apply hnot
  apply fusion_of_odd_conjugacyOrbits T M hTM hNT ?_ ?_ hxy
  · rw [heq hx hy hnot]
    exact hodd x hx
  · rw [heq hy hx hnot']
    exact hodd y hy

end Subgroup
