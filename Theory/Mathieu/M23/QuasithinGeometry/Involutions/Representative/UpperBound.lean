module

public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Representative.Basic
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Representative.Fano

/-!
# Upper bound for the concrete M23 involution centralizer

A centralizing permutation is determined by the images of `(1,2,3,16)`.
The first three points form a noncollinear ordered basis of the Fano plane
on the fixed heptad, with 168 possible images. The fourth point lies among
its sixteen exterior points.

For faithfulness, preservation of the Fano lines first determines all seven
fixed-heptad points. Seven explicitly indexed Witt heptads each contain point 16 and exactly
three points of the fixed heptad. Unique four-set extension therefore fixes
each of these heptads setwise. Their incidence patterns separate the sixteen exterior points.
Both this separation and the tuple count are kernel-checked finite certificates.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, Lemma 5.2.21,
printed p.657 (PDF p.674). The incidence certificates use this repository's
concrete derived Witt design, without any involution-fusion assumption.
-/

open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

private theorem fixes_line_third (g : M23)
    (hg : g • involutionLines = involutionLines)
    (a b c : Fin 23) (ha : g • a = a) (hb : g • b = b)
    (hca : c ≠ a) (hcb : c ≠ b) (hL : {a,b,c} ∈ involutionLines)
    (hu : ∀ d : Fin 23, d ≠ a → d ≠ b → {a,b,d} ∈ involutionLines → d = c) :
    g • c = c := by
  apply hu
  · intro h
    apply hca
    exact g.val.injective (h.trans ha.symm)
  · intro h
    apply hcb
    exact g.val.injective (h.trans hb.symm)
  · have h := Finset.smul_mem_smul_finset hL (a := g)
    simpa only [hg, Finset.smul_finset_insert, Finset.smul_finset_singleton, ha, hb] using h

private theorem fixes_heptad (g : M23)
    (hg : g ∈ Subgroup.centralizer ({involutionRepresentative} : Set M23))
    (h1 : g • (1 : Fin 23) = 1) (h2 : g • (2 : Fin 23) = 2)
    (h3 : g • (3 : Fin 23) = 3) :
    ∀ x ∈ involutionHeptad, g • x = x := by
  have hL := centralizer_preserves_involutionLines g hg
  have h5 := fixes_line_third g hL 1 2 5 h1 h2 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
  have h4 := fixes_line_third g hL 1 3 4 h1 h3 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
  have h17 := fixes_line_third g hL 2 3 17 h2 h3 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
  have h11 := fixes_line_third g hL 2 4 11 h2 h4 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [involutionHeptad, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals assumption

/-- Seven heptads through 16 whose incidence distinguishes exterior points. -/
private def separatingIndices : Fin 7 → Fin 253 := ![4,7,12,21,34,94,110]

private theorem separating_four (i : Fin 7) :
    ((m23BlockAt (separatingIndices i)) ∩ insert 16 involutionHeptad).card = 4 := by
  revert i
  decide +kernel

private theorem separating_points : ∀ a b : Fin 23,
    a ∉ involutionHeptad → b ∉ involutionHeptad →
    (∀ i : Fin 7, a ∈ m23BlockAt (separatingIndices i) ↔
      b ∈ m23BlockAt (separatingIndices i)) → a = b := by
  decide +kernel

private theorem fixes_all (g : M23)
    (hF : ∀ x ∈ involutionHeptad, g • x = x)
    (h16 : g • (16 : Fin 23) = 16) : g = 1 := by
  have hB (i : Fin 7) : g • m23BlockAt (separatingIndices i) =
      m23BlockAt (separatingIndices i) := by
    let S := m23BlockAt (separatingIndices i) ∩ insert 16 involutionHeptad
    have hS : g • S = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.mp hx
        have hy' := (Finset.mem_inter.mp hy).2
        have he : g • y = y := by
          rcases Finset.mem_insert.mp hy' with rfl | hy'
          · exact h16
          · exact hF y hy'
        rwa [he]
      · simp
    have hm : m23BlockAt (separatingIndices i) ∈ m23Blocks :=
      Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    apply heptad_eq_of_four_subset (separating_four i) (smul_heptad g hm) hm
    · have hs := Finset.smul_finset_subset_smul_finset (a := g)
        (Finset.inter_subset_left : S ⊆ m23BlockAt (separatingIndices i))
      rwa [hS] at hs
    · exact Finset.inter_subset_left
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change g • x = x
  by_cases hx : x ∈ involutionHeptad
  · exact hF x hx
  · refine separating_points (g • x) x ?_ hx ?_
    · intro hgx
      have he := hF (g • x) hgx
      have he' : g • x = x := g.val.injective he
      exact hx (he' ▸ hgx)
    · intro i
      exact MulAction.mem_stabilizer_finset.mp
        (MulAction.mem_stabilizer_iff.mpr (hB i)) x

/-- Fixing a Fano basis and one exterior point forces a centralizer element
of the concrete representative to be the identity. -/
public theorem involutionCentralizer_eq_one_of_fix_basis (g : M23)
    (hg : g ∈ Subgroup.centralizer ({involutionRepresentative} : Set M23))
    (h1 : g • (1 : Fin 23) = 1) (h2 : g • (2 : Fin 23) = 2)
    (h3 : g • (3 : Fin 23) = 3) (h16 : g • (16 : Fin 23) = 16) :
    g = 1 :=
  fixes_all g (fixes_heptad g hg h1 h2 h3) h16

private noncomputable abbrev C := Subgroup.centralizer ({involutionRepresentative} : Set M23)

private def bases : Finset (Fin 23 × Fin 23 × Fin 23) :=
  (involutionHeptad.product (involutionHeptad.product involutionHeptad)).filter
    (fun t => t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
      {t.1, t.2.1, t.2.2} ∉ involutionLines)

private def exterior : Finset (Fin 23) := Finset.univ \ involutionHeptad

private theorem image_mem_heptad (g : C) (x : Fin 23) :
    (g.val • x ∈ involutionHeptad) ↔ x ∈ involutionHeptad := by
  exact MulAction.mem_stabilizer_finset.mp
    (MulAction.mem_stabilizer_iff.mpr (centralizer_preserves_involutionHeptad g.val g.property)) x

private theorem image_mem_bases (g : C) :
    (g.val • (1 : Fin 23), g.val • (2 : Fin 23), g.val • (3 : Fin 23)) ∈ bases := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    refine ⟨(image_mem_heptad g 1).mpr (by decide +kernel), ?_⟩
    exact Finset.mem_product.mpr ⟨(image_mem_heptad g 2).mpr (by decide +kernel),
      (image_mem_heptad g 3).mpr (by decide +kernel)⟩
  · refine ⟨g.val.val.injective.ne (by decide), g.val.val.injective.ne (by decide),
      g.val.val.injective.ne (by decide), ?_⟩
    intro h
    have h' : g.val • ({1,2,3} : Finset (Fin 23)) ∈ involutionLines := by
      simpa only [Finset.smul_finset_insert, Finset.smul_finset_singleton] using h
    have he := centralizer_preserves_involutionLines g.val g.property
    rw [← he] at h'
    have hn : ({1,2,3} : Finset (Fin 23)) ∉ involutionLines := by decide +kernel
    exact hn (by simpa using h')

private noncomputable def record (g : C) : bases × exterior :=
  (⟨_, image_mem_bases g⟩, ⟨g.val • (16 : Fin 23), by
    simp only [exterior, Finset.mem_sdiff, Finset.mem_univ, true_and]
    rw [image_mem_heptad]
    decide +kernel⟩)

private theorem record_injective : Function.Injective record := by
  intro g h he
  have h1 : g.val • (1 : Fin 23) = h.val • (1 : Fin 23) :=
    congrArg (fun t : bases × exterior => t.1.val.1) he
  have h2 : g.val • (2 : Fin 23) = h.val • (2 : Fin 23) :=
    congrArg (fun t : bases × exterior => t.1.val.2.1) he
  have h3 : g.val • (3 : Fin 23) = h.val • (3 : Fin 23) :=
    congrArg (fun t : bases × exterior => t.1.val.2.2) he
  have h16 : g.val • (16 : Fin 23) = h.val • (16 : Fin 23) :=
    congrArg (fun t : bases × exterior => t.2.val) he
  have hf {x : Fin 23} (hx : g.val • x = h.val • x) : (h⁻¹ * g).val • x = x := by
    change (h.val⁻¹ * g.val) • x = x
    rw [mul_smul, hx, inv_smul_smul]
  have hid := involutionCentralizer_eq_one_of_fix_basis
    (h⁻¹ * g).val (h⁻¹ * g).property (hf h1) (hf h2) (hf h3) (hf h16)
  apply Subtype.ext
  exact (inv_mul_eq_one.mp hid).symm

/-- The concrete involution centralizer has at most `168 * 16 = 2688` elements. -/
public theorem involutionRepresentative_centralizer_card_le :
    Nat.card (Subgroup.centralizer ({involutionRepresentative} : Set M23)) ≤ 2688 := by
  have h := Nat.card_le_card_of_injective record record_injective
  have hc : Nat.card (bases × exterior) = 2688 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  exact hc ▸ h

end Sporadic.Mathieu.M23Geometry
