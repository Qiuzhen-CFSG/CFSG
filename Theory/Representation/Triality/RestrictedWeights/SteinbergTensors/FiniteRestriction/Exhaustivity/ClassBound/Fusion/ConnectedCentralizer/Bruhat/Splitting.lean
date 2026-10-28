module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Splitting.Inputs

/-!
# Absorption and uniqueness reductions for actual root Bruhat forms

Transport of realized root subgroups sends the retained root factor into the
positive subgroup and the inversion factor into the opposite subgroup.
Collection across that root partition therefore yields normalizer absorption.
The Borel decompositions then refine raw B--N--B coverage to root Bruhat forms.

The opposite big cell proves triangular separation and uniqueness within each
torus coset unconditionally from `Geometry`. Separation of distinct Borel
double cosets gives global injectivity. The final assembly keeps root
transport, root-partition collection, and cell separation explicit; their
existence is still required for the unconditional source theorem.

Source: GLS3 1.11.3--1.11.5 and 1.12.7(a),
`refs/KGroup/GLS3/Chapter1.tex`; Steinberg 6.2--6.3,
`refs/KGroup/GLS3/Chapter2St2.tex`.
-/

public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ConnectedCentralizer.Bruhat.Splitting
universe u
variable {k : Type u} [Field k] [CharP k 2]
  {K : Variety k} [AlgebraicGroup K]

/-- The same transport in the inverse-conjugation convention of GLS3 1.11.5. -/
theorem rootTransport_inverse (S : Geometry K)
    {f : S.torus.normalizer.toSubgroup →* AmbientCount.Weyl} (h : RootTransport S f)
    (n : S.torus.normalizer.toSubgroup) (a : S.roots.Root) :
    (S.roots.rootSubgroup a).conjugate ((n : Variety.Point K)⁻¹) =
      S.roots.rootSubgroup (S.rootIndex.symm
        ((typeDRootPairing 2).weylGroupToPerm (f n)⁻¹ (S.rootIndex a))) := by
  change _ = S.roots.rootSubgroup (rootAction S (f n)⁻¹ a)
  simpa only [map_inv, Subgroup.coe_inv] using h n⁻¹ a

private theorem conjugate_root_mem (S : Geometry K)
    {f : S.torus.normalizer.toSubgroup →* AmbientCount.Weyl} (h : RootTransport S f)
    (n : S.torus.normalizer.toSubgroup) (a : S.roots.Root) {x : Variety.Point K}
    (hx : x ∈ S.roots.rootSubgroup a) :
    (n : Variety.Point K) * x * (n : Variety.Point K)⁻¹ ∈
      S.roots.rootSubgroup (rootAction S (f n) a) := by
  rw [← h n a, ClosedSubgroup.mem_conjugate_iff]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  exact hx

private theorem conjugate_generated_le (S : Geometry K)
    {f : S.torus.normalizer.toSubgroup →* AmbientCount.Weyl} (h : RootTransport S f)
    (n : S.torus.normalizer.toSubgroup) (A Q : Set S.roots.Root)
    (hAQ : ∀ a ∈ A, rootAction S (f n) a ∈ Q) :
    RootSubgroupGenerated S.roots A ≤
      (RootSubgroupGenerated S.roots Q).comap
        (MulAut.conj (n : Variety.Point K)).toMonoidHom := by
  apply (RootSubgroupGenerated_le_iff _ _ _).mpr
  intro a ha x hx
  exact rootSubgroup_le_RootSubgroupGenerated S.roots (hAQ a ha)
    (conjugate_root_mem S h n a hx)

/-- Conjugation sends the retained positive-root factor back into the
positive subgroup. -/
theorem retained_conjugate_mem_positive (S : Geometry K)
    {f : S.torus.normalizer.toSubgroup →* AmbientCount.Weyl} (h : RootTransport S f)
    (n : S.torus.normalizer.toSubgroup) {a : Variety.Point K}
    (ha : a ∈ retainedFactor S (f n)) :
    (n : Variety.Point K) * a * (n : Variety.Point K)⁻¹ ∈ positiveGroup S :=
  conjugate_generated_le S h n (retainedRoots S (f n)) S.roots.positive
    (fun _ hα => hα.2) ha

/-- The inversion factor has the actual opposite-subgroup condition in
`Bruhat.Form`, not merely an abstract label of negative roots. -/
theorem inversion_conjugate_mem_negative (S : Geometry K)
    {f : S.torus.normalizer.toSubgroup →* AmbientCount.Weyl} (h : RootTransport S f)
    (n : S.torus.normalizer.toSubgroup) {v : Variety.Point K}
    (hv : v ∈ inversionFactor S (f n)) :
    (n : Variety.Point K) * v * (n : Variety.Point K)⁻¹ ∈ negativeGroup S := by
  apply conjugate_generated_le S h n (inversionRoots S (f n))
    (S.roots.neg ⁻¹' S.roots.positive) _ hv
  intro a ha
  have hall : rootAction S (f n) a ∈
      S.roots.positive ∪ S.roots.neg ⁻¹' S.roots.positive := by
    rw [S.bigCell.data.positive.2.1]
    exact Set.mem_univ _
  exact hall.resolve_left ha.2

/-- Root collection across the positive/negative image partition gives the
normalizer absorption formula. -/
theorem absorb_of_rootPartitionProducts (S : Geometry K)
    {f : S.torus.normalizer.toSubgroup →* AmbientCount.Weyl} (h : RootTransport S f)
    (hproducts : RootPartitionProducts S)
    (n : S.torus.normalizer.toSubgroup) (q : Variety.Point K)
    (hq : q ∈ positiveGroup S) :
    ∃ a v : Variety.Point K,
      a ∈ positiveGroup S ∧ v ∈ inversionFactor S (f n) ∧
        (n : Variety.Point K) * q = a * (n : Variety.Point K) * v := by
  obtain ⟨a, v, ha, hv, rfl⟩ := hproducts (f n) q hq
  refine ⟨(n : Variety.Point K) * a * (n : Variety.Point K)⁻¹, v,
    retained_conjugate_mem_positive S h n ha, hv, ?_⟩
  group

variable [IsAlgClosed k]

/-- The triangular separation needs only the actual big-cell intersection,
the torus, and the opposite condition on the right factor. -/
theorem triangular (S : Geometry K) (n : S.torus.normalizer.toSubgroup)
    {v t : Variety.Point K}
    (hv : (n : Variety.Point K) * v * (n : Variety.Point K)⁻¹ ∈ negativeGroup S)
    (ht : t ∈ S.torus.toSubgroup)
    (hvt : (n : Variety.Point K) * (v * t) * (n : Variety.Point K)⁻¹ ∈ positiveGroup S) :
    v = 1 ∧ t = 1 :=
  S.bigCell.triangular_separation S.maximalTorus.1 n hv ht hvt

/-- In particular the actual inversion factor has triangular separation. -/
theorem inversion_triangular (S : Geometry K)
    {f : S.torus.normalizer.toSubgroup →* AmbientCount.Weyl} (h : RootTransport S f)
    (n : S.torus.normalizer.toSubgroup) {v t : Variety.Point K}
    (hv : v ∈ inversionFactor S (f n)) (ht : t ∈ S.torus.toSubgroup)
    (hvt : (n : Variety.Point K) * (v * t) * (n : Variety.Point K)⁻¹ ∈ positiveGroup S) :
    v = 1 ∧ t = 1 :=
  triangular S n (inversion_conjugate_mem_negative S h n hv) ht hvt

/-- Within a torus coset, the actual three factors are unique. Distinct-cell
separation is a separate premise of global injectivity. -/
theorem form_eq_of_middle_torus (S : Geometry K) (a b : Bruhat.Form S)
    (hvalue : Bruhat.value S a = Bruhat.value S b)
    (hmiddle : a.middle⁻¹ * b.middle ∈ S.torus.toSubgroup) : a = b := by
  have ht : a.middle * b.middle⁻¹ ∈ S.torus.toSubgroup := by
    have hh := (Subgroup.mem_normalizer_iff.mp a.middle_mem
      (a.middle⁻¹ * b.middle)⁻¹).mp (S.torus.inv_mem hmiddle)
    convert hh using 1
    group
  have heq : a.left * a.middle * a.right = b.left * b.middle * b.right := hvalue
  have hleft : a.left = b.left := by
    have hbot : a.left⁻¹ * b.left ∈ (⊥ : Subgroup (Variety.Point K)) := by
      rw [← S.bigCell.positive_inf_negativeBorel_eq_bot S.maximalTorus.1]
      refine ⟨(positiveGroup S).mul_mem ((positiveGroup S).inv_mem a.left_mem) b.left_mem, ?_⟩
      have hx : a.left⁻¹ * b.left =
          (a.middle * a.right * a.middle⁻¹) * (a.middle * b.middle⁻¹) *
            (b.middle * b.right * b.middle⁻¹)⁻¹ := by
        calc
          _ = a.left⁻¹ * (b.left * b.middle * b.right) * (b.middle * b.right)⁻¹ := by group
          _ = a.left⁻¹ * (a.left * a.middle * a.right) * (b.middle * b.right)⁻¹ := by rw [← heq]
          _ = _ := by group
      rw [hx]
      exact S.bigCell.data.Bopp.mul_mem
        (S.bigCell.data.Bopp.mul_mem (S.bigCell.negative_le_borel a.opposite_mem)
          (S.bigCell.torus_le_negative ht))
        (S.bigCell.data.Bopp.inv_mem (S.bigCell.negative_le_borel b.opposite_mem))
    exact inv_mul_eq_one.mp (Subgroup.mem_bot.mp hbot)
  have hmr : a.middle * a.right = b.middle * b.right := by
    apply mul_left_cancel (a := a.left)
    simpa only [← mul_assoc, hleft] using heq
  have hmU : a.middle⁻¹ * b.middle ∈ positiveGroup S := by
    have h : a.middle⁻¹ * b.middle = a.right * b.right⁻¹ := by
      calc
        _ = a.middle⁻¹ * (b.middle * b.right) * b.right⁻¹ := by group
        _ = a.middle⁻¹ * (a.middle * a.right) * b.right⁻¹ := by rw [← hmr]
        _ = _ := by group
    rw [h]
    exact (positiveGroup S).mul_mem a.right_mem ((positiveGroup S).inv_mem b.right_mem)
  have hm : a.middle = b.middle := by
    have hh : a.middle⁻¹ * b.middle ∈ S.torus.toSubgroup ⊓ positiveGroup S :=
      ⟨hmiddle, hmU⟩
    rw [S.bigCell.torus_inf_positive_eq_bot S.maximalTorus.1] at hh
    exact inv_mul_eq_one.mp (Subgroup.mem_bot.mp hh)
  have hr : a.right = b.right := by
    rw [hm] at hmr
    exact mul_left_cancel hmr
  cases a
  cases b
  cases hleft
  cases hm
  cases hr
  rfl

/-- Actual Borel double-coset separation supplies the remaining global
uniqueness step. -/
theorem injective_of_cellSeparation (S : Geometry K) (hcell : CellSeparation S) :
    Function.Injective (Bruhat.value S) := by
  intro a b hab
  apply form_eq_of_middle_torus S a b hab
  exact hcell ⟨a.middle, a.middle_mem⟩ ⟨b.middle, b.middle_mem⟩
    a.left a.right b.left b.right
    (S.bigCell.positive_le_borel a.left_mem) (S.bigCell.positive_le_borel a.right_mem)
    (S.bigCell.positive_le_borel b.left_mem) (S.bigCell.positive_le_borel b.right_mem) hab

omit [IsAlgClosed k] in
/-- Raw B--N--B coverage refines to actual root Bruhat forms once the
root-partition collection and normalizer transport have been proved. -/
theorem surjective_of_rootPartitionProducts (S : Geometry K)
    {f : S.torus.normalizer.toSubgroup →* AmbientCount.Weyl} (h : RootTransport S f)
    (hproducts : RootPartitionProducts S) (hcover : Bruhat.BorelCoverage S) :
    Function.Surjective (Bruhat.value S) := by
  intro g
  obtain ⟨b, n, c, hb, hn, hc, hg⟩ := hcover g
  obtain ⟨t, u, ht, hu, rfl⟩ := (S.bigCell.positive_decomposition b).mp hb
  obtain ⟨s, q, hs, hq, rfl⟩ := (S.bigCell.positive_decomposition c).mp hc
  let m : S.torus.normalizer.toSubgroup :=
    ⟨t * n * s, S.torus.normalizer.mul_mem
      (S.torus.normalizer.mul_mem (S.torus.toSubgroup.le_normalizer ht) hn)
      (S.torus.toSubgroup.le_normalizer hs)⟩
  have htu : t * u * t⁻¹ ∈ positiveGroup S :=
    (Subgroup.mem_normalizer_iff.mp
      (torus_le_rootSubgroupGenerated_normalizer S.roots S.realized S.roots.positive ht) u).mp hu
  obtain ⟨a, v, ha, hv, hmq⟩ := absorb_of_rootPartitionProducts S h hproducts m q hq
  let form : Bruhat.Form S :=
    { left := (t * u * t⁻¹) * a
      middle := m
      right := v
      left_mem := (positiveGroup S).mul_mem htu ha
      middle_mem := m.property
      right_mem := inversionFactor_le_positive S (f m) hv
      opposite_mem := inversion_conjugate_mem_negative S h m hv }
  refine ⟨form, ?_⟩
  change ((t * u * t⁻¹) * a) * (m : Variety.Point K) * v = g
  calc
    _ = (t * u * t⁻¹) * ((m : Variety.Point K) * q) := by rw [hmq]; group
    _ = (t * u) * n * (s * q) := by dsimp [m]; group
    _ = g := hg.symm

/-- Conditional assembly with every remaining geometric input visible.
The source theorem requires independently constructing these inputs. -/
theorem bijective_of_root_geometry (S : Geometry K)
    {f : S.torus.normalizer.toSubgroup →* AmbientCount.Weyl} (h : RootTransport S f)
    (hproducts : RootPartitionProducts S) (hcell : CellSeparation S)
    (hcover : Bruhat.BorelCoverage S) : Function.Bijective (Bruhat.value S) :=
  ⟨injective_of_cellSeparation S hcell,
    surjective_of_rootPartitionProducts S h hproducts hcover⟩

end ConnectedCentralizer.Bruhat.Splitting
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
