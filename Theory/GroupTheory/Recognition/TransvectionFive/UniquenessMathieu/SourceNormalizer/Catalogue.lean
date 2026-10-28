module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Fusion
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Catalogue.Model

/-!
# The source Sylow catalogue and unconditional Mathieu fusion control

The matrix catalogue identifies each order-64 elementary subgroup of the
marked positive-root group. Transport through the original centralizer
marking identifies it with A₁ or A₂ in G. The unequal fusion counts then
give weak closure, fusion control by the ambient normalizers, and indices
21 and 45, discharging the catalogue premise of the conditional consumers.

Source: Aschbacher, *Sporadic Groups* (1994), 39.1(3), 39.6(1)–(3),
and 40.3–40.4, printed pp.213–219. The ambient quotient classifications
remain separate obligations.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear

/-- The order-64 elementary subgroups of the literal marked Sylow are precisely
the two marked rectangles. -/
theorem rectangleCatalogue {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z) :
    RectangleCatalogue F := by
  intro A hAT hEA h64
  let := hEA
  have hAC : A ≤ centralizer ({z} : Set G) := by
    rw [sourceSylow_eq_pullback_upper] at hAT
    exact hAT.trans (F.pullback_le upper)
  let f : A →* SL := BinaryLinear.TransvectionFiveLocal.centralizer.subtype.comp
    (F.equiv.toMonoidHom.comp (inclusion hAC))
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (F.equiv.injective.comp (inclusion_injective hAC))
  let e : A ≃* f.range := MonoidHom.ofInjective hf
  have hPu : f.range ≤ upper := by
    rintro _ ⟨a, rfl⟩
    apply (F.mem_pullback_iff upper ⟨a, hAC a.property⟩).mp
    rw [← sourceSylow_eq_pullback_upper]
    exact hAT a.property
  have hPEA : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_injective e.symm.toMonoidHom e.symm.injective
  have hPcard : Nat.card f.range = 64 := (Nat.card_congr e.toEquiv).symm.trans h64
  rcases model_elementary64_le_rectangle f.range hPu hPEA hPcard with hP | hP
  · left
    apply eq_of_le_of_card_ge ?_ (by rw [plane_card F, h64])
    intro a ha
    apply (F.mem_pullback_iff Model.plane ⟨a, hAC ha⟩).mpr
    exact hP ⟨⟨a, ha⟩, rfl⟩
  · right
    apply eq_of_le_of_card_ge ?_ (by rw [threeSpace_card F, h64])
    intro a ha
    apply (F.mem_pullback_iff Model.threeSpace ⟨a, hAC ha⟩).mpr
    exact hP ⟨⟨a, ha⟩, rfl⟩

variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

/-- The first rectangle is weakly closed in the actual Sylow subgroup. -/
theorem plane_weakly_closed (hfusion : F.MathieuFusion) (g : G)
    (hg : F.plane.map (MulAut.conj g).toMonoidHom ≤ (sourceSylow F : Subgroup G)) :
    g ∈ normalizer (F.plane : Set G) :=
  plane_weakly_closed_of_catalogue F (rectangleCatalogue F) hfusion g hg

/-- The second rectangle is weakly closed in the actual Sylow subgroup. -/
theorem threeSpace_weakly_closed (hfusion : F.MathieuFusion) (g : G)
    (hg : F.threeSpace.map (MulAut.conj g).toMonoidHom ≤ (sourceSylow F : Subgroup G)) :
    g ∈ normalizer (F.threeSpace : Set G) :=
  threeSpace_weakly_closed_of_catalogue F (rectangleCatalogue F) hfusion g hg

omit [Finite G] in
private theorem abelian_normalizes_subsets (A : Subgroup G)
    (hA : centralizer (A : Set G) = A) (X : Set G) (hX : X ⊆ A) :
    A ≤ normalizer X := by
  intro a ha
  apply mem_normalizer_iff_conj_image_eq.mpr
  calc
    MulAut.conj a '' X = id '' X := by
      apply Set.image_congr
      intro x hx
      have hc := (mem_centralizer_iff.mp (hA.symm ▸ ha) x (hX hx)).symm
      simp only [MulAut.conj_apply, hc, mul_inv_cancel_right, id_eq]
    _ = X := Set.image_id _

/-- Source 39.6(3) for arbitrary subsets of the literal A₁: ambient conjugate
subsets are conjugate under the actual ambient normalizer of A₁. -/
theorem plane_controls_set_fusion (hfusion : F.MathieuFusion)
    (X Y : Set G) (hX : X ⊆ F.plane) (hY : Y ⊆ F.plane)
    (g : G) (hg : MulAut.conj g '' X = Y) :
    ∃ n : planeNormalizer F, MulAut.conj (n : G) '' X = Y := by
  obtain ⟨n, hn, he⟩ := (sourceSylow F).weakly_closed_normalizer_controls_set_fusion
    F.plane (flag_le_sourceSylow F).2.2.1 (plane_weakly_closed F hfusion)
    X Y (abelian_normalizes_subsets F.plane (plane_centralizer_eq F) X hX)
    (abelian_normalizes_subsets F.plane (plane_centralizer_eq F) Y hY) g hg
  exact ⟨⟨n, hn⟩, he⟩

/-- Source 39.6(3) for arbitrary subsets of the literal A₂. -/
theorem threeSpace_controls_set_fusion (hfusion : F.MathieuFusion)
    (X Y : Set G) (hX : X ⊆ F.threeSpace) (hY : Y ⊆ F.threeSpace)
    (g : G) (hg : MulAut.conj g '' X = Y) :
    ∃ n : threeSpaceNormalizer F, MulAut.conj (n : G) '' X = Y := by
  obtain ⟨n, hn, he⟩ := (sourceSylow F).weakly_closed_normalizer_controls_set_fusion
    F.threeSpace (flag_le_sourceSylow F).2.2.2 (threeSpace_weakly_closed F hfusion)
    X Y (abelian_normalizes_subsets F.threeSpace (threeSpace_centralizer_eq F) X hX)
    (abelian_normalizes_subsets F.threeSpace (threeSpace_centralizer_eq F) Y hY) g hg
  exact ⟨⟨n, hn⟩, he⟩

/-- The first normalizer controls all element fusion in A₁, with the literal
ambient conjugation convention. -/
theorem plane_controls_fusion (hfusion : F.MathieuFusion)
    {x y : G} (hx : x ∈ F.plane) (hy : y ∈ F.plane) (hxy : IsConj x y) :
    ∃ n : planeNormalizer F, (n : G) * x * (n : G)⁻¹ = y := by
  obtain ⟨n, hn, he⟩ := (sourceSylow F).weakly_closed_normalizer_controls_centralizer_fusion
    F.plane (flag_le_sourceSylow F).2.2.1 (plane_weakly_closed F hfusion)
    ((plane_centralizer_eq F).symm ▸ hx) ((plane_centralizer_eq F).symm ▸ hy) hxy
  exact ⟨⟨n, hn⟩, he⟩

/-- The second normalizer controls all element fusion in A₂. -/
theorem threeSpace_controls_fusion (hfusion : F.MathieuFusion)
    {x y : G} (hx : x ∈ F.threeSpace) (hy : y ∈ F.threeSpace) (hxy : IsConj x y) :
    ∃ n : threeSpaceNormalizer F, (n : G) * x * (n : G)⁻¹ = y := by
  obtain ⟨n, hn, he⟩ := (sourceSylow F).weakly_closed_normalizer_controls_centralizer_fusion
    F.threeSpace (flag_le_sourceSylow F).2.2.2 (threeSpace_weakly_closed F hfusion)
    ((threeSpace_centralizer_eq F).symm ▸ hx) ((threeSpace_centralizer_eq F).symm ▸ hy) hxy
  exact ⟨⟨n, hn⟩, he⟩

/-- The ambient normalizer of A₁ controls conjugacy of z inside A₁. -/
theorem plane_fusion_control (hfusion : F.MathieuFusion)
    (a : G) (ha : a ∈ F.fusion F.plane) :
    ∃ n : planeNormalizer F, (n : G) * z * (n : G)⁻¹ = a :=
  plane_fusion_control_of_catalogue F (rectangleCatalogue F) hfusion a ha

/-- The ambient normalizer of A₂ controls conjugacy of z inside A₂. -/
theorem threeSpace_fusion_control (hfusion : F.MathieuFusion)
    (a : G) (ha : a ∈ F.fusion F.threeSpace) :
    ∃ n : threeSpaceNormalizer F, (n : G) * z * (n : G)⁻¹ = a :=
  threeSpace_fusion_control_of_catalogue F (rectangleCatalogue F) hfusion a ha

/-- The oriented first normalizer has point-centralizer intersection of index 21. -/
theorem plane_relative_index (hcounts : MathieuFusionOrientation F) :
    (centralizer ({z} : Set G)).relIndex (planeNormalizer F) = 21 :=
  plane_relative_index_of_catalogue F (rectangleCatalogue F) hcounts

/-- The oriented second normalizer has point-centralizer intersection of index 45. -/
theorem threeSpace_relative_index (hcounts : MathieuFusionOrientation F) :
    (centralizer ({z} : Set G)).relIndex (threeSpaceNormalizer F) = 45 :=
  threeSpace_relative_index_of_catalogue F (rectangleCatalogue F) hcounts

/-- The source fusion theorem now discharges the outstanding premise of the
obstruction to the incompatible legacy full-normalizer record. -/
theorem no_legacy_normalizer_data (hfusion : F.MathieuFusion) :
    ¬ Nonempty (NormalizerTypeConsequences F) :=
  no_legacy_data_of_catalogue F (rectangleCatalogue F) hfusion

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
