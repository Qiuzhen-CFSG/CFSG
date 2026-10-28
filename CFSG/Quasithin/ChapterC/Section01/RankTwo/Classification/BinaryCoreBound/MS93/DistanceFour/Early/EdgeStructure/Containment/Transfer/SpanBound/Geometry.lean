module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.Transfer.Span

/-!
# The kernel branches of the MS93 neighboring span argument

Equal kernels have the same omega-center Z, so their edge displacements
agree. Unequal kernels act nontrivially on the marked natural subgroup:
otherwise its exact centralizer and the equal finite kernel orders identify
the kernels. Every neighboring displacement centralizes its own kernel,
and the source B-containment gives the literal local commutator condition.

The last theorem assembles the two still-conditional unequal-kernel steps.
It is not the source span bound: the extension realization and edge-action
sharpening must both be proved from the source inputs.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), first paragraph of the proof of (4.2)(i), printed p.882.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.Transfer.SpanBound
variable {M : Type*} [Group M] {R : Subgroup M}

/-- Neighbors of the same holomorph vertex have the same M-color. -/
theorem neighbor_color (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b) : color R d = false := by
  have h₁ := adjacent_color_ne R hab
  have h₂ := adjacent_color_ne R hdb
  cases hb : color R b <;> cases hd : color R d <;> simp_all

/-- The neighboring kernel acts inside the original local stabilizer. -/
theorem neighbor_kernel_le_stabilizer [Finite M]
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b) :
    Q R d ≤ stabilizer R a := by
  have hb : color R b = true := by
    have h := adjacent_color_ne R hab
    cases hc : color R b <;> simp_all
  exact (Q_le_adjacent_h R hb hdb).trans (fun _ hx => hx.2 a (adjacent_symm R hab))

variable [Finite M] {L : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R} (common : CommonFacts R source geometry)

include common
omit [Finite M] in
/-- Equal kernels identify the actual omega-center layers, hence their edge displacements. -/
theorem displacement_eq_of_kernel_eq (a b d : Vertex R)
    (ha : color R a = false) (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (heq : Q R a = Q R d) : ⁅Z R d, Q R b⁆ = ⁅Z R a, Q R b⁆ := by
  have hd := neighbor_color a b d ha hab hdb
  have hZ : Z R d = Z R a := by
    rw [← common.X_eq_Z d hd, ← common.X_eq_Z a ha, X, X, heq]
  rw [hZ]

/-- An unequal neighboring kernel acts nontrivially on the marked natural group.
Local finiteness and the equal orders of transported kernels are essential. -/
theorem neighbor_kernel_not_centralizes (a b d : Vertex R)
    (ha : color R a = false) (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hne : Q R a ≠ Q R d) :
    ¬ Q R d ≤ centralizer (U R a : Set (FreeAmalgam R)) := by
  intro hc
  have hd := neighbor_color a b d ha hab hdb
  have hle : Q R d ≤ Q R a := by
    rw [← common.natural.centralizer a ha]
    exact le_inf (neighbor_kernel_le_stabilizer a b d ha hab hdb) hc
  let := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1))
    (inclusion_injective _)
  exact hne (eq_of_le_of_card_ge hle
    (by rw [source.Q_card a ha, source.Q_card d hd])).symm

/-- Every neighboring displacement is fixed by its own kernel. -/
theorem neighbor_displacement_centralizes (a b d : Vertex R)
    (ha : color R a = false) (hab : Adjacent R a b) (hdb : Adjacent R d b) :
    ⁅Z R d, Q R b⁆ ≤ centralizer (Q R d : Set (FreeAmalgam R)) := by
  have hd := neighbor_color a b d ha hab hdb
  exact ((edge_commutator_le_natural common d b hd hdb).trans (U_le_Z d)).trans
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hd))

omit [Finite M] in
/-- The given B-containment supplies the local kernel containment and the
literal commutator condition needed for the extension argument. -/
theorem neighbor_displacement_local (a b d : Vertex R)
    (ha : color R a = false)
    (hB : ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    ⁅Z R d, Q R b⁆ ≤ Q R a ∧ ⁅⁅Z R d, Q R b⁆, Ltilde R a⁆ ≤ Z R a := by
  refine ⟨hB.trans ((B_le_radius common a ha).trans (radius_le_Q common a ha)), ?_⟩
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl x hx
  exact ((mem_B_iff R a (geometry.Z_normal a)
    ((radius_le_Q common a ha).trans (fun _ hv => hv.1)) x).mp (hB hx)).2 l hl

omit [Finite M] in
/-- Assembly of the two unequal-kernel steps, with the equal-kernel case
proved here. The two premises must still be supplied from the source inputs. -/
theorem edgeSpan_le_of_neighbor_steps (a b : Vertex R)
    (ha : color R a = false) (hab : Adjacent R a b)
    (hB : ∀ d, Adjacent R d b → ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a))
    (hext : ∀ d, Adjacent R d b → Q R a ≠ Q R d →
      ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a) →
      ⁅Z R d, Q R b⁆ ≤ U R a ⊔ fixedCore R a)
    (hsharp : ∀ d, Adjacent R d b → Q R a ≠ Q R d →
      ⁅Z R d, Q R b⁆ ≤ U R a ⊔ fixedCore R a →
      ⁅Z R d, Q R b⁆ ≤ ⁅Z R a, Q R b⁆ ⊔ fixedCore R a) :
    edgeSpan R b ≤ ⁅Z R a, Q R b⁆ ⊔ fixedCore R a := by
  apply iSup_le
  intro d
  apply iSup_le
  intro hd
  by_cases heq : Q R a = Q R d
  · rw [displacement_eq_of_kernel_eq common a b d ha hab hd heq]
    exact le_sup_left
  · exact hsharp d hd heq (hext d hd heq (hB d hd))
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.Transfer.SpanBound
