module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Source

/-!
# The actual vertices of the generated A₃ system

Restrict the three source vertices to their generated group and retain the
literal family equation. This equation is needed to transfer the nonzero
chosen module into the point core; a bare existence statement for a D-system
would lose that marking. Quotients and parabolics use the existing restriction
maps, and ambient uniqueness supplies the core-free chamber.

Source: Aschbacher--Smith, 14.4.13, printed p.1012.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open LargerDimension LargerDimension.LocalAction LargerDimension.IntrinsicSource
variable {G : Type*} [Group G] [Finite G]

structure MarkedSystem (L T L₁ L₂ X : Subgroup G) where
  system : Quasithin.I5.DSystem .A3 (actualG0 L T L₁ L₂ X)
  vertex_eq : ∀ i, system.family i =
    (sourceVertex L T L₁ L₂ X i).subgroupOf (actualG0 L T L₁ L₂ X)

omit [Finite G] in
private theorem chamber_eq (A B C T : Subgroup G) (hTA : T ≤ A)
    (h : Quasithin.I5.RankTwoParabolics A (T.subgroupOf A)
      (B.subgroupOf A) (C.subgroupOf A)) :
    Quasithin.I5.chamberSubgroup ![A, B, C] = T := by
  ext x
  simp only [Quasithin.I5.chamberSubgroup, mem_iInf, Fin.forall_fin_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.forall_fin_zero, and_true]
  constructor
  · rintro ⟨ha, hb, hc⟩
    have hx : (⟨x, ha⟩ : A) ∈ B.subgroupOf A ⊓ C.subgroupOf A := ⟨hb, hc⟩
    rw [h.borel_eq] at hx
    exact hx
  · intro ht
    have hx : (⟨x, hTA ht⟩ : A) ∈ B.subgroupOf A ⊓ C.subgroupOf A := by
      rw [h.borel_eq]; exact ht
    exact ⟨hTA ht, hx.1, hx.2⟩

/-- Literal vertex restriction, with the family equation retained as an output.
The input geometry supplies intersections and parabolics, not incidence facts. -/
noncomputable def markedSystem_of_source_geometry
    (L L₁ L₂ X M : Subgroup G) (T : Sylow 2 G)
    (a : SourceGeometry L L₁ L₂ X M T)
    (hq₁ : Nonempty (coreQuotient (L ⊔ (T : Subgroup G)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)))
    (hq₂ : Nonempty (coreQuotient (L₁ ⊔ X ⊔ (T : Subgroup G)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hq₃ : Nonempty (coreQuotient (localJoin L₂ X ⊔ (T : Subgroup G)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)))
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → L ⊔ (T : Subgroup G) ≤ K → K = M)
    (hM : M ≤ normalizer (L : Set G)) : MarkedSystem L T L₁ L₂ X := by
  let K := actualG0 L T L₁ L₂ X
  let F := sourceVertex L T L₁ L₂ X
  let F₀ : Fin 3 → Subgroup K := fun i => (F i).subgroupOf K
  have hch : Quasithin.I5.chamberSubgroup F = (T : Subgroup G) :=
    chamber_eq _ _ _ _ le_sup_right a.parabolics₁
  have hch₀ : Quasithin.I5.chamberSubgroup F₀ = (T : Subgroup G).subgroupOf K := by
    change (⨅ i, (F i).comap K.subtype) = ((T : Subgroup G).comap K.subtype)
    rw [← comap_iInf]
    exact congrArg (fun A : Subgroup G => A.subgroupOf K) hch
  have hs (i : Fin 3) : ∃ S : Sylow 2 (F i),
      (S : Subgroup (F i)) = (T : Subgroup G).subgroupOf (F i) := by
    have ht : (T : Subgroup G) ≤ F i := by fin_cases i <;> exact le_sup_right
    exact ⟨T.subtype ht, rfl⟩
  obtain ⟨q₁, s₁, p₁⟩ := source_vertex_restriction L T L₁ L₂ X (F 1) (F 2) 0
    _ hq₁ (hs 0) a.parabolics₁
  obtain ⟨q₂, s₂, p₂⟩ := source_vertex_restriction L T L₁ L₂ X (F 0) (F 2) 1
    _ hq₂ (hs 1) a.parabolics₂
  obtain ⟨q₃, s₃, p₃⟩ := source_vertex_restriction L T L₁ L₂ X (F 0) (F 1) 2
    _ hq₃ (hs 2) a.parabolics₃
  refine ⟨{
    family := F₀
    finite_vertex := fun _ => inferInstance
    point_A3 := fun _ => q₁
    point_C3 := by simp
    line_quotient := q₂
    plane_quotient := q₃
    sylow := ?_
    point_parabolics := ?_
    line_parabolics := ?_
    plane_parabolics := ?_
    generate := ?_
    core_free := ?_
    nondegenerate := by simp }, fun _ => rfl⟩
  · intro i
    rw [hch₀]
    fin_cases i
    · exact s₁
    · exact s₂
    · exact s₃
  · rw [hch₀]; exact p₁
  · rw [hch₀]; exact p₂
  · rw [hch₀]; exact p₃
  · simpa [F₀, F, sourceVertex] using source_vertices_generate_actualG0 L T L₁ L₂ X
  · rw [hch₀]
    exact source_intrinsic_core_free_of_residual_normalizer L T L₁ L₂ X M
      hunique hM a.residual a.normalizer_eq.le a.parabolic_le_M a.proper_maximal T.isPGroup'

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
