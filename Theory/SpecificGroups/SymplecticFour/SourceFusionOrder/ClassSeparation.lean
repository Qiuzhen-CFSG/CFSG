module
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.ClassPairs
public import Theory.SpecificGroups.SymplecticFour.Sylow.Normalizer
public import Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual.Standard
public import Theory.GroupTheory.WeakClosureSetFusion
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification

/-!
# Distinct pinned symplectic involution classes

Burnside fusion reduces fusion in the Sylow center to the Borel. Its
explicit root action preserves zero coordinates, separating the three
pinned support patterns. Semilinear classification shows that every
diagram-preserving automorphism preserves each pinned native class.

Source: Aschbacher--Smith F.4.27,35,43, printed pp.288--296 of
refs/quasithin.pdf. These are the irredundance inputs to the ambient
order comparison, with the original root and Sylow conventions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
open CentralRootGeometry
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem borel_zero_support (g : Sp F) (hg : g∈borel)
    (s t u v : F) (he : g*(theta s t).val*g⁻¹=(theta u v).val) :
    (s=0 → u=0) ∧ (t=0 → v=0) := by
  have hh : (theta
      (g.val (.inl 0) (.inl 0)^2*s)
      ((g.val (.inl 0) (.inl 0)*g.val (.inl 1) (.inl 1)-
        g.val (.inl 0) (.inl 1)*g.val (.inl 1) (.inl 0))*t)).val = (theta u v).val := by
    rw [theta_val,theta_val] at he ⊢
    rw [show g*(rootElement 0 s*rootElement 4 t)*g⁻¹=
      (g*rootElement 0 s*g⁻¹)*(g*rootElement 4 t*g⁻¹) by group,
      RootNormalizerResidual.point_conjugate g hg.1,
      RootNormalizerResidual.plane_conjugate g hg.2] at he
    exact he
  have hc := (element_eq_iff _ _ _ _ _ _ _ _).mp (Subtype.ext hh)
  constructor
  · intro hs; simpa [hs] using hc.2.1.symm
  · intro ht; simpa [ht] using hc.2.2.1.symm

/-- The three pinned central representatives are distinct native conjugacy classes. -/
theorem centralRepresentative_irredundant {m : ℕ} (hm : 0<m) (hF : Nat.card F=2^m)
    (i j : Fin 3) (hij : IsConj (centralRepresentative (F := F) i).val
      (centralRepresentative j).val) : i=j := by
  let U := unipotentSylow hF hm
  have hc (k : Fin 3) : (centralRepresentative (F := F) k).val∈
      centralizer (unipotent (F := F) : Set (Sp F)) := by
    intro x hx
    exact congrArg Subtype.val ((mem_center_iff.mp (centralRepresentative_center k)) ⟨x,hx⟩)
  have hw (g : Sp F) (hg : unipotent.map (MulAut.conj g).toMonoidHom≤unipotent) :
      g∈normalizer (unipotent (F := F) : Set (Sp F)) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact eq_of_le_of_card_ge hg (card_map_of_injective (MulAut.conj g).injective).ge
  obtain ⟨g,hg,he⟩ := U.weakly_closed_normalizer_controls_centralizer_fusion
    unipotent le_rfl hw (hc i) (hc j) hij
  have hgB : g∈borel := normalizer_unipotent_le_borel hg
  have hi : g⁻¹*(centralRepresentative j).val*(g⁻¹)⁻¹=(centralRepresentative i).val := by
    rw [←he]; group
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals first
    | exact False.elim (one_ne_zero ((borel_zero_support g hgB _ _ _ _ he).1 rfl))
    | exact False.elim (one_ne_zero ((borel_zero_support g hgB _ _ _ _ he).2 rfl))
    | exact False.elim (one_ne_zero ((borel_zero_support g⁻¹ (borel.inv_mem hgB) _ _ _ _ hi).1 rfl))
    | exact False.elim (one_ne_zero ((borel_zero_support g⁻¹ (borel.inv_mem hgB) _ _ _ _ hi).2 rfl))

/-- Diagram-preserving automorphisms send each pinned representative to its native class. -/
theorem centralRepresentative_automorphism_conjugate
    (a : MulAut (Sp F)) (ha : DiagramAutomorphisms.PreservesDiagram a) (i : Fin 3) :
    IsConj (centralRepresentative (F := F) i).val (a (centralRepresentative i).val) := by
  obtain ⟨g,σ,rfl⟩ := DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram a ha
  have hf : DiagramAutomorphisms.fieldAutomorphism σ (centralRepresentative i).val=
      (centralRepresentative i).val := by
    fin_cases i <;> simp [centralRepresentative,theta_val,map_mul,
      DiagramAutomorphisms.ExceptionalGraph.fieldAutomorphism_root]
  refine isConj_iff.mpr ⟨g,?_⟩
  change g*(centralRepresentative i).val*g⁻¹=
    g*(DiagramAutomorphisms.fieldAutomorphism σ (centralRepresentative i).val)*g⁻¹
  rw [hf]
end Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
