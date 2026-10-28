module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.CentralPlacement
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement.OvergroupGeometry
public import Theory.GroupTheory.SylowOvergroupIncidence

/-!
# The actual Borel overgroup under a moving Sylow actor

Proper-Sylow-overgroup geometry and Sylow fusion put every proper overgroup
inside one of the two literal parabolics. A moving actor exchanges them, so
an invariant proper Borel overgroup is Borel. Source: E.2.2, pp.215–216.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.TwoConjugate
open DiagramAutomorphisms
variable {F:Type*} [Field F] [Finite F] [CharP F 2]

/-- A proper subgroup containing the standard Sylow lies in one of its two
literal parabolics, without independent conjugators. -/
theorem proper_unipotent_overgroup_le_parabolic {n:ℕ} (hF:Nat.card F=2^n) (hn:1≤n)
    (D:Subgroup (Sp F)) (hUD:unipotent≤D) (hD:D≠⊤) :
    D≤pointParabolic ∨ D≤planeParabolic := by
  obtain ⟨g,hg⟩:=ThreeResidualPlacement.proper_unipotent_overgroup_parabolic_cover D hUD hD
  have unrotate (P:Subgroup (Sp F)) (hUP:unipotent≤P)
      (hBP:borel≤P) (hDP:D.map (MulAut.conj g).toMonoidHom≤P) : D≤P := by
    have hDP':D≤P.map (MulAut.conj g⁻¹).toMonoidHom := by
      intro x hx
      refine ⟨MulAut.conj g x,hDP (mem_map_of_mem _ hx),?_⟩
      change g⁻¹*(g*x*g⁻¹)*(g⁻¹)⁻¹=x
      group
    have he: P.map (MulAut.conj g⁻¹).toMonoidHom=P :=
      (unipotentSylow hF hn).conjugate_overgroup_eq_of_normalizer_le P hUP
        (by change normalizer (unipotent (F:=F):Set (Sp F))≤_; rw [←borel_eq_normalizer_unipotent]
            exact hBP.trans P.le_normalizer) g⁻¹ (hUD.trans hDP')
    rwa [he] at hDP'
  rcases hg with hg|hg
  · exact Or.inl (unrotate _ (unipotent_le_borel.trans inf_le_left) inf_le_left hg)
  · exact Or.inr (unrotate _ (unipotent_le_borel.trans inf_le_right) inf_le_right hg)

/-- The actual moving actor exchanges both whole parabolics. -/
theorem moving_swaps_parabolics {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (a:MulAut (Sp F)) (hU:unipotent.map a.toMonoidHom=unipotent)
    (ha:¬PreservesDiagram a) :
    pointParabolic.map a.toMonoidHom=planeParabolic ∧
      planeParabolic.map a.toMonoidHom=pointParabolic := by
  obtain ⟨hp,hq⟩:=moving_swaps_radicals hF hn a hU ha
  constructor
  · rw [←pointRadicalAmbient_normalizer hF hn, map_equiv_normalizer_eq,hp,
      planeRadicalAmbient_normalizer hF hn]
  · rw [←planeRadicalAmbient_normalizer hF hn, map_equiv_normalizer_eq,hq,
      pointRadicalAmbient_normalizer hF hn]

/-- A proper Borel overgroup invariant under a moving Sylow actor is Borel. -/
theorem eq_borel_of_moving_actor {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (a:MulAut (Sp F)) (hU:unipotent.map a.toMonoidHom=unipotent)
    (ha:¬PreservesDiagram a) (D:Subgroup (Sp F)) (hBD:borel≤D)
    (hD:D≠⊤) (hDa:D.map a.toMonoidHom=D) : D=borel := by
  obtain ⟨hp,hq⟩:=moving_swaps_parabolics hF hn a hU ha
  apply le_antisymm _ hBD
  change D≤pointParabolic⊓planeParabolic
  obtain h|h:=proper_unipotent_overgroup_le_parabolic hF hn.le D (unipotent_le_borel.trans hBD) hD
  · have hm:=map_mono (f:=a.toMonoidHom) h
    rw [hDa,hp] at hm
    exact le_inf h hm
  · have hm:=map_mono (f:=a.toMonoidHom) h
    rw [hDa,hq] at hm
    exact le_inf hm h

end Theory.SpecificGroups.SymplecticFour.TwoConjugate
