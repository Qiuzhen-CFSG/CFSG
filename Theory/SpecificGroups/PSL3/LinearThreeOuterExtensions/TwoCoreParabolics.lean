module
public import Theory.SpecificGroups.PSL3.CartanActions.FullTorusFixer
public import Theory.SpecificGroups.PSL3Even.MinimalParabolicWitness.Diagram
public import Theory.GroupTheory.PCoreRestriction

/-!
# The overlap two-core on the two linear parabolics

For a normal PSL₃(2ⁿ) section with a marked Borel overlap, commutators
of the overlap two-core with the Borel lie in its unipotent radical.
Thus these actors fix the full projective torus quotient. For n > 1,
the graph-field calculation excludes diagram movement unless n = 2.
The literal Sylow incidence theorem then fixes each whole parabolic.

The field-four exception is retained: its projective torus alone cannot
exclude a graph-field actor. The covering center is addressed separately
by the source assembly. Source: Aschbacher–Smith 5.1.11(3), 5.2.1,
printed pp.635,646 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3.CartanActions
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {G : Type*} [Group G]

/-- Ambient conjugation expressed through the prescribed projective marking. -/
@[expose] def markedAction (N : Subgroup G) [N.Normal]
    (e : PSL(3,F) ≃* N) : G →* MulAut PSL(3,F) :=
  (MulAut.congr e.symm).toMonoidHom.comp
    (N.normalizerMonoidHom.comp
      ((MonoidHom.id G).codRestrict (normalizer (N : Set G))
        (fun g => normalizer_eq_top (H := N) ▸ mem_top g)))

omit [Finite F] [CharP F 2] in
/-- The marked action evaluates to the original ambient conjugation. -/
theorem markedAction_apply (N : Subgroup G) [N.Normal]
    (e : PSL(3,F) ≃* N) (g : G) (x : PSL(3,F)) :
    (e (markedAction N e g x)).val = g * (e x).val * g⁻¹ := by
  change (e (e.symm _)).val = _
  simp only [e.apply_symm_apply]
  rfl

omit [CharP F 2] in
/-- Every element of the marked overlap preserves the literal Borel. -/
theorem markedAction_preserves_borel (N M : Subgroup G) [N.Normal]
    (e : PSL(3,F) ≃* N)
    (hM : M.comap (N.subtype.comp e.toMonoidHom) = borel F)
    {g : G} (hg : g ∈ M) :
    (borel F).map (markedAction N e g).toMonoidHom = borel F := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    rw [←hM] at hx ⊢
    change (e (markedAction N e g x)).val ∈ M
    rw [markedAction_apply]
    exact M.mul_mem (M.mul_mem hg hx) (M.inv_mem hg)
  · rw [card_map_of_injective (markedAction N e g).injective]

/-- Away from field four, the overlap two-core preserves each whole parabolic. -/
theorem twoCore_normalizes_parabolic {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hn2 : n ≠ 2)
    (N M : Subgroup G) [N.Normal] (e : PSL(3,F) ≃* N)
    (hM : M.comap (N.subtype.comp e.toMonoidHom) = borel F) (i : Bool) :
    M.pCoreIn 2 ≤ normalizer ((RootPlaneGeometry.parabolic F i).map
      (N.subtype.comp e.toMonoidHom) : Set G) := by
  let f := N.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := N.subtype_injective.comp e.injective
  let j : borel F →* M :=
    (f.comp (borel F).subtype).codRestrict M (fun x => by
      change f x.val ∈ M
      exact (show x.val ∈ M.comap f from hM.symm ▸ x.property))
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (hf (congrArg (fun z : M => z.val) h))
  have hcore : (pCore 2 M).comap j ≤ pCore 2 (borel F) :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective j hj⟩
  rintro _ ⟨s,hs,rfl⟩
  let a := markedAction N e s.val
  have hB := markedAction_preserves_borel N M e hM s.property
  have hfix : ∀ x ∈ torus F, a x * x⁻¹ ∈ unipotent F := by
    intro x hx
    let t : borel F := ⟨x,torus_le_borel F hx⟩
    let b : borel F := ⟨a x,hB.le (mem_map_of_mem _ t.property)⟩
    have hb : b * t⁻¹ ∈ pCore 2 (borel F) := by
      apply hcore
      change j (b * t⁻¹) ∈ pCore 2 M
      have he : j (b * t⁻¹) = s * j t * s⁻¹ * (j t)⁻¹ := by
        apply Subtype.ext
        change f (a x * x⁻¹) = s.val * f x * s.val⁻¹ * (f x)⁻¹
        rw [map_mul,map_inv]
        exact congrArg (fun z => z * (f x)⁻¹) (markedAction_apply N e s.val x)
      rw [he]
      exact (commutator_le_left (pCore 2 M) ⊤)
        (commutator_mem_commutator hs (mem_top (j t)))
    rw [BorelQuotient.twoCore_eq F hF] at hb
    exact hb
  have hd : PreservesPointType F a ∧ PreservesLineType F a := by
    by_contra hh
    exact hn2 (FullTorusFixer.degree_eq_two_of_fixed_torus hF hn a hB hfix hh)
  have hk : diagramAction F (by omega : 0 < n) hF a = 1 := by
    change a ∈ (diagramAction F (by omega : 0 < n) hF).ker
    rw [diagramAction_ker]
    exact (mem_diagramTrivial_iff F a).mpr hd
  have hU := FullTorusFixer.map_unipotent_of_map_borel hF a hB
  have hp := Matrix.PSL3Even.MinimalParabolicWitness.map_parabolic_of_preserves_unipotent
    F (by omega : 0 < n) hF a hU i
  rw [hk] at hp
  apply mem_normalizer_iff_map_conj_eq.mpr
  calc
    _ = ((RootPlaneGeometry.parabolic F i).map a.toMonoidHom).map f := by
      rw [Subgroup.map_map,Subgroup.map_map]
      congr 1
      ext x
      exact (markedAction_apply N e s.val x).symm
    _ = _ := by rw [hp]; rfl
end Matrix.PSL3.LinearThree.OuterExtensions
