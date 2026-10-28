module
public import Theory.GroupAction.NormalPChiefSeries.Linear
public import Theory.GroupTheory.NoncentralChiefRefinement.BinaryFlagSections

/-!
# Irreducible sections in an actual chief series

Pull a simple submodule of a quotient back to the original normal elementary
abelian group. Its two preimages form a chief interval. Refinement below and
above that interval puts it into an actual chief series on the original group.
The specified first-isomorphism coordinates retain the same ambient action.
This supplies the literal chief factor used for the essential quotient in
Aschbacher–Smith3.1.9(5), printed p.578.
-/

public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
namespace NoncentralChiefRefinement
open BinaryFlag
variable {H : Type*} [Group H] [Finite H]
 (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]

omit [IsElementaryAbelian 2 U] in
private theorem exists_series_containing {A B : NormalNode H}
    (hab : A ⋖ B) (hBU : B.val ≤ U) :
    ∃ s : SeriesOn U, ∃ i : Fin s.series.length,
      s.lower i = A ∧ s.upper i = B := by
  obtain ⟨s,hs0,hsl⟩ := exists_chiefSeries (⊥ : NormalNode H) A bot_le
  have hstep : s.last ⋖ B := hsl ▸ hab
  let s' : ChiefSeries H := s.snoc B hstep
  obtain ⟨t,ht0,htl⟩ := exists_chiefSeries B ⟨U,inferInstanceAs U.Normal⟩ hBU
  have hst : s'.last = t.head := (RelSeries.last_snoc s B hstep).trans ht0.symm
  let d : SeriesOn U := {
    series := s'.smash t hst
    head_eq := by simpa only [s',RelSeries.head_smash,RelSeries.head_snoc] using hs0
    last_eq := (RelSeries.last_smash hst).trans htl }
  refine ⟨d,(Fin.last s.length).castAdd t.length,?_,?_⟩
  · exact (RelSeries.smash_castAdd (p := s') (q := t) hst (Fin.last s.length)).trans
      ((RelSeries.snoc_castSucc s B hstep (Fin.last s.length)).trans hsl)
  · exact (RelSeries.smash_succ_castAdd (p := s') (q := t) hst (Fin.last s.length)).trans
      (RelSeries.last_snoc s B hstep)

private def baseMap : Map (⟨U,inferInstanceAs U.Normal⟩ : NormalNode H) (normalRepresentation U) where
  hom := {
    toFun := fun u => Multiplicative.ofAdd (Additive.ofMul u)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  equivariant _ _ := rfl

theorem SeriesOn.exists_irreducible_subquotient_coordinates
    (W : Subrepresentation (normalRepresentation U))
    (P : Subrepresentation W.quotientRepresentation) [Representation.IsIrreducible P.toRepresentation]
    (hn : ∃ h v, P.toRepresentation h v ≠ v) :
    ∃ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i ∧
      ∃ e : Additive (s.Factor i) ≃ₗ[ZMod 2] P.toSubmodule,
        ∀ h v, e (s.factorRepresentation i h v) = P.toRepresentation h (e v) := by
  let q := (baseMap U).onQuotient W
  have hq : Function.Surjective q.hom :=
    (baseMap U).onQuotient_surjective W (fun x => ⟨x.toAdd.toMul,rfl⟩)
  let c := q.submoduleCoordinates P hq
  have hc := c.covBy (q.preimage_mono bot_le) hn
  obtain ⟨s,i,hi,hj⟩ := exists_series_containing U hc (q.preimage_le P)
  let d : SectionCoordinates (s.lower i) (s.upper i) P.toRepresentation 1 := by
    rw [hi,hj]
    exact c
  have hnc : ¬ s.Central i := d.not_isCentral (by decide) hn
  let f : Additive (s.Factor i) ≃+ P.toSubmodule := {
    toFun := fun v => (d.equiv v.toMul).toAdd 0
    invFun := fun v => Additive.ofMul (d.equiv.symm (Multiplicative.ofAdd (fun _ => v)))
    left_inv := by
      intro v
      apply Additive.toMul.injective
      apply d.equiv.injective
      change d.equiv (d.equiv.symm (Multiplicative.ofAdd
        (fun _ => (d.equiv v.toMul).toAdd 0))) = d.equiv v.toMul
      rw [d.equiv.apply_symm_apply]
      apply Multiplicative.toAdd.injective
      funext j
      exact congrArg (d.equiv v.toMul).toAdd (Subsingleton.elim 0 j)
    right_inv := by intro v; exact congrArg (fun x => x.toAdd 0) (d.equiv.apply_symm_apply _)
    map_add' := by intro v w; exact congrArg (fun x => x.toAdd 0) (d.equiv.map_mul v.toMul w.toMul) }
  let e : Additive (s.Factor i) ≃ₗ[ZMod 2] P.toSubmodule :=
    { f with map_smul' := ZMod.map_smul f }
  exact ⟨s,i,hnc,e,fun h v => d.equivariant h v.toMul 0⟩
end NoncentralChiefRefinement
