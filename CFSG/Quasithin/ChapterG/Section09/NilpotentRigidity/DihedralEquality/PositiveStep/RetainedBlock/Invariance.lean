module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.BlockContracts
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.CentralizingActors
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.Restriction
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Invariance and fixation of the retained actors

The distinguished rotation subgroup is normal in the full dihedral product,
so both its fixed and displacement spaces are invariant before restricting
any operator. Each retained dihedral factor commutes with the faithful
classified action on the fixed space; the supplied centralizer theorem
therefore makes the entire retained product fix that space pointwise.

Source: Aschbacher--Smith G.9.2, printed pp.352--353.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.RetainedBlock
open DihedralDegree DihedralGroup
universe v
variable {ι : Type} [DecidableEq ι] {p : ι → ℕ}
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  (σ : Representation (ZMod 2) (∀ i, DihedralGroup (p i)) W) (i : ι)

private theorem rotation_normal : (Subgroup.zpowers (Pi.mulSingle i (r (1 : ZMod (p i))) : ∀ j, DihedralGroup (p j))).Normal := by
  constructor
  intro x hx g
  obtain ⟨k, rfl⟩ := hx
  have he : g * Pi.mulSingle i (r (1 : ZMod (p i))) ^ k * g⁻¹ =
      Pi.mulSingle i (g i * r (k : ZMod (p i)) * (g i)⁻¹) := by
    ext j
    by_cases hj : j = i
    · subst j; simp [r_zpow]
    · simp [Pi.mulSingle_eq_of_ne hj]
  rw [he]
  cases hg : g i with
  | r a =>
    have he : r a * r (k : ZMod (p i)) * (r a)⁻¹ = r (k : ZMod (p i)) := by
      simp
    rw [he]
    exact ⟨k, by simp [← Pi.mulSingle_zpow, r_zpow]⟩
  | sr a =>
    have he : sr a * r (k : ZMod (p i)) * (sr a)⁻¹ = r (-k : ZMod (p i)) := by
      simp
    rw [he]
    exact ⟨-k, by simp only [← Pi.mulSingle_zpow, r_zpow, one_mul, Int.cast_neg]⟩

private theorem fixed_eq_invariants : rotationFixed (factorRep σ i) =
    Representation.invariants (σ.comp (Subgroup.zpowers (Pi.mulSingle i (r 1))).subtype) := by
  let x : ∀ j, DihedralGroup (p j) := Pi.mulSingle i (r (1 : ZMod (p i)))
  let R := Subgroup.zpowers x
  let y : R := ⟨x, Subgroup.mem_zpowers x⟩
  have hg : ∀ g : R, g ∈ Subgroup.zpowers y := by
    rintro ⟨g, ⟨n, rfl⟩⟩
    exact ⟨n, rfl⟩
  ext w
  exact (mem_rotationFixed (factorRep σ i) w).trans
    (Representation.mem_invariants_iff_of_forall_mem_zpowers
      (ρ := σ.comp R.subtype) y hg w).symm

theorem fixed_stable (g : ∀ j, DihedralGroup (p j)) :
    rotationFixed (factorRep σ i) ≤ (rotationFixed (factorRep σ i)).comap (σ g) := by
  let := rotation_normal (p := p) i
  rw [fixed_eq_invariants]
  exact Representation.le_comap_invariants σ _ g

private theorem moved_eq : rotationMoved (factorRep σ i) =
    movedSpace σ (Subgroup.zpowers (Pi.mulSingle i (r 1))) := by
  have h := movedSpace_map σ (MonoidHom.mulSingle (fun j => DihedralGroup (p j)) i)
    (Subgroup.zpowers (r 1))
  rw [MonoidHom.map_zpowers] at h
  exact h.symm

theorem moved_stable (g : ∀ j, DihedralGroup (p j)) :
    rotationMoved (factorRep σ i) ≤ (rotationMoved (factorRep σ i)).comap (σ g) := by
  let := rotation_normal (p := p) i
  rw [moved_eq]
  exact Representation.Coinvariants.le_comap_ker σ _ g

theorem subproduct_injective (S : Finset ι) :
    Function.Injective (subproductHom (p := p) S) := by
  intro g h he
  funext j
  have he' := congrFun he j.val
  simpa [subproductHom, j.property] using he'

theorem subproducts_commute (S T : Finset ι) (h : Disjoint S T)
    (g : ∀ j : S, DihedralGroup (p j)) (k : ∀ j : T, DihedralGroup (p j)) :
    Commute (subproductHom S g) (subproductHom T k) := by
  change _ * _ = _ * _
  ext j
  have hh := Finset.disjoint_left.mp h
  by_cases hj : j ∈ S
  · simp [subproductHom, hj, show j ∉ T from fun ht => hh hj ht]
  · simp [subproductHom, hj]

variable [Fintype ι] [FiniteDimensional (ZMod 2) W]

theorem retained_fixes_fixed
    (centralizer : ClassifiedInvolutionCentralizerTheorem.{0,v})
    {exceptional : Prop} (s : PreparedSplit σ i exceptional)
    (g : ∀ j : s.retainedIndices, DihedralGroup (p j))
    (w : rotationFixed (factorRep σ i)) : σ (subproductHom s.retainedIndices g) w = (w : W) := by
  let C := rotationFixed (factorRep σ i)
  let I := s.fixedIndices
  let R := s.retainedIndices
  let μ := σ.subrepresentation C (fixed_stable σ i)
  let τ := Representation.subrepresentation (σ.comp (subproductHom I)) C s.actions.fixed_stable
  have hIR : Disjoint I R := by
    apply Finset.disjoint_left.mpr
    intro j hjI hjR
    have hjI' := Finset.mem_sdiff.mp hjI
    rcases Finset.mem_insert.mp hjR with rfl | hj
    · exact (Finset.mem_erase.mp hjI'.1).1 rfl
    · exact hjI'.2 hj
  have hsingle (j : R) (x : DihedralGroup (p j)) :
      μ (subproductHom R (Pi.mulSingle j x)) = 1 := by
    have hjI : j.val ∉ I := fun hj => Finset.disjoint_left.mp hIR hj j.property
    let υ := μ.comp (MonoidHom.mulSingle (fun j => DihedralGroup (p j)) j.val)
    have hcomm : ∀ x (g : (⊤ : Subgroup (∀ j : I, DihedralGroup (p j)))),
        Commute (υ x) (τ g) := by
      intro x g
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      exact congrArg (fun f : Module.End (ZMod 2) W => f w)
        (((subproduct_commutes I j.val hjI g.val x).map σ).symm.eq)
    have hfaith : Function.Injective (τ.comp (⊤ : Subgroup _).subtype) :=
      s.actions.fixed_faithful.comp Subtype.val_injective
    have hh := dihedral_fixes_classified centralizer τ ⊤ exceptional
      s.fixed_classification hfaith υ hcomm x
    change μ (Pi.mulSingle j.val x) = 1 at hh
    simpa only [subproductHom_single] using hh
  have hk : g ∈ (μ.comp (subproductHom R)).ker := by
    apply Subgroup.pi_mem_of_mulSingle_mem
    intro j
    exact hsingle j (g j)
  exact congrArg Subtype.val (congrArg (fun f : Module.End (ZMod 2) C => f w) hk)

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.RetainedBlock
