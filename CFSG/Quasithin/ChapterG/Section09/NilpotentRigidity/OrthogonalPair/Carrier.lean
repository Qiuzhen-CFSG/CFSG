/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Root formulas adapted from ATLAS, D2MatrixImage.lean.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.OrthogonalPair.MatrixModel

/-!
# The exact elementary carrier of the binary orthogonal pair

The four upper/lower root transformations of the two matrix factors are
explicit Siegel transformations. They generate the dihedral product, so its
image lies in the elementary subgroup. Conversely, finite binary coordinate
calculations express every Siegel transformation in the image. The same
coordinates show that the action kernel is trivial. This constructs an
actual multiplicative equivalence, with its natural action retained.

All finite checks use kernel reduction (`decide +kernel`). No full
orthogonal-group, commutator-group or order identification is assumed.
The root parameters agree with ATLAS
`Atlas/LinearGroups/Orthogonal/D2MatrixImage.lean`; the binary finite proofs
and marked dihedral-product construction are new here.
Source application: Aschbacher--Smith G.9.2, printed pp.352--353.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.BinaryD2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem kernel_check : ∀ g : Pair, (∀ x : Space, (pairHom g).val x = x) → g = 1 := by
  decide +kernel

theorem pairHom_injective : Function.Injective pairHom := by
  apply (injective_iff_map_eq_one pairHom).mpr
  intro g hg
  exact kernel_check g (fun x => by rw [hg]; rfl)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem siegel_preimage : ∀ u v : Space, formD 2 (ZMod 2) u = 0 →
    (formD 2 (ZMod 2)).polarBilin u v = 0 →
    ∃ g : Pair, ∀ x : Space, (pairHom g).val x = Quadratic.siegel (formD 2 (ZMod 2)) u v x := by
  decide +kernel


/-- The four standard generators generate the actual dihedral product. -/
theorem pair_induction (P : Pair → Prop)
    (h1 : P 1) (hr : P (DihedralGroup.r 1, 1)) (ha : P (DihedralGroup.sr 0, 1))
    (hs : P (1, DihedralGroup.r 1)) (hc : P (1, DihedralGroup.sr 0))
    (hmul : ∀ g h, P g → P h → P (g * h)) (g : Pair) : P g := by
  have hp {x : Pair} (hx : P x) (n : ℕ) : P (x ^ n) := by
    induction n with
    | zero => simpa using h1
    | succ n ih => simpa only [pow_succ] using hmul _ _ ih hx
  have hl (d : DihedralGroup 3) : P (d, 1) := by
    cases d with
    | r i => simpa using hp hr i.val
    | sr i => simpa using hmul _ _ ha (hp hr i.val)
  have hrt (d : DihedralGroup 3) : P (1, d) := by
    cases d with
    | r i => simpa using hp hs i.val
    | sr i => simpa using hmul _ _ hc (hp hs i.val)
  simpa using hmul _ _ (hl g.1) (hrt g.2)

/-- The four binary root transformations in the two matrix factors. -/
def rootActor : Fin 4 → Pair :=
  ![(DihedralGroup.sr 0, 1), (DihedralGroup.sr 1, 1),
    (1, DihedralGroup.sr 0), (1, DihedralGroup.sr 1)]

def rootDirection : Fin 4 → Space :=
  ![Pi.single (.inl 0) 1, Pi.single (.inr 0) 1,
    Pi.single (.inl 1) 1, Pi.single (.inl 0) 1]

def rootParameter : Fin 4 → Space :=
  ![Pi.single (.inl 1) 1, Pi.single (.inr 1) 1,
    Pi.single (.inr 0) 1, Pi.single (.inr 1) 1]

theorem root_singular : ∀ i, formD 2 (ZMod 2) (rootDirection i) = 0 := by decide +kernel

theorem root_perpendicular : ∀ i,
    (formD 2 (ZMod 2)).polarBilin (rootDirection i) (rootParameter i) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem root_action : ∀ i x,
    (pairHom (rootActor i)).val x =
      Quadratic.siegel (formD 2 (ZMod 2)) (rootDirection i) (rootParameter i) x := by
  decide +kernel

theorem root_mem_elementary (i : Fin 4) :
    pairHom (rootActor i) ∈ elementarySubgroup (formD 2 (ZMod 2)) := by
  have he : pairHom (rootActor i) = siegelElement (formD 2 (ZMod 2))
      (rootDirection i) (rootParameter i) (root_singular i) (root_perpendicular i) := by
    apply Subtype.ext
    exact LinearEquiv.ext (root_action i)
  rw [he]
  exact siegelElement_mem _ _ _ _ _

theorem pair_mem_elementary (g : Pair) :
    pairHom g ∈ elementarySubgroup (formD 2 (ZMod 2)) := by
  let H := elementarySubgroup (formD 2 (ZMod 2))
  have hmul (x y : Pair) (hx : pairHom x ∈ H) (hy : pairHom y ∈ H) :
      pairHom (x * y) ∈ H := by rw [map_mul]; exact H.mul_mem hx hy
  have h0 := root_mem_elementary 0
  have h1 := root_mem_elementary 1
  have h2 := root_mem_elementary 2
  have h3 := root_mem_elementary 3
  dsimp only [rootActor, Matrix.cons_val_zero, Matrix.cons_val_succ] at h0 h1 h2 h3
  apply pair_induction (fun g => pairHom g ∈ H) (by simp) ?_ h0 ?_ h2 hmul g
  · have he : ((DihedralGroup.r 1, 1) : Pair) =
        (DihedralGroup.sr 0, 1) * (DihedralGroup.sr 1, 1) := by decide
    rw [he]
    exact hmul _ _ h0 h1
  · have he : ((1, DihedralGroup.r 1) : Pair) =
        (1, DihedralGroup.sr 0) * (1, DihedralGroup.sr 1) := by decide
    rw [he]
    exact hmul _ _ h2 h3

/-- Equality with the exact Siegel-generated subgroup, in both directions. -/
theorem range_pairHom : pairHom.range = elementarySubgroup (formD 2 (ZMod 2)) := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact pair_mem_elementary g
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨u, v, hu, huv, rfl⟩
    obtain ⟨g, hg⟩ := siegel_preimage u v hu huv
    exact ⟨g, Subtype.ext (LinearEquiv.ext hg)⟩

/-- The genuine elementary split four-space carrier is the dihedral product. -/
def pairEquiv : Pair ≃* elementarySubgroup (formD 2 (ZMod 2)) :=
  (MonoidHom.ofInjective pairHom_injective).trans
    (MulEquiv.subgroupCongr range_pairHom)

@[simp] theorem pairEquiv_apply (g : Pair) (x : Space) :
    (pairEquiv g).val.val x = (pairHom g).val x := rfl

end ClassicalOrthogonal.BinaryD2
