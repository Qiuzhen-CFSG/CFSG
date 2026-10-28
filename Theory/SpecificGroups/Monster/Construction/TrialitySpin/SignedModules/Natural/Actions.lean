module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Natural.Coordinates

/-!
# Computed Parker actions on the natural signed modules

The restrictions of the actual `psi` permutations to the three axes are loop
translations or inverse sandwiches. Their code coordinates give exactly the
sign changes of Lemma 27.4(1). The actual `psiAut` formulas act by a marked
coordinate permutation; inversion has no effect on code coordinates, while
odd parity determines the target axis. This proves the halfspace and linear
formulas of 27.4(2)–(3) from the coordinate witness of a standard automorphism.

The all-ones word of `sπ` complements first-axis halfspaces under `psi2`, so
its induced action is minus identity. The element `z1` fixes those halfspaces
and acts trivially. These conclusions apply to every induced group action
with the indicated actual ambient permutations.

Source: Aschbacher, *Sporadic Groups*, Lemma 27.4(1)–(3) and Lemma 27.5(4),
printed pp. 146–147 (PDF page 79); the defining permutations are in Section 14.
-/

@[expose] public section
noncomputable section
open Atlas.Fischer Atlas.Codes
namespace Sporadic.Monster.Construction.TrialitySpin.SignedModules.Natural

/-- A bijection on an actual axis, with its computed coordinate effect, transports halfspaces. -/
theorem image_halfspace_of_loop {i j : Axis} (g : Equiv.Perm Triple)
    (e : Equiv.Perm ParkerLoop) (he : ∀ d, g (point i d) = point j (e d))
    (x y : Omega) (c ε : ParkerBit)
    (hc : ∀ d, (e d).1.val y = d.1.val x + c) :
    g '' halfspace i (x, ε) = halfspace j (y, ε + c) := by
  ext a
  constructor
  · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    rw [he, point_mem_halfspace, hc]
    exact congrArg (· + c) hd
  · rintro ⟨b, hb, rfl⟩
    refine ⟨point i (e.symm b), ?_, by rw [he, e.apply_symm_apply]⟩
    rw [point_mem_halfspace]
    have h := hc (e.symm b)
    rw [e.apply_symm_apply] at h
    exact add_right_cancel (h.symm.trans hb)

/-- The three actual loop generators, indexed in the same order as the axes. -/
def psiAt : Axis → ParkerLoop → Equiv.Perm Triple
  | 0 => psi1
  | 1 => psi2
  | 2 => psi3

private def loopAction : Axis → Axis → ParkerLoop → Equiv.Perm ParkerLoop
  | 0, 0, d => (loopLeft (loopInverse d)).trans (loopRight (loopInverse d))
  | 0, 1, d => loopLeft d
  | 0, 2, d => loopRight d
  | 1, 0, d => loopRight d
  | 1, 1, d => (loopLeft (loopInverse d)).trans (loopRight (loopInverse d))
  | 1, 2, d => loopLeft d
  | 2, 0, d => loopLeft d
  | 2, 1, d => loopRight d
  | 2, 2, d => (loopLeft (loopInverse d)).trans (loopRight (loopInverse d))

private theorem psiAt_point (i j : Axis) (d b : ParkerLoop) :
    psiAt i d (point j b) = point j (loopAction i j d b) := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem loopAction_coordinate (i j : Axis) (d b : ParkerLoop) (x : Omega) :
    (loopAction i j d b).1.val x = b.1.val x + if i = j then 0 else d.1.val x := by
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact add_comm (d.1.val x) (b.1.val x)
    | change (d.1.val x + b.1.val x) + d.1.val x = b.1.val x + 0
      calc
        (d.1.val x + b.1.val x) + d.1.val x = b.1.val x + (d.1.val x + d.1.val x) := by ac_rfl
        _ = b.1.val x + 0 := by simp

/-- Source 27.4(1), on all three genuine coordinate-halfspace families. -/
theorem psi_halfspace (i j : Axis) (d : ParkerLoop) (x : Omega) (ε : ParkerBit) :
    psiAt i d '' halfspace j (x, ε) =
      halfspace j (x, ε + if i = j then 0 else d.1.val x) :=
  image_halfspace_of_loop (psiAt i d) (loopAction i j d) (psiAt_point i j d)
    x x _ ε (fun b => loopAction_coordinate i j d b x)

theorem psi_carries (i j : Axis) (d : ParkerLoop) : Carries j j (psiAt i d) := by
  rintro ⟨x, ε⟩
  exact ⟨_, psi_halfspace i j d x ε⟩

theorem psi_linear (i j : Axis) (d : ParkerLoop) (x : Omega) (ε : ParkerBit) :
    transport (psiAt i d) (psi_carries i j d) (L j ε x) =
      L j (ε + if i = j then 0 else d.1.val x) x := by
  rw [transport_L, labelEquiv_of_image _ _ _ _ (psi_halfspace i j d x ε)]

/-- The automorphism permutations in their source order. -/
def psiAutAt : Axis → Equiv.Perm ParkerLoop → Equiv.Perm Triple
  | 0 => psiAut1
  | 1 => psiAut2
  | 2 => psiAut3

/-- An odd `ψᵢ(α)` fixes axis `i` and interchanges the other two. -/
def oddAxis : Axis → Axis → Axis
  | 0, 0 => 0
  | 0, 1 => 2
  | 0, 2 => 1
  | 1, 0 => 2
  | 1, 1 => 1
  | 1, 2 => 0
  | 2, 0 => 1
  | 2, 1 => 0
  | 2, 2 => 2

def autTarget (i : Axis) (e : Equiv.Perm ParkerLoop) (j : Axis) : Axis :=
  if e parkerOmega = parkerOmega then j else oddAxis i j

private def autLoop (e : Equiv.Perm ParkerLoop) : Equiv.Perm ParkerLoop :=
  if e parkerOmega = parkerOmega then e else loopInverseEquiv.trans e

private theorem psiAutAt_point (i j : Axis) (e : Equiv.Perm ParkerLoop) (b : ParkerLoop) :
    psiAutAt i e (point j b) = point (autTarget i e j) (autLoop e b) := by
  fin_cases i <;> fin_cases j <;> by_cases h : e parkerOmega = parkerOmega
  all_goals simp [psiAutAt, point, autTarget, oddAxis, autLoop, psiAut1, psiAut2,
    psiAut3, h, axis1, axis2, axis3, diagonal, flip1, flip2, flip3, loopInverseEquiv]

/-- The marked coordinate permutation is used with forward coordinate `σ x`.
Loop inversion changes only the Parker sign and hence leaves these evaluations unchanged. -/
private theorem autLoop_coordinate (e : Equiv.Perm ParkerLoop) (σ : Equiv.Perm Omega)
    (hσ : ∀ d, (e d).1.val = coordinatePermutation σ d.1.val)
    (d : ParkerLoop) (x : Omega) : (autLoop e d).1.val (σ x) = d.1.val x := by
  by_cases h : e parkerOmega = parkerOmega
  · simp only [autLoop, if_pos h, hσ]
    change d.1.val (σ.symm (σ x)) = d.1.val x
    rw [σ.symm_apply_apply]
  · simp only [autLoop, if_neg h, Equiv.trans_apply, hσ]
    change d.1.val (σ.symm (σ x)) = d.1.val x
    rw [σ.symm_apply_apply]

/-- Source 27.4(2)–(3), with all source and target axes explicit. -/
theorem psiAut_halfspace (i j : Axis) (e : Equiv.Perm ParkerLoop) (σ : Equiv.Perm Omega)
    (hσ : ∀ d, (e d).1.val = coordinatePermutation σ d.1.val)
    (x : Omega) (ε : ParkerBit) :
    psiAutAt i e '' halfspace j (x, ε) = halfspace (autTarget i e j) (σ x, ε) := by
  simpa only [add_zero] using image_halfspace_of_loop (psiAutAt i e) (autLoop e)
    (psiAutAt_point i j e) x (σ x) 0 ε (fun d => by
      rw [add_zero]; exact autLoop_coordinate e σ hσ d x)

theorem psiAut_carries (i j : Axis) (e : Equiv.Perm ParkerLoop) (σ : Equiv.Perm Omega)
    (hσ : ∀ d, (e d).1.val = coordinatePermutation σ d.1.val) :
    Carries j (autTarget i e j) (psiAutAt i e) := by
  rintro ⟨x, ε⟩
  exact ⟨_, psiAut_halfspace i j e σ hσ x ε⟩

theorem psiAut_linear (i j : Axis) (e : Equiv.Perm ParkerLoop) (σ : Equiv.Perm Omega)
    (hσ : ∀ d, (e d).1.val = coordinatePermutation σ d.1.val)
    (x : Omega) (ε : ParkerBit) :
    transport (psiAutAt i e) (psiAut_carries i j e σ hσ) (L j ε x) =
      L (autTarget i e j) ε (σ x) := by
  rw [transport_L, labelEquiv_of_image _ _ _ _ (psiAut_halfspace i j e σ hσ x ε)]


/-- In particular, a loop generator fixes every halfspace on its own axis. -/
theorem psi_self_halfspace (i : Axis) (d : ParkerLoop) (l : Label) :
    psiAt i d '' halfspace i l = halfspace i l := by
  simpa using psi_halfspace i i d l.1 l.2

/-- On the other axes, its Golay coordinate toggles the halfspace sign. -/
theorem psi_other_halfspace (i j : Axis) (hij : i ≠ j) (d : ParkerLoop)
    (x : Omega) (ε : ParkerBit) :
    psiAt i d '' halfspace j (x, ε) = halfspace j (x, ε + d.1.val x) := by
  simpa only [if_neg hij] using psi_halfspace i j d x ε

theorem z1_halfspace (l : Label) : z1 '' halfspace 0 l = halfspace 0 l :=
  psi_self_halfspace 0 loopPi l

theorem z1_carries : Carries 0 0 z1 := psi_carries 0 0 loopPi

/-- The central sign `z1` is trivial on the first natural module. -/
theorem z1_transport : transport z1 z1_carries = LinearEquiv.refl ℝ B1_24 :=
  (transport_kernel_iff z1 z1_carries).2 z1_halfspace

/-- `sπ` has the all-ones Golay word: the second loop generator complements
all first-axis halfspaces, regardless of the sign of the loop representative. -/
theorem psi2_signOmega_halfspace (l : Label) :
    psi2 (parkerSign 1 parkerOmega) '' halfspace 0 l = halfspace 0 (signs.flip l) :=
  psi_other_halfspace 1 0 (by decide) (parkerSign 1 parkerOmega) l.1 l.2

theorem psi2_signOmega_carries : Carries 0 0 (psi2 (parkerSign 1 parkerOmega)) :=
  psi_carries 1 0 (parkerSign 1 parkerOmega)

/-- Complementing every halfspace acts as minus identity on signed functions. -/
theorem transport_neg_of_complements {i : Axis} (g : Equiv.Perm Triple) (hg : Carries i i g)
    (hc : ∀ l, g '' halfspace i l = halfspace i (signs.flip l)) (v : Space i) :
    transport g hg v = -v := by
  have he : labelEquiv g hg = signs.flip := by
    apply Equiv.ext
    intro l
    exact labelEquiv_of_image g hg l (signs.flip l) (hc l)
  have ht : transport g hg = signs.transport signs signs.flip (fun _ => rfl) := by
    ext w l
    change w.val ((labelEquiv g hg).symm l) = w.val (signs.flip.symm l)
    rw [he]
  rw [ht, signs.flip_transport]

/-- Source 27.5(4), on the first natural factor. -/
theorem psi2_signOmega_transport (v : B1_24) :
    transport (psi2 (parkerSign 1 parkerOmega)) psi2_signOmega_carries v = -v :=
  transport_neg_of_complements _ _ psi2_signOmega_halfspace v

theorem representation_of_z1 {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm Triple) (hρ : ∀ g, Carries 0 0 (ρ g))
    (g : G) (hg : ρ g = z1) : representation ρ hρ g = 1 := by
  apply (representation_kernel_iff ρ hρ g).2
  intro l
  rw [hg]
  exact z1_halfspace l

theorem representation_of_psi2_signOmega {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm Triple) (hρ : ∀ g, Carries 0 0 (ρ g))
    (g : G) (hg : ρ g = psi2 (parkerSign 1 parkerOmega)) (v : B1_24) :
    representation ρ hρ g v = -v := by
  apply transport_neg_of_complements (ρ g) (hρ g) _ v
  intro l
  rw [hg]
  exact psi2_signOmega_halfspace l

end Sporadic.Monster.Construction.TrialitySpin.SignedModules.Natural
