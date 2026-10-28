module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.Quotients
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Spin

/-!
# The concrete first triality spin representation

The actual centralizer `N1` acts on the signed functions on the `k1`-orbits
of `A2 ∪ A3`. Axis preservation and commutation with both involutions follow
from the concrete permutation structure. The orbit-kernel theorem identifies
the kernel as `J`, and its restriction to `Q1` has kernel `⟨k1⟩`.

Source: Aschbacher, *Sporadic Groups*, Lemma 14.6 and Section 27,
printed pp. 62–63 and 146–147. The action preserves the normalized positive
form and is monomial in the actual signed-orbit basis.
-/

@[expose] public section
noncomputable section
open Atlas.Fischer
namespace Sporadic.Monster.Construction.TrialitySpin.SpinAction

def permutations : N1 →* Equiv.Perm Triple := N.subtype.comp N1.subtype

theorem preserves_axes (g : N1) (a : Triple) :
    a ∈ A ↔ permutations g a ∈ A := by
  constructor
  · exact fun h => N1_mapsTo_A g.val g.prop h
  · intro h
    have hh := N1_mapsTo_A g.val⁻¹ (N1.inv_mem g.prop) h
    change g.val.val.symm (g.val.val a) ∈ A at hh
    simpa only [Equiv.symm_apply_apply] using hh

theorem commutes_k1 (g : N1) (a : Triple) :
    permutations g (k1.val a) = k1.val (permutations g a) :=
  congrArg (fun p : N => p.val a) (N1_commute_k1 g.val g.prop).eq

theorem commutes_z1 (g : N1) (a : Triple) :
    permutations g (z1 a) = z1 (permutations g a) :=
  congrArg (fun p : N => p.val a)
    (Subgroup.mem_centralizer_singleton_iff.mp g.prop)

/-- The fixed 4096-dimensional representation, with all normalization proved. -/
def representation : Representation ℝ N1 SpinSpace :=
  bothAxesDomain.inducedRepresentation permutations preserves_axes commutes_k1 commutes_z1

theorem representation_eq_one_iff (g : N1) :
    representation g = 1 ↔ g.val ∈ J := by
  exact (bothAxesDomain.inducedRepresentation_kernel_iff permutations preserves_axes
    commutes_k1 commutes_z1 g).trans (N1_orbit_kernel g.val g.prop)

theorem representation_kernel : representation.ker = J.subgroupOf N1 := by
  ext g
  exact representation_eq_one_iff g

theorem representation_vector (g : N1) (a : A) :
    representation g (bothAxesDomain.vector a) =
      bothAxesDomain.vector ⟨g.val.val a.val, N1_mapsTo_A g.val g.prop a.prop⟩ :=
  bothAxesDomain.representation_vector (bothAxesDomain.restrictPermutations permutations preserves_axes)
    (fun g a => Subtype.ext (commutes_k1 g a.val))
    (fun g a => Subtype.ext (commutes_z1 g a.val)) g a

theorem representation_isometry (g : N1) (v w : SpinSpace) :
    bothAxesDomain.form (representation g v) (representation g w) =
      bothAxesDomain.form v w :=
  bothAxesDomain.representation_isometry (bothAxesDomain.restrictPermutations permutations preserves_axes)
    (fun g a => Subtype.ext (commutes_k1 g a.val))
    (fun g a => Subtype.ext (commutes_z1 g a.val)) g v w

theorem representation_monomial (g : N1)
    (a : bothAxesDomain.signedOrbits.toPairing.Orbit) :
    ∃ b, representation g (bothAxesDomain.basis a) = bothAxesDomain.basis b ∨
      representation g (bothAxesDomain.basis a) = -bothAxesDomain.basis b :=
  bothAxesDomain.representation_monomial (bothAxesDomain.restrictPermutations permutations preserves_axes)
    (fun g a => Subtype.ext (commutes_k1 g a.val))
    (fun g a => Subtype.ext (commutes_z1 g a.val)) g a

/-- The distinguished elements as elements of the actual acting group. -/
def z : N1 := ⟨z1N, psi1N_mem_N1 loopPi⟩
def c : N1 := ⟨psi2N (parkerSign 1 parkerOmega), psi2N_mem_N1 _⟩
def kOne : N1 := ⟨k1, K_le_N1 ((mem_K_iff _).mpr (by simp))⟩
def kTwo : N1 := ⟨k2, K_le_N1 ((mem_K_iff _).mpr (by simp))⟩
def kThree : N1 := ⟨k3, K_le_N1 ((mem_K_iff _).mpr (by simp))⟩

theorem representation_z (v : SpinSpace) : representation z v = -v :=
  bothAxesDomain.inducedRepresentation_of_z1 _ _ _ _ z rfl v

theorem representation_z_eq : representation z = -1 := by
  apply LinearMap.ext
  exact representation_z

theorem representation_c : representation c = 1 :=
  spin_inducedRepresentation_of_psi2_signOmega _ _ _ _ c rfl

theorem representation_kOne : representation kOne = 1 :=
  (representation_eq_one_iff _).mpr (K1_le_J (Subgroup.mem_zpowers k1))

/-- The paired-minus element in the source tensor-kernel calculation. -/
theorem kTwo_eq_c_mul_z : kTwo = c * z := by
  apply Subtype.ext
  apply Subtype.ext
  ext ⟨a,b,d⟩ : 1
  change k2.val (a,b,d) = psi2 (parkerSign 1 parkerOmega) (z1 (a,b,d))
  simp [k2_apply, psi2_apply, z1_apply, loopInverse_signOmega,
    signOmega_commutes_zero]

theorem kThree_eq_kOne_mul_kTwo : kThree = kOne * kTwo :=
  Subtype.ext k1_mul_k2.symm

theorem representation_kTwo : representation kTwo = -1 := by
  rw [kTwo_eq_c_mul_z, map_mul, representation_c, one_mul, representation_z_eq]

theorem representation_kThree : representation kThree = -1 := by
  rw [kThree_eq_kOne_mul_kTwo, map_mul, representation_kOne, one_mul,
    representation_kTwo]

def q1Inclusion : Q1 →* N1 := Subgroup.inclusion Q1_le_N1

def q1Representation : Representation ℝ Q1 SpinSpace :=
  representation.comp q1Inclusion

theorem q1Representation_eq_one_iff (q : Q1) :
    q1Representation q = 1 ↔ q.val ∈ K1 := by
  change representation (q1Inclusion q) = 1 ↔ _
  rw [representation_eq_one_iff, ← Q1_inf_J_eq_K1]
  exact ⟨fun h => ⟨q.prop,h⟩, fun h => h.2⟩

theorem q1Representation_kernel : q1Representation.ker = K1.subgroupOf Q1 := by
  ext q
  exact q1Representation_eq_one_iff q

end Sporadic.Monster.Construction.TrialitySpin.SpinAction
