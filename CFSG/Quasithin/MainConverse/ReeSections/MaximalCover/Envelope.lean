module

public import CFSG.Quasithin.MainConverse.ReeSections.Reduction
public import Mathlib.GroupTheory.Nilpotent

/-!
# Envelopes for the groups on the Ree maximal-subgroup list

The elementary closure calculations used in Malle's list are central extensions,
products, extensions of index two, and homomorphisms with finite two-group kernels.
The SU₃ case uses the scalar kernel of its map into PGL. The PGU₃ case instead
uses the determinant on U₃, whose kernel is SU₃, followed by the surjection to
its projective image. Thus neither unitary group is identified with PSU₃.
The symplectic case retains its central kernel as well.

For the two parabolics it suffices to construct a map to SL₂ times the field
units, or to the Suzuki group times the field units, with a two-group kernel.
No surjectivity, ambient simplicity, radical order or subgroup exhaustion is
assumed in these elementary implications.

Source: the maximal-subgroup list in the proof of Theorem 5, pp.2–3, of
Himstedt–Nguyen–Tiep, arXiv:0910.4758, citing Malle, J. Algebra 139 (1991),
52–69, DOI 10.1016/0021-8693(91)90283-E. These are closure lemmas for the
section argument, not a proof that the list exhausts the maximal subgroups.
-/

public section

open Matrix BenderSuzuki.MatrixGroups

namespace CFSG.Quasithin.MainConverse.ReeSections

/-- Commutative groups provide solvable leaves. -/
theorem Envelope.commutative {m : ℕ} (H : Type) [Group H] [IsMulCommutative H] :
    Envelope m H :=
  .solvable _ (Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b)

/-- Transport an envelope along an actual multiplicative equivalence. -/
theorem Envelope.of_mulEquiv {m : ℕ} {H L : Type} [Group H] [Group L]
    (h : Envelope m L) (e : H ≃* L) : Envelope m H :=
  .subgroup e.toMonoidHom e.injective h

/-- Remove a kernel using the faithful map from its actual quotient. -/
theorem Envelope.of_kernel {m : ℕ} {H L : Type} [Group H] [Group L]
    (p : H →* L) (hker : Envelope m p.ker) (hL : Envelope m L) :
    Envelope m H :=
  .extension p.ker hker
    (.subgroup (QuotientGroup.kerLift p) (QuotientGroup.kerLift_injective p) hL)

/-- A solvable kernel does not add nonsolvable leaves to the envelope. -/
theorem Envelope.of_solvable_kernel {m : ℕ} {H L : Type} [Group H] [Group L]
    (p : H →* L) [Group.IsSolvable p.ker] (hL : Envelope m L) : Envelope m H :=
  Envelope.of_kernel p (.solvable _ inferInstance) hL

/-- The two factors give an envelope for their direct product. -/
theorem Envelope.prod {m : ℕ} {H L : Type} [Group H] [Group L]
    (hH : Envelope m H) (hL : Envelope m L) : Envelope m (H × L) := by
  let p : H × L →* L := MonoidHom.snd H L
  let i : p.ker →* H := (MonoidHom.fst H L).comp p.ker.subtype
  have hi : Function.Injective i := by
    intro a b hab
    apply Subtype.ext
    apply Prod.ext hab
    exact a.property.trans b.property.symm
  exact Envelope.of_kernel p (.subgroup i hi hH) hL

/-- A normal subgroup of index two has a cyclic, hence solvable, quotient. -/
theorem Envelope.of_index_two {m : ℕ} {H : Type} [Group H]
    (N : Subgroup H) [N.Normal] (hN : Envelope m N)
    (hindex : Nat.card (H ⧸ N) = 2) : Envelope m H := by
  let : IsCyclic (H ⧸ N) := isCyclic_of_prime_card hindex
  exact .extension N hN (.commutative _)

/-- The central quotient of SL₂ is the concrete PSL₂ carrier. -/
theorem Envelope.specialLinearTwo {m : ℕ} (F : Type) [Field F] [Finite F] :
    Envelope m (SpecialLinearGroup (Fin 2) F) := by
  exact .extension (Subgroup.center (SpecialLinearGroup (Fin 2) F))
    (.commutative _)
    (.linearTwo _ (Nat.card F) ⟨F, inferInstance, inferInstance, rfl, ⟨MulEquiv.refl _⟩⟩)

/-- The scalar kernel of SU₃ → PSU₃ is central inside SU₃. -/
theorem Envelope.specialUnitary {m : ℕ} {F : Type} [Field F]
    (J : HermitianForm 3 F) (h : Envelope m (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Envelope m J.specialSubgroup := by
  let p : J.specialSubgroup →* ProjectiveSpecialUnitaryMatrixGroup J :=
    ProjGenLinGroup.mk.subgroupMap J.specialSubgroup
  have hcentral : p.ker ≤ Subgroup.center J.specialSubgroup := by
    intro x hx
    have hx' : ProjGenLinGroup.mk x.val = 1 := congrArg Subtype.val hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (ProjGenLinGroup.mk_eq_one.mp hx') y.val
  exact Envelope.of_kernel p (.subgroup (Subgroup.inclusion hcentral)
    (Subgroup.inclusion_injective hcentral) (.commutative _)) h

private def unitaryDetKernelEquiv {F : Type} [Field F] (J : HermitianForm 3 F) :
    (GeneralLinearGroup.det.comp J.unitarySubgroup.subtype).ker ≃* J.specialSubgroup where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The determinant kernel in U₃ is the actual special unitary subgroup. -/
theorem Envelope.unitary {m : ℕ} {F : Type} [Field F]
    (J : HermitianForm 3 F) (h : Envelope m (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Envelope m J.unitarySubgroup := by
  let d : J.unitarySubgroup →* Fˣ := GeneralLinearGroup.det.comp J.unitarySubgroup.subtype
  have hk : Envelope m d.ker := (h.specialUnitary J).of_mulEquiv (unitaryDetKernelEquiv J)
  exact Envelope.of_kernel d hk (.commutative Fˣ)

/-- PGU₃ is the projective image of U₃, with its determinant layer retained. -/
theorem Envelope.projectiveUnitary {m : ℕ} {F : Type} [Field F]
    (J : HermitianForm 3 F) (h : Envelope m (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Envelope m (J.unitarySubgroup.map ProjGenLinGroup.mk) :=
  .quotient (ProjGenLinGroup.mk.subgroupMap J.unitarySubgroup)
    (ProjGenLinGroup.mk.subgroupMap_surjective J.unitarySubgroup) (h.unitary J)

/-- Remove the center of Sp₄ to obtain the concrete PSp₄ carrier. -/
theorem Envelope.symplectic {m : ℕ} (F : Type) [Field F] [Finite F]
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) : Envelope m (symplecticGroup (Fin 2) F) :=
  .extension (Subgroup.center (symplecticGroup (Fin 2) F)) (.commutative _)
    (.symplecticFour _ ⟨F, inferInstance, inferInstance, hcard, ⟨MulEquiv.refl _⟩⟩)

/-- A finite two-group kernel is nilpotent and hence solvable. -/
theorem Envelope.of_two_group_kernel {m : ℕ} {H L : Type}
    [Group H] [Finite H] [Group L] (p : H →* L) (hker : IsPGroup 2 p.ker)
    (hL : Envelope m L) : Envelope m H := by
  let : Group.IsNilpotent p.ker := hker.isNilpotent
  exact hL.of_solvable_kernel p

/-- The precise linear Levi-map contract sufficient for a parabolic envelope. -/
theorem Envelope.linearParabolic {m : ℕ} {H : Type} [Group H] [Finite H]
    (p : H →* SpecialLinearGroup (Fin 2) (ReeF4.CoefficientField m) ×
      (ReeF4.CoefficientField m)ˣ) (hker : IsPGroup 2 p.ker) : Envelope m H :=
  ((Envelope.specialLinearTwo (ReeF4.CoefficientField m)).prod
    (.solvable _ inferInstance)).of_two_group_kernel p hker

/-- The precise Suzuki Levi-map contract sufficient for a parabolic envelope. -/
theorem Envelope.suzukiParabolic {m : ℕ} (hm : 1 ≤ m) {H : Type}
    [Group H] [Finite H]
    (p : H →* SuzukiMatrixGroup m × (ReeF4.CoefficientField m)ˣ)
    (hker : IsPGroup 2 p.ker) : Envelope m H :=
  ((Envelope.suzuki m hm).prod (.solvable _ inferInstance)).of_two_group_kernel p hker

end CFSG.Quasithin.MainConverse.ReeSections
