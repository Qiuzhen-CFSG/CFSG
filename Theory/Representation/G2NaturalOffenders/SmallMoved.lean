module

public import Theory.Representation.G2NaturalOffenders
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Every natural G₂ offender moves more than a binary plane

The concrete offender classification places a conjugate of the short root C
inside every offender. That single root has displacement rank three times the
field degree, since its fixed space is the upper three-space. Its displacement
range lies in the offender's whole moved space. This includes the binary
endpoint G₂(2) and hence marked actions whose component is G₂(2)′.

Source: Aschbacher–Smith B.4.6(13) and 13.7.15(1), printed pp.88–90,943–944.
-/

public section
namespace Atlas.G2.NaturalOffenders
open Representation Representation.BinaryOffender Subgroup
open Restricted.NaturalCoordinates LieParabolicSetup
variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F] [Finite F]

/-- The short-root displacement has binary dimension three times the field degree. -/
theorem fixedCodim_rootC {n : ℕ} (hc : Nat.card F = 2 ^ n) (a : F) (ha : a ≠ 0) :
    fixedCodim (binaryAction (F := F)) (zpowers (rootC a)) = 3 * n := by
  have hs : fixedSpace (binaryAction (F := F)) (zpowers (rootC a)) =
      (upper (F := F)).restrictScalars (ZMod 2) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    exact fixed_rootC_iff a ha v
  have hd := fixedCodim_add_finrank (binaryAction (F := F)) (zpowers (rootC a))
  rw [hs, upper_binary_finrank hc, coordinates_binary_finrank hc] at hd
  omega

/-- A genuine offender contains an actor with displacement rank 3n. -/
theorem natural_offender_large_displacement {n : ℕ} (hc : Nat.card F = 2 ^ n)
    (hn : 0 < n) (A : Subgroup (Model F)) (hA : IsOffender (binaryNatural (F := F)) A) :
    ∃ a ∈ A, fixedCodim (binaryNatural (F := F)) (zpowers a) = 3 * n := by
  obtain ⟨g,_,hg⟩ := natural_offender_rootPair hc hn A hA
  refine ⟨g * rootC 1 * g⁻¹,hg,?_⟩
  rw [natural_fixedCodim_eq]
  change fixedCodim (binaryAction (F := F))
    (zpowers ((MulAut.conj g).toMonoidHom (rootC 1))) = _
  rw [← MonoidHom.map_zpowers, fixedCodim_map_conj]
  exact fixedCodim_rootC hc 1 one_ne_zero

/-- This is the actual moved-space exclusion used in 13.7.15. -/
theorem natural_offender_moved_gt_two {n : ℕ} (hc : Nat.card F = 2 ^ n)
    (hn : 0 < n) (A : Subgroup (Model F)) (hA : IsOffender (binaryNatural (F := F)) A) :
    2 < Module.finrank (ZMod 2) (subspaceCommutator (binaryNatural (F := F)) ⊤ A) := by
  obtain ⟨a,ha,hcA⟩ := natural_offender_large_displacement hc hn A hA
  rw [fixedCodim_zpowers_eq_displacement_rank] at hcA
  have hle : LinearMap.range (binaryNatural a - LinearMap.id) ≤
      subspaceCommutator (binaryNatural (F := F)) ⊤ A := by
    rintro _ ⟨v,rfl⟩
    exact Submodule.subset_span ⟨a,ha,v,Submodule.mem_top,rfl⟩
  have hd := Submodule.finrank_mono hle
  omega
end Atlas.G2.NaturalOffenders
