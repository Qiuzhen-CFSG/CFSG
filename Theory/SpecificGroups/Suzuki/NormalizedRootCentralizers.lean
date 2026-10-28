module

public import Theory.SpecificGroups.Suzuki.RootCenter
public import Theory.GroupTheory.NormalizedRootCentralizers

/-!
# Uniform centralizers of central Suzuki root elements

The center of the standard Sylow subgroup consists exactly of the matrices
u(0,b). The already proved root centralizer containment then identifies the
centralizer of every nonidentity such element with the whole Sylow subgroup.
In particular all these elements have the same centralizer in the Borel.

Source: Huppert–Blackburn III, XI.3.1 and XI.3.10; Aschbacher–Smith,
proof of 13.6.6, printed p.927. This result concerns the actual Suzuki group;
it does not extend the Borel by arbitrary field automorphisms.
-/

public section
namespace BenderSuzuki.MatrixGroups.NormalizedRootCentralizers
open Subgroup PFAppendixIII
open scoped LinearAlgebra.Projectivization

theorem mem_center_iff_coordinates (m : ℕ) (hm : 0 < m)
    (r : SuzukiMatrixGroup m) :
    r ∈ (center (SuzukiRootSubgroup m)).map (SuzukiRootSubgroup m).subtype ↔
      ∃ b : BinaryGaloisField (2 * m + 1),
        (r : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) = SuzukiRootGL m 0 b := by
  let F := BinaryGaloisField (2 * m + 1)
  let σ : F ≃+* F := iterateFrobeniusEquiv F 2 (m + 1)
  obtain ⟨_, _, _, _, _, _, _, _, _, hc, hz, _⟩ :=
    External.huppert_blackburn_XI_3_1 m hm σ
      (External.binaryGaloisField_tits_formula_sq m σ
        (iterateFrobeniusEquiv_def F 2 (m + 1)))
  change commutator (SuzukiRootClosure m) = center (SuzukiRootClosure m) at hc
  change ∀ x : SuzukiRootClosure m, x ∈ commutator (SuzukiRootClosure m) ↔
    ∃ b : F, (x : GL (Fin 4) F) = SuzukiRootGL m 0 b at hz
  rw [hc] at hz
  let e : SuzukiRootSubgroup m ≃* SuzukiRootClosure m :=
    subgroupOfEquivOfLe (suzukiRootClosure_le m)
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact (hz (e r)).mp (centerCongr e ⟨r, hr⟩).property
  · rintro ⟨b, hb⟩
    have hr : r ∈ SuzukiRootSubgroup m :=
      (mem_suzukiRootSubgroup_iff m r).mpr ⟨0, b, hb⟩
    let u : SuzukiRootSubgroup m := ⟨r, hr⟩
    have hu : e u ∈ center (SuzukiRootClosure m) := (hz (e u)).mpr ⟨b, hb⟩
    refine ⟨u, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro x
    apply e.injective
    simpa only [map_mul] using mem_center_iff.mp hu (e x)

theorem centralizer_eq_root (m : ℕ) (hm : 0 < m)
    (r : SuzukiMatrixGroup m)
    (hr : r ∈ (center (SuzukiRootSubgroup m)).map (SuzukiRootSubgroup m).subtype)
    (hne : r ≠ 1) : centralizer ({r} : Set (SuzukiMatrixGroup m)) = SuzukiRootSubgroup m :=
  Subgroup.NormalizedRootCentralizers.centralizer_eq_of_center _
    (fun _ hx hn => suzukiRootSubgroup_centralizer_le m hm hx hn) r hr hne

theorem uniform (m : ℕ) (hm : 0 < m) (B : Subgroup (SuzukiMatrixGroup m))
    (r : SuzukiMatrixGroup m)
    (hr : r ∈ (center (SuzukiRootSubgroup m)).map (SuzukiRootSubgroup m).subtype)
    (hne : r ≠ 1) :
    B ⊓ centralizer ({r} : Set (SuzukiMatrixGroup m)) =
      B ⊓ centralizer (((center (SuzukiRootSubgroup m)).map
        (SuzukiRootSubgroup m).subtype : Subgroup (SuzukiMatrixGroup m)) : Set _) :=
  Subgroup.NormalizedRootCentralizers.uniform_of_centralizer_le _
    (fun _ hx hn => suzukiRootSubgroup_centralizer_le m hm hx hn) B r hr hne

end BenderSuzuki.MatrixGroups.NormalizedRootCentralizers
