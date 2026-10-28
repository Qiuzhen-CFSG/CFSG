module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.InvolutionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterActionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterFieldKernelSource

/-!
# The actual centralizer kernel for the terminal transfer

When the original block is centerless, source 2.4.17 makes the quotient
T/C_T(Z(R)) cyclic and identifies its intersection with S as R. These
proved source conclusions construct the entire terminal transfer datum
once the marked involution has no fusion into T minus S. No explicit
product description of the torus-normalizer complement is required.

The second theorem is the literal p.539 transfer application. The
centerlessness conclusion of 2.4.24(2), involution closure of 2.4.21(2),
and final marked-involution fusion comparison remain genuine source
premises, retained by the single-linear assembly owner.
Source: Aschbacher–Smith, printed pp.534 and538–539.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The original centerless kernel supplies every transfer datum except the
last source fusion comparison. No splitting of its Sylow complement is needed. -/
theorem source_terminal_transfer_setup_of_centerless_fusion
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (s : T)
    (hZ : center (d.block.map d.H.subtype) = ⊥)
    (hfusion : ∀ t : T, IsConj (s : G) (t : G) →
      (t : G) ∈ (d.S : Subgroup d.H).map d.H.subtype) :
    Nonempty (TerminalTransferSetup d T s) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := R ⊓ centralizer (R : Set G)
  obtain ⟨hN,hcyc⟩ := source_centerless_center_quotient_cyclic d hG T hST hsingle hL
    hM hTM hu c hZ
  have hCS : S ⊓ centralizer (Z : Set G) = R := by
    simpa only [distinguishedZ_of_centerless d hZ] using
      source_distinguished_sylow_centralizer_eq d hG T hST hsingle hL hM hTM hu
  refine ⟨{
    kernel := (centralizer (Z : Set G)).subgroupOf (T : Subgroup G)
    normal := hN
    cyclic := hcyc
    intersection := ?_
    fusion := hfusion }⟩
  ext t
  change ((t : G) ∈ centralizer (Z : Set G) ∧ (t : G) ∈ S) ↔ (t : G) ∈ R
  rw [and_comm]
  change (t : G) ∈ S ⊓ centralizer (Z : Set G) ↔ (t : G) ∈ R
  rw [hCS]

/-- The literal p.539 transfer consumer, with only the source centerlessness
and marked-involution fusion comparison still explicit after 2.4.21. -/
theorem source_false_of_centerless_fusion
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (s : T) (hs : orderOf s = 2)
    (hsR : (s : G) ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (hclosed : ∀ r t : T, orderOf r = 2 →
      (r : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) →
      IsConj (r : G) (t : G) →
      (t : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (hZ : center (d.block.map d.H.subtype) = ⊥)
    (hfusion : ∀ t : T, IsConj (s : G) (t : G) →
      (t : G) ∈ (d.S : Subgroup d.H).map d.H.subtype) : False := by
  obtain ⟨terminal⟩ := source_terminal_transfer_setup_of_centerless_fusion
    d hG T hST hsingle hL hM hTM hu c s hZ hfusion
  exact terminal.false_of_fusion hG hs hsR hclosed
end CFSG.Quasithin.Chapter2.LinearShadows.Single
