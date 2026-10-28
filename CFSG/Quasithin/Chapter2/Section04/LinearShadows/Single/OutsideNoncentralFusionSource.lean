module
public import CFSG.Quasithin.ChapterI.Section06To08.TICommutatorFusion
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterDisplacementSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DistinguishedGeometrySource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideDerivedSource
public import Theory.GroupAction.SubgroupFixedPrimeElement

/-!
# Noncentral outside involutions in the centerless source branch

For an involution fused into the Thompson center, the cyclic center action
forces its fixed subgroup's derived subgroup to centralize the entire fused
center. A nonzero fixed central element then gives commutation by the TI-pair
theorem. The actual outside fixed-derived calculation and Singer displacements
discharge the local commutator premise. Consequently every outside involution
fused into the center centralizes that center.

Source: Aschbacher–Smith, 2.4.21, noncentral z-class case, printed p.536.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open Theory.GroupTheory ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_centerless_conjugate_centralizes_of_fixed_derived
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (a g : G) (haT : a ∈ T) (ha2 : a^2=1) (ha1 : a ≠ 1) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    let I := R ⊓ centralizer ({a} : Set G)
    a ∈ Z.map (MulAut.conj g).toMonoidHom →
    Z ⊓ centralizer ({a} : Set G) ≤ ⁅I,I⁆ → a ∈ centralizer (Z : Set G) := by
  intro R Z I ha hd
  have hzdef := distinguishedZ_of_centerless d hZ
  have hTI : IsTISubgroup Z := by
    simpa only [hzdef] using source_distinguished_TI d hG T hST hsingle hL hM hTM hunique
  have hzdata := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  rw [hzdef] at hzdata
  let : IsElementaryAbelian 2 Z := hzdata.1
  obtain ⟨hTZ,hcyc⟩ := source_centerless_center_action_cyclic d hG T hST hsingle hL
    hM hTM hunique c hZ
  have hI : IsPGroup 2 I := T.isPGroup'.to_le
    (inf_le_left.trans ((sSup_le fun _ h => h.1).trans hST.le))
  have hcomm := hTI.commutator_le_conjugate_centralizer_of_sylow_action Z I T hTZ hcyc
    hI g a ha ha1 inf_le_right
  have hdiv : 2 ∣ Nat.card Z := by
    rw [hzdata.2.1]
    exact dvd_pow_self _ (by have := hL.1; omega)
  obtain ⟨z,hz,hz2,hza⟩ := Z.exists_order_prime_in_centralizer_of_normalizes ha2 (hTZ haT) hdiv
  have hfix : Z ⊓ centralizer ({a} : Set G) ≠ ⊥ := by
    intro he
    have hz1 : z=1 := by
      have hm : z ∈ Z ⊓ centralizer ({a} : Set G) := ⟨hz,hza⟩
      rw [he] at hm
      exact hm
    simp only [hz1,orderOf_one] at hz2
    omega
  exact hTI.mem_centralizer_of_derived_fixed Z I g a ha hfix hd hcomm

theorem source_centerless_outside_conjugate_centralizes
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (a g : G) (haT : a ∈ T) (haS : a ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (ha2 : a^2=1) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    a ∈ Z.map (MulAut.conj g).toMonoidHom → a ∈ centralizer (Z : Set G) := by
  intro R Z ha
  by_contra han
  have htrace := source_centerless_center_involution_coboundary d hG T hST hsingle hL
    hM hTM hunique c hZ a haT ha2 han
  have hderived := source_outside_fixed_derived_of_coboundaries d hG T hST hsingle hL
    hM hTM hunique a haT haS ha2 htrace
  exact han (source_centerless_conjugate_centralizes_of_fixed_derived d hG T hST hsingle hL
    hM hTM hunique c hZ a g haT ha2 (fun he => haS (he ▸ one_mem _)) ha hderived.ge)
end CFSG.Quasithin.Chapter2.LinearShadows.Single
