module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiCoordinates
public import Theory.Representation.FixedPointPermutation
public import Theory.Representation.Suzuki.MinimalDegree
public import Theory.Representation.Suzuki.NaturalMatrix
public import Theory.Representation.TwoDimensionalOddOrder

/-!
# The binary natural module needed in Section 10

Every faithful four-dimensional binary representation of Sz(2) is equivalent
to its actual natural matrix representation. The root Sylow has four elements
and five cosets. A nonzero Sylow-fixed vector gives a map from the augmentation
module of those five cosets. Irreducibility makes the map onto, and the equal
four-dimensional ranks make it an equivalence. Applying this to both modules
identifies them without invoking a simplicity theorem for Sz(2).

Consumer: the two literal Suzuki sections in NaturalLayers, including m = 0.
Source: Fong--Seitz II (1974), printed pp.221--224, before (10.4) and (10.11).
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups Representation
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10

private abbrev binaryPoints := SuzukiMatrixGroup 0 ⧸ SuzukiRootSubgroup 0

private instance : Fintype binaryPoints := Fintype.ofFinite _

private theorem binaryPoints_card : Nat.card binaryPoints = 5 := by
  have h := (SuzukiRootSubgroup 0).card_mul_index
  have hc : Nat.card (SuzukiRootSubgroup 0) = 4 := by simpa using matrixRoot_card 0
  rw [hc, suzukiZero_card] at h
  change (SuzukiRootSubgroup 0).index = 5
  omega

private def binaryCore := FixedPointPermutation.core
  (K := ZMod 2) (G := SuzukiMatrixGroup 0) (Ω := binaryPoints)

private theorem binaryCore_finrank : Module.finrank (ZMod 2) binaryCore.toSubmodule = 4 := by
  have h := FixedPointPermutation.finrank_core (K := ZMod 2) (G := SuzukiMatrixGroup 0)
    (Ω := binaryPoints) (QuotientGroup.mk (1 : SuzukiMatrixGroup 0))
  rw [← Nat.card_eq_fintype_card, binaryPoints_card] at h
  change Module.finrank (ZMod 2) binaryCore.toSubmodule + 1 = 5 at h
  omega

private theorem binaryCore_equiv
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup 0) V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4) :
    Nonempty (binaryCore.toRepresentation.Equiv ρ) := by
  have hc : Nat.card V = 2 ^ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) V)
  let := (Suzuki.irreducible_of_faithful_small_card ρ hf (by simp [hc])).1
  have hp : IsPGroup 2 (SuzukiRootSubgroup 0) :=
    IsPGroup.of_card (n := 2) (by simpa using matrixRoot_card 0)
  obtain ⟨v,hv,hfix⟩ := pGroup_fix_nonzero_vector (F := ZMod 2)
    (by simp [ZMod.ringChar_zmod_n]) (by simpa [ZMod.ringChar_zmod_n] using hp)
    (ρ.comp (SuzukiRootSubgroup 0).subtype)
  let x : binaryPoints := QuotientGroup.mk (1 : SuzukiMatrixGroup 0)
  have hx (g : SuzukiMatrixGroup 0) (hg : g • x = x) : ρ g v = v := by
    have hm : g ∈ SuzukiRootSubgroup 0 := by
      rw [← MulAction.stabilizer_quotient (SuzukiRootSubgroup 0)]
      exact hg
    exact hfix ⟨g,hm⟩
  have hmove : ∃ g, ρ g v ≠ v := by
    by_contra! hall
    have hn : invariants (ρ.comp (⊤ : Subgroup (SuzukiMatrixGroup 0)).subtype) ≠ ⊥ := by
      intro hz
      exact hv (hz.le (fun g => hall g))
    have hk := ρ.le_ker_of_normal_invariants_ne_bot ⊤ hn
    have he : ρ = 1 := MonoidHom.ext (fun g => hk (Subgroup.mem_top g))
    let : Subsingleton (SuzukiMatrixGroup 0) := ⟨fun g h => hf (by simp only [he,MonoidHom.one_apply])⟩
    have hh := Nat.card_of_subsingleton (1 : SuzukiMatrixGroup 0)
    rw [suzukiZero_card] at hh
    omega
  let f := FixedPointPermutation.coreOrbitMap x ρ v hx
  have hn : f ≠ 0 := FixedPointPermutation.coreOrbitMap_ne_zero x ρ v hx hmove
  have hs := (IsIrreducible.surjective_or_eq_zero f).resolve_right hn
  have hi : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) (binaryCore_finrank.trans hd.symm)).mpr hs
  exact ⟨f.ofBijective ⟨hi,hs⟩⟩

/-- In degree four, a faithful binary Suzuki representation is the literal
natural matrix module. The five Sylow cosets give the common augmentation model. -/
theorem binary_natural_equiv
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup 0) V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4) :
    Nonempty (ρ.Equiv (SuzukiNatural.natural 0)) := by
  have hnat : Function.Injective (SuzukiNatural.natural 0) := by
    intro x y h
    apply (SuzukiMatrixSubgroup 0).subtype_injective
    apply generalLinearNatural_injective 4
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun h v
  obtain ⟨a⟩ := binaryCore_equiv ρ hf hd
  obtain ⟨b⟩ := binaryCore_equiv (SuzukiNatural.natural 0) hnat
    (by simpa using SuzukiNatural.natural_finrank 0)
  exact ⟨a.symm.trans b⟩

end Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
