module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.SylowCalculation.Geometry
public import Theory.Representation.BinaryPermutation.FiveCentralExtension
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# Fixed points of the marked five-point action

The original marked A₅-module has no nonidentity L-fixed point: the sum of
its twenty three-cycle operators is identity on the augmentation core and
zero on fixed vectors. Its T-fixed subgroup is exactly the chosen flag line.
Every Sylow-fixed vector is singular, and two distinct nonzero singular
vectors cannot have singular sum, so the fixed subgroup has order two.

These facts identify the original Z=Ω₁Z(T) after the outside-group argument
places Z inside V, and then force C_T(L)=1.
Source: Aschbacher–Smith 13.2.11(1),(3), printed p.881.
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module

theorem Marking.fixed_eq_bot {G : Type*} [Group G] {L V : Subgroup G}
    (s : Marking L V) : V ⊓ centralizer (L : Set G) = ⊥ := by
  apply bot_unique
  intro v hv
  obtain ⟨x, rfl⟩ := s.range_eq.ge hv.1
  have hxfix (g : Equiv.Perm (Fin 5)) (hg : g ∈ alternatingGroup (Fin 5)) :
      BinaryPermutation.coreRepresentation (Fin 5) g x.toAdd = x.toAdd := by
    obtain ⟨l, hl⟩ := s.onto ⟨g, hg⟩
    apply Multiplicative.ofAdd.injective
    apply s.injective
    have he := s.equivariant l x.toAdd
    rw [hl] at he
    change MulAut.conj (l : G) (s.map x) =
      s.map (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) g x.toAdd)) at he
    rw [← he]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hv.2 l l.property)
  have hx0 : x.toAdd = 0 := by
    calc
      x.toAdd = ∑ g ∈ BinaryPermutation.FiveCentralExtension.cubes,
          BinaryPermutation.coreRepresentation (Fin 5) g x.toAdd :=
        (BinaryPermutation.FiveCentralExtension.core_sum x.toAdd).symm
      _ = ∑ _g ∈ BinaryPermutation.FiveCentralExtension.cubes, x.toAdd :=
        Finset.sum_congr rfl (fun g hg => hxfix g (BinaryPermutation.FiveCentralExtension.cubes_even g hg))
      _ = 0 := by
        rw [Finset.sum_const, BinaryPermutation.FiveCentralExtension.cubes_card,
          ← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
        change (20 : ZMod 2) • x.toAdd = 0
        rw [show (20 : ZMod 2) = 0 from rfl, zero_smul]
  change s.map x = 1
  rw [show x = 1 from hx0, map_one]

theorem FlagSource.module_fixed_eq_line {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂) :
    V ⊓ centralizer ((T : Subgroup G) : Set G) = V₁ := by
  have h1V : V₁ ≤ V := d.one_le_two.trans d.two_le_V
  have h1C : V₁ ≤ centralizer ((T : Subgroup G) : Set G) := le_centralizer_iff.mp
    (d.one_invariant.trans (normalizer_le_centralizer_of_card_two _ d.one_card))
  apply le_antisymm ?_ (le_inf h1V h1C)
  obtain ⟨a, ha, _⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp d.one_card
  obtain ⟨z, hz⟩ := d.module.range_eq.ge (h1V a.property)
  have hz0 : z.toAdd ≠ 0 := by
    intro he
    apply ha
    apply Subtype.ext
    rw [← hz, show z = 1 from he, map_one]
    rfl
  have hfixed (x : Multiplicative (BinaryPermutation.core (Fin 5)))
      (hx : d.module.map x ∈ centralizer ((T : Subgroup G) : Set G)) :
      ∀ p : d.image, p ∈ (d.imageSylow : Subgroup d.image) →
        BinaryPermutation.coreRepresentation (Fin 5) p.val x.toAdd = x.toAdd := by
    rintro p ⟨t, ht, rfl⟩
    apply Multiplicative.ofAdd.injective
    apply d.module.injective
    change d.module.map (Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5) (d.normalizerAction t) x.toAdd)) =
        d.module.map x
    rw [← d.normalizer_equivariant]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hx t ht)
  have hzfix := hfixed z (hz.symm ▸ h1C a.property)
  have hzform := FlagCoordinates.SylowCalculation.sylow_fixed_singular
    d.image d.alternating_le_image d.imageSylow z.toAdd hzfix
  intro v hv
  obtain ⟨x, rfl⟩ := d.module.range_eq.ge hv.1
  have hxfix := hfixed x hv.2
  have hxform := FlagCoordinates.SylowCalculation.sylow_fixed_singular
    d.image d.alternating_le_image d.imageSylow x.toAdd hxfix
  have hsum := FlagCoordinates.SylowCalculation.sylow_fixed_singular
    d.image d.alternating_le_image d.imageSylow (x.toAdd + z.toAdd) (by
      intro p hp
      rw [map_add, hxfix p hp, hzfix p hp])
  rcases BinaryPermutation.FiveGeometry.singular_add x.toAdd z.toAdd hxform hzform hsum with he | he | he
  · rw [show x = 1 from he, map_one]
    exact V₁.one_mem
  · exact (hz0 he).elim
  · have hxz : x = z := he
    rw [hxz, hz]
    exact a.property

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
