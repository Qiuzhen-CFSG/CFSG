module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.BinaryLinearThree
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import Theory.GroupTheory.PResidual.PrimeToPerfect

/-!
# Quintic automorphisms of a natural binary SL3 block

The literal core quotient is SL3(2), whose automorphism group has order
336. A five-group therefore fixes that quotient. The natural binary
module has no nontrivial scalar automorphisms, and two-perfectness removes
the central attachment, so the five-group centralizes the entire block.
The original prime-five component consumer is in Chapter15
ExchangedSelection.Decomposable.QuinticExclusion.

Source: Aschbacher--Smith C.1.10 and 15.1.23, printed pp.124 and 1100.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- A five-group normalizing a natural binary SL3 block fixes its full cover. -/
theorem IsSL3EvenBlock.quintic_centralizes
    {L Y : Subgroup G} (hL : IsSL3EvenBlock L 1)
    (hY : IsPGroup 5 Y) (hn : Y ≤ normalizer (L : Set G)) :
    Y ≤ centralizer (L : Set G) := by
  let a : Y →* MulAut L := L.normalizerMonoidHom.comp (inclusion hn)
  let q := (quotientAut (pCore 2 L)).comp a
  have hc : Nat.card (MulAut (L ⧸ pCore 2 L)) = 336 := by
    obtain ⟨F,_,_,hF,ρ,⟨m⟩,hρ⟩ := hL.2.2
    have hfield : Nat.card F = 2 := by simpa using hF
    let _ := Fintype.ofFinite F
    let eF : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hfield)).symm
    let e := m.quotientIso.trans (Atlas.fieldEquivSL 3 eF)
    rw [Nat.card_congr (MulAut.congr (e.trans Matrix.PSL3Two.equiv)).toEquiv]
    exact Matrix.PSL3Two.Automorphisms.card_aut
  have hq (y : Y) : q y = 1 := by
    obtain ⟨n,hn⟩ := hY y
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 5 336).pow_left n)
    · exact orderOf_dvd_of_pow_eq_one (by rw [←map_pow,hn,map_one])
    · simpa only [hc] using orderOf_dvd_natCard (q y)
  have hperf : IsPPerfect 2 Y := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have he : primeToResidual 5 Y = ⊤ := by
      apply top_unique
      intro y _
      obtain ⟨n,hn⟩ := hY y
      exact mem_primeToResidual_of_pow hn
    exact (isPPerfect_primeToResidual (G := Y) 5 2 (by decide)).of_surjective
      (primeToResidual 5 Y).subtype (by
        intro y
        exact ⟨⟨y,he ▸ mem_top y⟩,rfl⟩)
  apply hL.centralizes_of_coreQuotient hperf hn
  apply commutator_le.mpr
  intro y hy l hl
  have he := DFunLike.congr_fun (hq ⟨y,hy⟩)
    (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩)
  change quotientAut (pCore 2 L) (a ⟨y,hy⟩)
    (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩) = _ at he
  rw [quotientAut_apply_mk] at he
  have hh : a ⟨y,hy⟩ ⟨l,hl⟩ * (⟨l,hl⟩ : L)⁻¹ ∈ pCore 2 L := by
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp he
  exact mem_map.mpr ⟨_,hh,rfl⟩

end CFSG.Quasithin.ChapterC
