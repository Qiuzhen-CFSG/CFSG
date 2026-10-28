module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.CoveredSeed
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Support
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.BlockModuleSource.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.ResidualGeometry
/-!
# The original A₅ block module from the covered natural quotient

Once the selected short seed has made L a block, subnormal core action
identifies its intrinsic U(L) with the original commutator [U,L]. The cubic
class-sum section maps onto this literal space. Its quotient by fixed vectors
therefore has the specified natural five-letter action. The resulting block
model records the original quotient map and conjugation on representatives.
No split-cover or irreducibility assumption is introduced.
Source: C.1.21(2), C.1.23(1), printed pp.128–130; I.1.6(1).
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
open ChiProduct.BlockModuleSource
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
/-- The actual quotient witnesses movement of the original module by L. -/
theorem covered_quotient_moved_ne_bot
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H))
    (L : Subgroup H) (hL : L.map q = alternatingGroup (Fin 5))
    (p : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (p v)) : ⁅U,L⁆ ≠ ⊥ := by
  open Theory.SpecificGroups.SymmetricFive.CubicSelection in
    obtain ⟨v,hv,hm⟩ := cubic_moves_four_fixed
    obtain ⟨u,hu⟩ := hp v
    obtain ⟨l,hl,hlq⟩ := (hL.symm ▸ cubic_le_alternating cycle_mem : cycle ∈ L.map q)
    intro hc
    have hf : NormalElementaryQuotient.representation U q hq hk (q l) u = u := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [NormalElementaryQuotient.representation_apply]
      exact mul_inv_eq_iff_eq_mul.mpr ((commutator_eq_bot_iff_le_centralizer.mp hc) u.toMul.property l hl)
    have hh := he (q l) u
    rw [hf,hu,hlq] at hh
    exact hm hh.symm

/-- After actual short-seed propagation, the same covered quotient marks the
intrinsic A₅ block module. Its support is the original nonzero commutator. -/
theorem alternating_block_of_covered_quotient
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H))
    (L : Subgroup H) (hL : L.map q = alternatingGroup (Fin 5)) (hblk : IsBlock L)
    (hQC : pCore 2 H ≤ centralizer (U : Set H))
    (p : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (p v))
    (hfix : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hk g v = v) :
    IsAlternatingBlock L 5 ∧ (blockU L).map L.subtype = ⁅U,L⁆ := by
  have hne := covered_quotient_moved_ne_bot U q hq hk L hL p hp he
  have hW := ChiProduct.SelectedRankOne.blockU_eq_nontrivial_normal_module_commutator L U hblk hne
  have hWU : (blockU L).map L.subtype ≤ U := hW.le.trans (commutator_le_left _ _)
  let ρ := NormalElementaryQuotient.representation U q hq hk
  let I := space U ((blockU L).map L.subtype)
  have hI : subspaceCommutator ρ ⊤ (alternatingGroup (Fin 5)) = I := by
    simpa only [hL] using blockSpace_eq_moved U q hq hk L hblk hWU
  obtain ⟨s,hs,hse,hsr⟩ := BinaryPermutation.FiveCentralExtension.exists_moved_section ρ p hp he hfix
  have hsI : s.range = I := hsr.trans hI
  let r : I →ₗ[ZMod 2] BinaryPermutation.core (Fin 5) := p.comp I.subtype
  have hr : Function.Surjective r := by
    intro v
    exact ⟨⟨s v,hsI ▸ LinearMap.mem_range_self s v⟩,hs v⟩
  have hker : r.ker = (fixedSpace ρ (L.map q)).comap I.subtype := by
    ext w
    change p (w : Additive U) = 0 ↔ (w : Additive U) ∈ fixedSpace ρ (L.map q)
    constructor
    · intro hw b
      exact hfix w hw b (hL ▸ b.property)
    · intro hw
      have hpw : p (w : Additive U) ∈ fixedSpace (BinaryPermutation.coreRepresentation (Fin 5))
          (alternatingGroup (Fin 5)) := by
        intro b
        have hb := hw ⟨b,hL.symm ▸ b.property⟩
        change BinaryPermutation.coreRepresentation (Fin 5) b (p w) = p w
        rw [←he]
        exact congrArg p hb
      simpa only [SymmetricFive.fixedSpace_alternating_eq_bot,Submodule.mem_bot] using hpw
  let ec : centralQuotient ρ (L.map q) I ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (r.quotKerEquivOfSurjective hr)
  let en := ec.trans (BinaryPermutation.coreEquivNatural (Fin 5) (by decide))
  have hnorm : L ≤ normalizer ((blockU L).map L.subtype : Set H) :=
    L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (blockU L))
  have hstable := space_stable U q hq hk L ((blockU L).map L.subtype) hnorm
  have hcore : (q.subgroupMap L).ker = pCore 2 L := by
    rw [ker_subgroupMap,hk]
    apply le_antisymm
    · intro x hx
      apply centralizer_blockU_le_of_fitting hblk.short.fitting
      intro u hu
      apply Subtype.ext
      exact hx (u : H) (hWU (mem_map_of_mem L.subtype hu))
    · intro x hx
      exact hQC (pCoreIn_le_of_subnormal 2 hblk.subnormal (mem_map_of_mem L.subtype hx))
  refine ⟨⟨by decide,hblk.short,?_⟩,hW⟩
  apply linearBlockModel_of_coordinates U q hq hk L hWU hstable hcore
    ((BinaryPermutation.naturalRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype)
    (MulEquiv.subgroupCongr hL) en
  intro b v
  refine Submodule.Quotient.induction_on _ v ?_
  intro w
  change BinaryPermutation.coreEquivNatural (Fin 5) (by decide) (p (ρ b w)) =
    BinaryPermutation.naturalRepresentation (Fin 5) b
      (BinaryPermutation.coreEquivNatural (Fin 5) (by decide) (p w))
  rw [he,BinaryPermutation.coreEquivNatural_equivariant]

end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
