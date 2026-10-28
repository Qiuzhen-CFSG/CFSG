module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2CoverCoordinates
public import Theory.Representation.SL2OrthogonalCover.Sylow

/-!
# Fusion in an even rank-one block module

The natural quotient moves every vector into the fixed line of a prescribed
Sylow two-subgroup. Fixed-point lifting through the actual central cover
then puts its original lift in the Sylow centralizer. When the center is
trivial, the natural coordinates give transitivity on nonidentity elements.

Source: Aschbacher–Smith, I.2.3(1) and the proof of 2.4.20(3),
printed pp.413 and535.
-/

public section
open Subgroup Representation Representation.OneCohomology Matrix
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
open ExceptionalRestrictions
variable {L : Type*} [Group L] [Finite L]

/-- Every original module element has a conjugate fixed by the prescribed Sylow. -/
theorem IsL2EvenBlock.module_conjugate_centralizes_sylow
    {n : ℕ} (hL : IsL2EvenBlock L n) (P : Sylow 2 L) (u : blockU L) :
    ∃ l : L, (blockConjugate L l u : L) ∈ centralizer (P : Set L) := by
  let := hL.2.1.elementary
  let := hL.2.1.module_elementary
  obtain ⟨F,_,_,hF,_,ρ,⟨m⟩,hm⟩ := hL.2.2
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let q : L →* Matrix.SpecialLinearGroup (Fin 2) F :=
    m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q :=
    m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective hq
  let σ := modelCoverAction hL.2.1 m
  let p := modelCoverMap m
  let v := p (Additive.ofMul u)
  have hmove : ∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
      SL2OrthogonalCover.binaryNatural g v ∈
        fixed ((SL2OrthogonalCover.binaryNatural (F := F)).comp Q.toSubgroup.subtype) := by
    by_cases hv : v = 0
    · refine ⟨1,?_⟩
      simp only [hv,map_zero]
      exact Submodule.zero_mem _
    · have hd := SL2OrthogonalCover.natural_sylow_fixed_dimension Q
      let W := fixed ((SL2OrthogonalCover.natural (F := F)).comp Q.toSubgroup.subtype)
      let : Nontrivial W := Module.nontrivial_of_finrank_pos (R := F) (by
        change 0 < Module.finrank F (fixed ((SL2OrthogonalCover.natural (F := F)).comp Q.toSubgroup.subtype))
        rw [hd]; exact Nat.zero_lt_one)
      obtain ⟨w,hw⟩ := exists_ne (0 : W)
      have hw0 : (w : Fin 2 → F) ≠ 0 := fun he => hw (Subtype.ext he)
      obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq F v w hv hw0
      refine ⟨g,?_⟩
      change SL2OrthogonalCover.natural g v ∈ W
      change g.val *ᵥ v ∈ W
      rw [hg]
      exact w.property
  obtain ⟨g,hg⟩ := hmove
  obtain ⟨l,hl⟩ := hq g
  let w := blockConjugate L l u
  have hw : p (Additive.ofMul w) ∈
      fixed ((SL2OrthogonalCover.binaryNatural (F := F)).comp Q.toSubgroup.subtype) := by
    have he := modelCoverMap_intertwining hL.2.1 m hm (q l) (Additive.ofMul u)
    change modelCoverMap m (modelCoverAction hL.2.1 m
      (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l)) (Additive.ofMul u)) = _ at he
    rw [modelCoverAction_apply] at he
    change p (Additive.ofMul w) = SL2OrthogonalCover.binaryNatural (q l) v at he
    rw [he,hl]
    exact hg
  have hf : Additive.ofMul w ∈ fixed (σ.comp Q.toSubgroup.subtype) := by
    intro a
    apply SL2NaturalFixedLifting.fixed_lift_of_fixed_kernel σ p.toAddMonoidHom
      (modelCoverMap_surjective m)
      (fun g z => modelCoverMap_intertwining hL.2.1 m hm g z)
      (fun z hz g => (uRepresentation_fixed hL.2.1 z).mpr
        ((modelCoverMap_ker m z).mp hz) _) a.val (Additive.ofMul w)
    exact (modelCoverMap_intertwining hL.2.1 m hm a.val (Additive.ofMul w)).trans (hw a)
  refine ⟨l,mem_centralizer_iff.mpr ?_⟩
  intro a ha
  have he := hf ⟨q a,mem_map_of_mem q ha⟩
  change modelCoverAction hL.2.1 m (q a) (Additive.ofMul w) = Additive.ofMul w at he
  change modelCoverAction hL.2.1 m
    (m.quotientIso (QuotientGroup.mk' (pCore 2 L) a)) (Additive.ofMul w) = Additive.ofMul w at he
  rw [modelCoverAction_apply] at he
  have hc : a * (w : L) * a⁻¹ = (w : L) := congrArg (fun z => (z.toMul : L)) he
  exact (mul_inv_eq_iff_eq_mul.mp hc)

omit [Finite L] in
/-- A centerless natural block acts transitively on its nonidentity module elements. -/
theorem IsL2EvenBlock.module_transitive_of_centerless
    {n : ℕ} (hL : IsL2EvenBlock L n) (hz : center L = ⊥)
    (u v : blockU L) (hu : u ≠ 1) (hv : v ≠ 1) :
    ∃ l : L, blockConjugate L l u = v := by
  let := hL.2.1.elementary
  let := hL.2.1.module_elementary
  obtain ⟨F,_,_,hF,_,ρ,⟨m⟩,hm⟩ := hL.2.2
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hfixed : blockFixed L = ⊥ := by
    change (center L).subgroupOf (blockU L) = ⊥
    rw [hz,bot_subgroupOf]
  obtain ⟨e,he⟩ := modelCover_natural_equiv hL.2.1 m hm hfixed
  have hu0 : (e u).toAdd ≠ 0 := by
    intro he
    exact hu (e.injective (he.trans e.map_one.symm))
  have hv0 : (e v).toAdd ≠ 0 := by
    intro he
    exact hv (e.injective (he.trans e.map_one.symm))
  obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq F (e u).toAdd (e v).toAdd hu0 hv0
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (m.quotientIso.symm g)
  refine ⟨l,e.injective (Multiplicative.toAdd.injective ?_)⟩
  rw [he,hl,m.quotientIso.apply_symm_apply]
  exact hg

end CFSG.Quasithin.ChapterC
