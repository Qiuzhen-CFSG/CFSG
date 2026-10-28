module
public import Theory.SpecificGroups.PSL2.BinaryCoreCommutator
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupCoreGeneration
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.NaturalExtensionRecognition

/-!
# The block forced by a nonabelian point-normalizer span

In odd field degree, the binary rank-one multiplier theorem identifies
O₂(L) with [O₂(L),L]. The proved G.2.3 collapse therefore identifies it
with the chosen natural module when the full point-normalizer span is
nonabelian. Its literal conjugation isomorphism constructs the actual
L₂(2ⁿ)-block, including all short-group and module clauses.

The only earlier independent premise retained is solvability of the literal
residual quotient-action kernel. Source 5.1.16(2) supplies it through the
Suzuki recognition owner. The ambient exclusion of this block, full
residual-normalizer TI, and Seed/parity assembly remain with
qt-d-1222-linear-field-parity. Block recognition is not block exclusion.
Source: Aschbacher–Smith 5.1.17, printed pp.640–641 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}

/-- Odd degree excludes the exceptional multiplier at field order four. -/
theorem odd_linear_core_eq_commutator
    (h : Input KnownSimple.IsKnownSimple T L W n) (hodd : Odd n) :
    L.pCoreIn 2 = ⁅L.pCoreIn 2,L⁆ := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h.linear
  have hthree : 3 ≤ n := by have := h.exponent; obtain ⟨k,hk⟩ := hodd; omega
  have hlarge : 8 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hthree
  have heven : Even (Nat.card F) := hF ▸ Even.pow_of_ne_zero (by decide) (by omega)
  have he := Theory.PSL2.core_eq_commutator_of_even_psl2 h.local_mem.2.2.1 heven hlarge e
  simpa only [Subgroup.pCoreIn,map_commutator,←MonoidHom.range_eq_map,range_subtype] using
    congrArg (map L.subtype) he

/-- Identify the literal short block through its actual natural conjugation model. -/
theorem fundamental_block_of_core_eq
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    (hcore : L.pCoreIn 2 = D.moduleSubgroup) :
    ChapterC.IsL2EvenBlock L n := by
  obtain ⟨F,_,_,_,hF,e,f,hf⟩ := hnat
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let Q := pCore 2 L
  let eqv : Q ≃* D.moduleSubgroup :=
    (Q.equivMapOfInjective L.subtype L.subtype_injective).trans (MulEquiv.subgroupCongr hcore)
  let en := eqv.trans f
  let a : L →* SL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' Q)
  have ha : Function.Surjective a := e.surjective.comp (QuotientGroup.mk'_surjective Q)
  have hk : a.ker = Q := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let := D.module_elementary
  have hQ : IsElementaryAbelian 2 Q := IsElementaryAbelian.of_injective eqv.toMonoidHom eqv.injective
  have he (l : L) (u : Q) :
      (en (extensionConjugate Q l u)).toAdd = (a l).val.mulVec (en u).toAdd := by
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.ext
    change (f.symm (f (eqv (extensionConjugate Q l u))) : G) =
      (f.symm (Multiplicative.ofAdd ((a l).val.mulVec (f (eqv u)).toAdd)) : G)
    rw [f.symm_apply_apply]
    have hh := hf l (eqv u)
    change (f.symm (Multiplicative.ofAdd ((a l).val.mulVec (f (eqv u)).toAdd)) : G) = _ at hh
    exact hh.symm
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    have hn := h.exponent
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) hn)
  exact ChapterC.isL2EvenBlock_of_naturalExtension
    (naturalExtensionOfNatural hQ a ha hk hlarge en he) h.exponent hF

/-- The nonabelian full normalizer span forces the original L to be a natural block. -/
theorem fundamental_nonabelian_block_of_solvable
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    (hnon : ¬ IsMulCommutative (normalizerSetup T L D.moduleSubgroup).U) :
    L.pCoreIn 2 = D.moduleSubgroup ∧ ChapterC.IsL2EvenBlock L n := by
  let E := normalizerSetup T L D.moduleSubgroup
  have hnot : ¬ L ≤ E.G₁ := by
    intro hn
    have hc := fundamental_point_card D h.sylow_normalizes h.linear hodd hnat
    change Nat.card E.V₁ = 2 ^ n at hc
    have hp : 1 < 2 ^ n := Nat.one_lt_pow (by have := h.exponent; omega) (by decide)
    rcases hnat.invariant_subgroup E.V₁ inf_le_right hn with hz | hz
    · rw [hz,card_bot] at hc
      omega
    · rw [hz,hnat.card,pow_mul] at hc
      nlinarith
  obtain ⟨l,hl,hlout⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨_,_,hmov⟩ := fundamental_nonabelian_core_collapse_of_solvable
    h hH c hodd hK hnf hm hsolv D hnat hnon hl hlout
  have he : L.pCoreIn 2 = D.moduleSubgroup := (odd_linear_core_eq_commutator h hodd).trans hmov
  exact ⟨he,fundamental_block_of_core_eq h D hnat he⟩
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
