module

public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.RankOne
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.SpecificGroups.PSL2.RankOneRoots
public import Theory.SpecificGroups.Suzuki.RankOneRoots

/-!
# Rank-one root cases for characteristic-two components

For a quasisimple group with trivial odd core, its center is its two-core.
Faithfulness on the central quotient makes an inner involutory automorphism
conjugation by an actual quotient involution. The matrix calculations put
that involution in a long-root subgroup, with a two-group centralizer.
Taking inverse images through the central two-kernel proves that C_L(r) is
a two-group, including for exceptional Suzuki covers. The inverse image of
the conjugate standard Borel is a proper parabolic containing C_L(r).
It gives the equality of the two residuals with their embeddings in L retained.

The PSL₂ branch takes innerness as its branch hypothesis. Suzuki innerness
and the PSL₂ Sylow-fixing assertion are supplied by `RankOne`; no extra
model, splitting, or automorphism-coverage hypotheses are introduced here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
16.1.4(1) and 16.1.6, printed pp.1171–1172. Full source case assembly
remains in `LiePreliminaries`.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.LiePreliminaries
variable {L S : Type*} [Group L] [Group S] [Finite L] [IsQuasisimple L]

/-- The full inverse image of a conjugate standard Borel in a specified quotient. -/
@[expose] def rankOneParabolic (e : (L ⧸ pCore 2 L) ≃* S) (B : Subgroup S) (g : S) : Subgroup L :=
  (B.comap (MulAut.conj g).toMonoidHom).comap
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))

/-- O²(C_P(r)), embedded in the original component. -/
@[expose] def parabolicFixedTwoResidual (P : Subgroup L) (r : MulAut L) : Subgroup L :=
  (pResidual 2 (P ⊓ r.fixedSubgroup : Subgroup L)).map (P ⊓ r.fixedSubgroup).subtype

omit [Finite L] [IsQuasisimple L] in
private theorem residual_bot_of_two (r : MulAut L) (h : IsPGroup 2 r.fixedSubgroup) :
    fixedTwoResidual L r = ⊥ := by
  have hb : pResidual 2 r.fixedSubgroup = ⊥ :=
    le_bot_iff.mp (sInf_le ⟨inferInstance, h.to_quotient ⊥⟩)
  rw [fixedTwoResidual, hb, Subgroup.map_bot]

private theorem quotient_inner_involution (hodd : pPrimeCore 2 L = ⊥)
    (e : (L ⧸ pCore 2 L) ≃* S) (r : MulAut L) (hr : orderOf r = 2)
    (hinner : ∃ y : L, r = MulAut.conj y) :
    let c := (centerQuotientEquivTwoCore hodd).trans e
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    ∃ x : S, orderOf x = 2 ∧ MulAut.centralQuotientAction c r = MulAut.conj x ∧
      r.fixedSubgroup ≤ (centralizer {x}).comap f := by
  dsimp only
  let c := (centerQuotientEquivTwoCore hodd).trans e
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  obtain ⟨y, rfl⟩ := hinner
  have hc : center S = ⊥ := by
    apply (center S).eq_bot_iff_forall.mpr
    intro x hx
    have hz : c.symm x ∈ center (L ⧸ center L) :=
      (MulEquivClass.apply_mem_center_iff c.symm).mpr hx
    have h1 : c.symm x = 1 := by
      simpa only [Group.IsPerfect.center_quotient_center_eq_bot, mem_bot] using hz
    simpa only [c.apply_symm_apply, map_one] using congrArg c h1
  have ha : MulAut.centralQuotientAction c (MulAut.conj y) = MulAut.conj (f y) :=
    MulAut.centralQuotientAction_conj c y
  refine ⟨f y, ?_, ha, ?_⟩
  · rw [← orderOf_injective MulAut.conj (conj_injective_of_center_eq_bot hc), ← ha,
      MulAut.orderOf_centralQuotientAction, hr]
  · rw [MulAut.fixedSubgroup_conj]
    intro z hz
    exact mem_centralizer_singleton_iff.mpr
      ((show Commute z y from mem_centralizer_singleton_iff.mp hz).map f).eq

omit [Finite L] [IsQuasisimple L] in
private theorem cover_geometry (e : (L ⧸ pCore 2 L) ≃* S) (r : MulAut L) (x g : S)
    (B : Subgroup S) (hB : B ≠ ⊤)
    (hfix : r.fixedSubgroup ≤ (centralizer {x}).comap
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))
    (hCB : centralizer {x} ≤ B.comap (MulAut.conj g).toMonoidHom)
    (hC : IsPGroup 2 (centralizer {x})) :
    let P := rankOneParabolic e B g
    P ≠ ⊤ ∧ r.fixedSubgroup ≤ P ∧ IsPGroup 2 r.fixedSubgroup ∧
      fixedTwoResidual L r = ⊥ ∧ fixedTwoResidual L r = parabolicFixedTwoResidual P r := by
  dsimp only
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 L := by
    ext y
    change e (QuotientGroup.mk' (pCore 2 L) y) = 1 ↔ y ∈ pCore 2 L
    rw [← map_one e, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff y
  have htwo : IsPGroup 2 r.fixedSubgroup :=
    (hC.comap_of_ker_isPGroup f (hk ▸ pCore_isPGroup)).to_le hfix
  have hle : r.fixedSubgroup ≤ rankOneParabolic e B g :=
    hfix.trans (comap_mono hCB)
  refine ⟨?_, hle, htwo, residual_bot_of_two r htwo, ?_⟩
  · intro h
    apply hB
    apply top_unique
    intro z _
    obtain ⟨y, hy⟩ := ((MulAut.conj g).surjective.comp hf) z
    have hm : y ∈ rankOneParabolic e B g := by rw [h]; trivial
    change MulAut.conj g (f y) ∈ B at hm
    change MulAut.conj g (f y) = z at hy
    rwa [hy] at hm
  · unfold parabolicFixedTwoResidual
    rw [show rankOneParabolic e B g ⊓ r.fixedSubgroup = r.fixedSubgroup from
      inf_eq_right.mpr hle]
    rfl

end CFSG.Quasithin.Chapter16.LiePreliminaries

namespace CFSG.Quasithin.Chapter16.LiePreliminaries
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups BenderSuzuki.Converse
open BenderSuzuki.PFAppendixIII

variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]

/-- The inner PSL₂ branch of 16.1.4(1), with actual matrix roots and the
proper parabolic obtained from the standard Borel of the simple quotient. -/
theorem psl2_inner_involution_roots (hodd : pPrimeCore 2 L = ⊥)
    {n : ℕ} (_hn : 2 ≤ n) (e : (L ⧸ pCore 2 L) ≃* PSL2BinaryMatrixGroup n)
    (r : MulAut L) (hr : orderOf r = 2) (hinner : ∃ y : L, r = MulAut.conj y) :
    let c := (centerQuotientEquivTwoCore hodd).trans e
    ∃ (x g : PSL2BinaryMatrixGroup n) (t : BinaryGaloisField n),
      orderOf x = 2 ∧ MulAut.centralQuotientAction c r = MulAut.conj x ∧
      t ≠ 0 ∧ MulAut.conj g x = pi _ (uni t) ∧
      let P := rankOneParabolic e (PBorel (BinaryGaloisField n)) g
      P ≠ ⊤ ∧ r.fixedSubgroup ≤ P ∧ IsPGroup 2 r.fixedSubgroup ∧
        fixedTwoResidual L r = ⊥ ∧
        fixedTwoResidual L r = parabolicFixedTwoResidual P r := by
  dsimp only
  obtain ⟨x, hx, ha, hfix⟩ := quotient_inner_involution hodd e r hr hinner
  obtain ⟨g, t, ht, he, hCB, hC⟩ := Theory.PSL2.involution_root_geometry x hx
  refine ⟨x, g, t, hx, ha, ht, he, cover_geometry e r x g _ ?_ hfix hCB hC⟩
  intro hB
  apply PWeyl_notMem_PBorel (F := BinaryGaloisField n)
  rw [hB]
  trivial

/-- The Suzuki branch of 16.1.4(1), valid for all central covers, including
the exceptional covers of Sz(8). No splitting of the two-kernel is assumed. -/
theorem suzuki_involution_roots (hodd : pPrimeCore 2 L = ⊥)
    {m : ℕ} (hm : 1 ≤ m) (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m)
    (r : MulAut L) (hr : orderOf r = 2) :
    let c := (centerQuotientEquivTwoCore hodd).trans e
    ∃ (x g : SuzukiMatrixGroup m) (b : BinaryGaloisField (2 * m + 1)),
      orderOf x = 2 ∧ MulAut.centralQuotientAction c r = MulAut.conj x ∧
      b ≠ 0 ∧ (MulAut.conj g x).val = SuzukiRootGL m 0 b ∧
      let P := rankOneParabolic e (SuzukiBorelSubgroup m) g
      P ≠ ⊤ ∧ r.fixedSubgroup ≤ P ∧ IsPGroup 2 r.fixedSubgroup ∧
        fixedTwoResidual L r = ⊥ ∧
        fixedTwoResidual L r = parabolicFixedTwoResidual P r := by
  dsimp only
  obtain ⟨x, hx, ha, hfix⟩ := quotient_inner_involution hodd e r hr
    (suzuki_involution_inner hodd hm e r hr)
  obtain ⟨g, b, hb, he, hCB, hC⟩ := suzuki_involution_root_geometry m (by omega) x hx
  exact ⟨x, g, b, hx, ha, hb, he, cover_geometry e r x g _
    (suzukiBorelSubgroup_ne_top m (by omega)) hfix hCB hC⟩

/-- In 16.1.6 a binary PSL₂ Sylow fixer of order two induces a genuine
long-root involution on the simple quotient. -/
theorem psl2_sylow_fixing_longRoot (hodd : pPrimeCore 2 L = ⊥)
    {n : ℕ} (hn : 2 ≤ n) (e : (L ⧸ pCore 2 L) ≃* PSL2BinaryMatrixGroup n)
    (P : Sylow 2 L) (r : MulAut L) (hr : orderOf r = 2)
    (hfix : ∀ x ∈ P, r x = x) :
    ∃ x : PSL2BinaryMatrixGroup n, Theory.PSL2.IsLongRootInvolution x ∧
      MulAut.centralQuotientAction ((centerQuotientEquivTwoCore hodd).trans e) r =
        MulAut.conj x := by
  have hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) :=
    ⟨BinaryGaloisField n, inferInstance, inferInstance,
      card_binaryGaloisField n (by omega), ⟨e⟩⟩
  obtain ⟨y, -, hy⟩ := psl2_sylow_fixing_inner hodd (by omega : 0 < n) hmodel P r hfix
  obtain ⟨x, g, t, hx, ha, ht, he, -⟩ :=
    psl2_inner_involution_roots hodd hn e r hr ⟨y, hy⟩
  exact ⟨x, ⟨hx, g, t, ht, he⟩, ha⟩

/-- Every involutory automorphism of a Suzuki cover induces a long-root
involution; in particular this gives the Suzuki long-root clause of 16.1.6. -/
theorem suzuki_involution_longRoot (hodd : pPrimeCore 2 L = ⊥)
    {m : ℕ} (hm : 1 ≤ m) (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m)
    (r : MulAut L) (hr : orderOf r = 2) :
    ∃ x : SuzukiMatrixGroup m, IsSuzukiLongRootInvolution x ∧
      MulAut.centralQuotientAction ((centerQuotientEquivTwoCore hodd).trans e) r =
        MulAut.conj x := by
  obtain ⟨x, g, b, hx, ha, hb, he, -⟩ := suzuki_involution_roots hodd hm e r hr
  exact ⟨x, ⟨hx, g, b, hb, he⟩, ha⟩

end CFSG.Quasithin.Chapter16.LiePreliminaries
