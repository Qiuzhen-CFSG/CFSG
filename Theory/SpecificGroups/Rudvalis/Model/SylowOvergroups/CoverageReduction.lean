module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Definitions
public import Theory.GroupTheory.CoatomPCoreNormalizer

/-!
# Local obligations for the Rudvalis Sylow-overgroup cover

The exhaustive cover splits into two mathematical inputs: odd-index maximal
subgroups have nontrivial intrinsic two-core, and maximal normalizers of
nontrivial two-radical subgroups have the two specified isomorphism types.
The first input excludes the nonlocal case; the second is a local-normalizer
calculation on the actual degree-4060 carrier. Neither input is proved here.

When the ambient two-core is trivial, a maximal subgroup with nontrivial
two-core equals the normalizer of its core's ambient image. That image is
two-radical, so the local cover applies to the subgroup itself.

Source: Aschbacher--Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528), citing Aschbacher, *Overgroups of Sylow subgroups in sporadic
groups*, Memoirs AMS 60 (1986), no.343. GLS3 Table 5.3r supplies local
structures; it does not by itself prove either exhaustive assertion below.
-/

namespace Rudvalis.SylowOvergroups

/-- The nonlocal case to exclude. The two-core is taken inside M. -/
@[expose] public def OddIndexMaximalTwoCore : Prop :=
  ∀ M : Subgroup Model, IsCoatom M → ¬ 2 ∣ M.index → pCore 2 M ≠ ⊥

/-- Coverage restricted to maximal normalizers of nontrivial two-radical
subgroups. Radicality uses the ambient image of the intrinsic two-core.
This is a separate proof obligation, with actual multiplicative equivalences. -/
@[expose] public def OddIndexMaximalRadicalCover : Prop :=
  ∀ U : Subgroup Model, U.IsPRadical 2 →
    IsCoatom (Subgroup.normalizer (U : Set Model)) →
    ¬ 2 ∣ (Subgroup.normalizer (U : Set Model)).index →
    Nonempty (Subgroup.normalizer (U : Set Model) ≃* max4) ∨
      Nonempty (Subgroup.normalizer (U : Set Model) ≃* max6)

/-- Nontrivial two-cores and radical-normalizer coverage together give the
full maximal-subgroup cover. Neither premise can be omitted from assembly. -/
public theorem oddIndexMaximalCover_of_twoCore_of_radicalCover
    (hG : pCore 2 Model = ⊥)
    (hcore : OddIndexMaximalTwoCore)
    (hlocal : OddIndexMaximalRadicalCover) : OddIndexMaximalCover := by
  intro M hM hodd
  have hc := hcore M hM hodd
  have hn := Subgroup.normalizer_map_pCore_eq_of_isCoatom M hM hG hc
  have hr := Subgroup.isPRadical_map_pCore_of_isCoatom M hM hG hc
  have hN := hlocal ((pCore 2 M).map M.subtype) hr (hn.symm ▸ hM) (hn.symm ▸ hodd)
  exact hN.imp
    (Nonempty.map fun e => (MulEquiv.subgroupCongr hn).symm.trans e)
    (Nonempty.map fun e => (MulEquiv.subgroupCongr hn).symm.trans e)

end Rudvalis.SylowOvergroups
