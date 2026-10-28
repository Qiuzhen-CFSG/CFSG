module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.BinaryAffineModel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.BinaryUnitaryApplications

/-!
# The original binary unitary cover over its affine panel model

The order-144 alternative is now identified with the actual natural affine
semidirect product F₃² ⋊ S for a Sylow two-subgroup S of GL₂(3). The panel
bijection is equivariant and sends the origin to the original Borel coset;
the full point stabilizer is the same affine complement.

Compose the inverse group comparison with the original cover projection.
This preserves its exact kernel, centrality, odd order and stem condition,
and gives an equation on every original representative. Zero translation
is equivalent to membership in the entire original Borel, intersected with
the cover numerator. The endpoint parameter is arbitrary, and the original
amalgam isomorphism retains both inclusion squares.

The source catalogue and literal Chapter 12 application supply this
comparison in the exceptional branch without a new model premise. This
identifies a local action, not an ambient completion or a rank-two amalgam.
Excluding the affine branch from the genuine global source data, the
remaining minimality reduction and all seven marked rows remain necessary.
The earlier marked quotient and split data retain their apartment/exchange
producer and final source-assembly discharge.

Source: Fong--Seitz I (2A)--(2B), pp.7--9, (5B)--(5C), pp.25--26;
DGS Theorem D, printed p.224; Aschbacher--Smith F.1.1--3 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Matrix.GeneralLinearGroup.PrimeThreeFiveResidual
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open BinaryPanel
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)

/-- An actual affine isomorphism, its panel chart, and the same original central cover.
The last clause marks the entire original Borel intersection with the cover numerator. -/
@[expose] def BinaryAffineComparison : Prop :=
  letI := originalRadicalInClosure_normal Q e h split i
  let E := originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i
  ∃ (T : Sylow 2 PlaneGL) (a : AffineNine T ≃* localGroup Q split i) (c : Nine ≃ Panel Q i),
    c 1 = panelBase Q i ∧
    (∀ u v, a u • c v = c (u.left * planeAction 3 (u.right : PlaneGL) v)) ∧
    (SemidirectProduct.inr : T →* AffineNine T).range.map a.toMonoidHom =
      MulAction.stabilizer (localGroup Q split i) (panelBase Q i) ∧
    ∃ f : E →* AffineNine T,
      Function.Surjective f ∧
      f.ker = ((originalPanelKernel (L := L) (S := S) i).subgroupOf
        (originalLocalClosure Q e split i)).map (QuotientGroup.mk' (originalRadicalInClosure Q e split i)) ∧
      f.ker ≤ center E ∧ Nat.Coprime 2 (Nat.card f.ker) ∧ f.ker ≤ _root_.commutator E ∧
      (∀ x : originalLocalClosure Q e split i,
        (a (f (QuotientGroup.mk' _ x)) : Equiv.Perm (Panel Q i)) =
          localAction Q split i (originalLocalClosureEquiv Q e split i x)) ∧
      (∀ x : originalLocalClosure Q e split i,
        (f (QuotientGroup.mk' _ x)).left = 1 ↔ (x.val : G) ∈ commonBorel L S)

private theorem localAction_base_iff (x : localClosure Q split i) :
    localAction Q split i x (panelBase Q i) = panelBase Q i ↔ (x : X ⧸ Q.D) ∈ Q.tits.B := by
  rw [localAction_eq_panelAction,ReeSource.panelBase_eq_mk_one Q split i]
  change QuotientGroup.mk ((⟨x,(localClosure_le_parabolic Q split i) x.property⟩ :
    Q.tits.standardParabolic {Q.simple i}) * 1) = (QuotientGroup.mk 1 : Panel Q i) ↔ _
  rw [QuotientGroup.eq]
  change ((x : X ⧸ Q.D) * 1)⁻¹ * 1 ∈ Q.tits.B ↔ _
  simp only [mul_one,inv_mem_iff]

/-- The exceptional branch is the natural affine Sylow action, with the original cover marked. -/
theorem binary_affine_comparison_of_exception
    (hx : BinaryUnitaryException Q split i) : BinaryAffineComparison Q e h split i := by
  let := originalRadicalInClosure_normal Q e h split i
  let := hx.1
  obtain ⟨T,a,c,hc,ha,hstab⟩ := exists_affine_sylow_comparison
    (localGroup_two_pretransitive Q split i) hx.2.1 hx.2.2.1 (panelBase Q i)
  let f := a.symm.toMonoidHom.comp (originalProjection Q e h split i)
  have hk : f.ker = (originalProjection Q e h split i).ker := by
    ext x
    change a.symm (originalProjection Q e h split i x) = 1 ↔ originalProjection Q e h split i x = 1
    exact a.symm.map_eq_one_iff
  obtain ⟨hs,hz,ho,hd⟩ := original_central_odd_cover Q e h split i
  have hm (x : originalLocalClosure Q e split i) :
      (a (f (QuotientGroup.mk' _ x)) : Equiv.Perm (Panel Q i)) =
        localAction Q split i (originalLocalClosureEquiv Q e split i x) := by
    change (a (a.symm (originalProjection Q e h split i (QuotientGroup.mk' _ x))) : Equiv.Perm (Panel Q i)) = _
    exact (congrArg (fun g : localGroup Q split i => (g : Equiv.Perm (Panel Q i)))
      (a.apply_symm_apply (originalProjection Q e h split i (QuotientGroup.mk' _ x)))).trans
        (originalProjection_mk Q e h split i x)
  refine ⟨T,a,c,hc,ha,hstab,f,a.symm.surjective.comp hs,
    hk.trans (originalProjection_ker Q e h split i),hk ▸ hz,hk ▸ ho,hk ▸ hd,hm,?_⟩
  intro x
  have hfix : (f (QuotientGroup.mk' _ x)).left = 1 ↔
      localAction Q split i (originalLocalClosureEquiv Q e split i x) (panelBase Q i) = panelBase Q i := by
    have hh := ha (f (QuotientGroup.mk' _ x)) 1
    rw [hc,map_one,mul_one] at hh
    change (a (f (QuotientGroup.mk' _ x)) : Equiv.Perm (Panel Q i)) (panelBase Q i) = _ at hh
    rw [hm] at hh
    rw [hh,← hc]
    exact c.injective.eq_iff.symm
  rw [hfix,localAction_base_iff,originalLocalClosureEquiv_apply]
  change x.val ∈ Q.tits.B.comap (endpointMap Q e i) ↔ _
  rw [endpoint_borel_comap Q e h i]
  rfl

variable [Finite (L i)] (T : Sylow 2 (L i))
  (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
include e h hT in
/-- Every source endpoint is regular, or has the genuine marked affine degree-nine comparison. -/
theorem remainder_le_kernel_or_binary_affine :
    (simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (endpointMap Q e i) = pCore 2 (parabolic L S i)) ∨
    (BinaryUnitaryException Q split i ∧ BinaryAffineComparison Q e h split i) := by
  rcases remainder_le_kernel_or_binary_unitary_exception Q e h split i T hT with hreg | hx
  · exact Or.inl hreg
  · exact Or.inr ⟨hx,binary_affine_comparison_of_exception Q e h split i hx⟩
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The actual selected pair is regular at both ends, or its second local action
has affine Sylow coordinates with the same original central cover and full Borel. -/
theorem rankOne_global_regularity_or_binary_affine
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
    (∀ i : Fin 2, simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (MarkedLocal.endpointMap Q e i) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) i)) ∨
    (MarkedLocal.BinaryUnitaryException Q split 1 ∧ MarkedLocal.BinaryAffineComparison Q e hf split 1) := by
  let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  rcases D.rankOne_global_regularity_or_binary_unitary_exception
      h hmany hn hpsl d hTH Q e split with hr | hx
  · exact Or.inl hr
  · exact Or.inr ⟨hx,MarkedLocal.binary_affine_comparison_of_exception Q e hf split 1 hx⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
