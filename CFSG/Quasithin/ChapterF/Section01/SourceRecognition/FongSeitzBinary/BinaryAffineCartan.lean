module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.AffineCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RegularUnitaryApplications

/-!
# The full original affine endpoint and its Cartan

The exceptional source local group is the whole faithful endpoint action,
by AffineCartan. Compose its actual affine isomorphism with the original
endpoint marking. The resulting surjection has exactly the original full
panel kernel. Its panel chart is equivariant, and zero translation is
membership in the entire original Borel. Thus the affine comparison now
applies to the full endpoint, in addition to the earlier central odd stem
cover of the root closure.

The same marked Cartan pulls back into that original kernel and centralizes
the actual smaller root-generated subgroup. The literal Chapter 12 consumer
retains the old central cover and the even-Weyl restriction while adding
these new conclusions. Both endpoint squares and the full middle map are
those of the supplied original amalgam marking; no quotient is replaced.

Source: Fong--Seitz I, (2A)(VI), pp.8--9, and the first step of (5I), p.31;
DGS Theorem D, p.224; Aschbacher--Smith F.1.1--3 and 12.2.2. This does not
exclude the remaining even affine branch. Its subsequent global module
argument and the exhaustive seven marked rows remain with source recognition.
The earlier quotient/split data retain the apartment/exchange producer and
final source-assembly discharge.
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

/-- The entire original endpoint, with its exact panel kernel and full Borel,
acts as the natural affine group. -/
@[expose] def BinaryAffineEndpointComparison : Prop :=
  ∃ (T : Sylow 2 PlaneGL) (a : AffineNine T ≃* (endpointAction Q i).range)
    (c : Nine ≃ Panel Q i),
    c 1 = panelBase Q i ∧
    (∀ u v, a u • c v = c (u.left * planeAction 3 (u.right : PlaneGL) v)) ∧
    ∃ f : parabolic L S i →* AffineNine T,
      Function.Surjective f ∧
      f.ker = originalPanelKernel (L := L) (S := S) i ∧
      (∀ x, (a (f x) : Equiv.Perm (Panel Q i)) = endpointAction Q i (endpoint Q e i x)) ∧
      (∀ x, (f x).left = 1 ↔ (x : G) ∈ commonBorel L S)

include h

/-- The full endpoint comparison follows from the exceptional local alternative. -/
theorem binary_affine_endpoint_comparison
    (hx : BinaryUnitaryException Q split i) : BinaryAffineEndpointComparison Q e i := by
  let := hx.1
  obtain ⟨T,b,c,hc,hb,hstab⟩ := exists_affine_sylow_comparison
    (localGroup_two_pretransitive Q split i) hx.2.1 hx.2.2.1 (panelBase Q i)
  let μ := MulEquiv.subgroupCongr
    (endpoint_image_eq_localGroup_of_affine Q split i hx.1 hx.2.1 hx.2.2.1)
  let a : AffineNine T ≃* (endpointAction Q i).range := b.trans μ.symm
  let g := (endpointAction Q i).rangeRestrict.comp (endpoint Q e i).toMonoidHom
  let f := a.symm.toMonoidHom.comp g
  have hf : Function.Surjective f := a.symm.surjective.comp
    ((endpointAction Q i).rangeRestrict_surjective.comp (endpoint Q e i).surjective)
  have hm (x : parabolic L S i) :
      (a (f x) : Equiv.Perm (Panel Q i)) = endpointAction Q i (endpoint Q e i x) := by
    change (a (a.symm (g x)) : Equiv.Perm (Panel Q i)) = _
    rw [a.apply_symm_apply]
    rfl
  have ha (u : AffineNine T) (v : Nine) :
      a u • c v = c (u.left * planeAction 3 (u.right : PlaneGL) v) := hb u v
  refine ⟨T,a,c,hc,ha,f,hf,?_,hm,?_⟩
  · rw [← originalPanelKernel_comap Q e h i]
    ext x
    change a.symm (g x) = 1 ↔ endpointMap Q e i x ∈ localKernel Q i
    rw [a.symm.map_eq_one_iff]
    change g x = 1 ↔ endpoint Q e i x ∈
      (localKernel Q i).subgroupOf (Q.tits.standardParabolic {Q.simple i})
    rw [localKernel_subgroupOf,normalCore_eq_ker]
    exact Subtype.ext_iff
  · intro x
    have hh := ha (f x) 1
    rw [hc,map_one,mul_one] at hh
    change (a (f x) : Equiv.Perm (Panel Q i)) (panelBase Q i) = _ at hh
    rw [hm] at hh
    have hfix : (f x).left = 1 ↔
        endpointAction Q i (endpoint Q e i x) (panelBase Q i) = panelBase Q i := by
      rw [hh,← hc]
      exact c.injective.eq_iff.symm
    rw [hfix,ReeSource.panelBase_eq_mk_one Q split i]
    change QuotientGroup.mk (endpoint Q e i x * 1) = (QuotientGroup.mk 1 : Panel Q i) ↔ _
    rw [QuotientGroup.eq]
    simp only [mul_one,inv_mem_iff]
    change x ∈ Q.tits.B.comap (endpointMap Q e i) ↔ _
    rw [endpoint_borel_comap Q e h i]
    rfl

/-- The same original Cartan lies in the full panel kernel and centralizes
the actual original smaller root closure, at either endpoint. -/
theorem binary_affine_original_cartan
    (hx : BinaryUnitaryException Q split i) :
    (Q.tits.B ⊓ Q.tits.N).comap (endpointMap Q e i) ≤
      originalPanelKernel (L := L) (S := S) i ∧
    (Q.tits.B ⊓ Q.tits.N).comap (endpointMap Q e i) ≤
      centralizer (originalRankOne Q e split i : Set (parabolic L S i)) := by
  constructor
  · rw [← originalPanelKernel_comap Q e h i]
    exact comap_mono (torus_le_kernel_of_affine Q split i hx.1 hx.2.1 hx.2.2.1)
  · intro t ht
    apply mem_centralizer_iff.mpr
    intro r hr
    apply (Q.tits.standardParabolic {Q.simple i}).subtype_injective.comp
      (endpoint Q e i).injective
    change endpointMap Q e i (r*t) = endpointMap Q e i (t*r)
    rw [map_mul,map_mul]
    exact mem_centralizer_iff.mp
      (torus_centralizes_rankOne_of_affine Q split i hx.1 hx.2.1 hx.2.2.1 ht)
      _ hr

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The literal Chapter 12 affine remainder has the full endpoint action and
its actual Cartan kernel and centralizer, with both original markings retained. -/
theorem rankOne_global_regularity_or_even_affine_cartan
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
    (MarkedLocal.BinaryUnitaryException Q split 1 ∧
      MarkedLocal.BinaryAffineComparison Q e hf split 1 ∧ Even (rotationOrder Q) ∧
      MarkedLocal.BinaryAffineEndpointComparison Q e 1 ∧
      (Q.tits.B ⊓ Q.tits.N).comap (MarkedLocal.endpointMap Q e 1) ≤
        MarkedLocal.originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) 1 ∧
      (Q.tits.B ⊓ Q.tits.N).comap (MarkedLocal.endpointMap Q e 1) ≤
        centralizer (MarkedLocal.originalRankOne Q e split 1 : Set (parabolic ![L,R] (Global.sourceS L H) 1))) := by
  let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  rcases D.rankOne_global_regularity_or_even_binary_affine h hmany hn hpsl d hTH Q e split with hr | hx
  · exact Or.inl hr
  · exact Or.inr ⟨hx.1,hx.2.1,hx.2.2,
      MarkedLocal.binary_affine_endpoint_comparison Q e hf split 1 hx.1,
      MarkedLocal.binary_affine_original_cartan Q e hf split 1 hx.1⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
