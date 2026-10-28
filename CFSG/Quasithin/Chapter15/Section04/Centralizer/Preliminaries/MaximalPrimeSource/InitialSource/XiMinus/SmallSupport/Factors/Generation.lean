module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.SmallSupport.Factors.Frattini
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.SmallSupport
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDecomposition
public import Theory.GroupTheory.Fitting.PrimeSubgroups
public import Theory.ElementaryAbelian.CommutingFamily

/-!
# Canonical five-factors generate the actual odd image

Every canonical order-five factor lies in O₅(H)=P. Their join is normal
in H, so its image in the original Xi Frattini quotient is T-invariant.
D.2.13 supplies a nontrivial moved commutator in this family; coprime
detection makes its image nonzero. Xi irreducibility and Frattini
nongeneration prove that the canonical join is exactly P. D.2.12 then
makes P elementary abelian, and the original Frattini projection injective.
No prescribed decomposition or factor permutation is assumed.
Source: Aschbacher--Smith, 3.2.13, printed pp.584--585, using D.2.12--13.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
variable {G : Type*} [Group G] [Finite G] {T X : Subgroup G}

@[expose] def sourceFiveGroup (hX : X ∈ Chapter1.Xi G T) :
    Subgroup (sourceActionGroup hX) := sSup (sourceFiveFactors hX)

omit [Finite G] in
theorem sourceFiveGroup_normal (hX : X ∈ Chapter1.Xi G T) :
    (sourceFiveGroup hX).Normal := by
  let := Representation.BinaryGroupAction.action (sourceRepresentation hX)
  change (ChapterD.smallSupportGroup (sourceActionGroup hX)
    (Multiplicative (Additive (sourceModule T X))) 2).Normal
  infer_instance

theorem sourceFiveGroup_le_oddImage (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hp : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X)) :
    sourceFiveGroup hX ≤ sourceOddImage hX := by
  rw [sourceOddImage_eq_pCore hX hT (by decide : Odd 5) hp]
  apply sSup_le
  intro D hD
  exact IsPGroup.le_pCore_of_le_fitting (IsPGroup.of_card (p := 5) (n := 1)
    (by simpa only [pow_one] using hD.2.1)) hD.1

omit [Finite G] in
theorem sourceFiveGroup_frattini_invariant (hX : X ∈ Chapter1.Xi G T)
    (hk : SourceKernelInFrattini hX) :
    ∀ t : T, ∀ a ∈ ((sourceFiveGroup hX).subgroupOf (sourceOddImage hX)).map
      (sourceFrattiniProjection hX hk),
      Chapter1.xiFrattiniAction T X hX.invariant t a ∈
        ((sourceFiveGroup hX).subgroupOf (sourceOddImage hX)).map
          (sourceFrattiniProjection hX hk) := by
  let J := sourceGroup T X
  let P := sourceOddImage hX
  let K := sourceFiveGroup hX
  let := sourceFiveGroup_normal hX
  let := conjMulDistribMulActionOfLeNormalizer T X hX.invariant
  intro t a ha
  obtain ⟨y, hy, rfl⟩ := ha
  obtain ⟨x, rfl⟩ := sourceOddProjection_surjective hX y
  let tJ : J := ⟨t.val, mem_sup_right t.property⟩
  let i : X →* J := inclusion (show X ≤ J from le_sup_left)
  let q := sourceActionProjection hX
  have hc : ((sourceOddProjection hX (t • x) : P) : sourceActionGroup hX) =
      q tJ * ((sourceOddProjection hX x : P) : sourceActionGroup hX) * (q tJ)⁻¹ := by
    change q (i (t • x)) = q tJ * q (i x) * (q tJ)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg q
    apply Subtype.ext
    rfl
  have hm : sourceOddProjection hX (t • x) ∈ K.subgroupOf P := by
    change ((sourceOddProjection hX (t • x) : P) : sourceActionGroup hX) ∈ K
    rw [hc]
    exact (show K.Normal from inferInstance).conj_mem _ hy (q tJ)
  refine ⟨sourceOddProjection hX (t • x), hm, ?_⟩
  rw [sourceFrattiniProjection_apply, sourceFrattiniProjection_apply]
  unfold Chapter1.xiFrattiniAction
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, quotientAut_apply_mk,
    quotientAut_apply_mk]
  rfl

theorem sourceFiveGroup_eq_oddImage (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hred : IsPReduced 2 (sourceModule T X))
    (hk : SourceKernelInFrattini hX)
    (hratio : Representation.BinaryOffender.cubicRatio (sourceRepresentation hX) ≤ 2)
    (hp : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X)) :
    sourceFiveGroup hX = sourceOddImage hX := by
  let P := sourceOddImage hX
  let K := sourceFiveGroup hX
  have hKP : K ≤ P := sourceFiveGroup_le_oddImage hX hT hp
  have hcore : pCore 5 (sourceActionGroup hX) = P :=
    (sourceOddImage_eq_pCore hX hT (by decide : Odd 5) hp).symm
  obtain ⟨A, hA, _, hn, _, hf⟩ := source_five_canonical_support hX hT hred hratio hp
  rw [hcore] at hn hf
  have hA2 : IsPGroup 2 A := by
    let := hA.1.2.1.2
    exact IsElementaryAbelian.isPGroup 2 A
  have hnon := source_moved_frattini_image_ne_bot hX hk hp A hA2 hn
  have hD : ⁅P, A⁆ ≤ K := le_sSup hf
  have hgen : K.subgroupOf P = ⊤ := by
    apply sourceOddImage_generate_of_invariant_image hX hk (K.subgroupOf P)
    · intro he
      apply hnon
      exact le_bot_iff.mp ((map_mono (comap_mono hD)).trans he.le)
    · exact sourceFiveGroup_frattini_invariant hX hk
  have hm := congrArg (Subgroup.map P.subtype) hgen
  rwa [map_subgroupOf_eq_of_le hKP, ← MonoidHom.range_eq_map, range_subtype] at hm

theorem sourceFiveGroup_elementary (hX : X ∈ Chapter1.Xi G T) :
    IsElementaryAbelian 5 (sourceFiveGroup hX) := by
  let := sourceModule_normal hX
  let H := sourceActionGroup hX
  let W := Multiplicative (Additive (sourceModule T X))
  let := Representation.BinaryGroupAction.action (sourceRepresentation hX)
  let : IsElementaryAbelian 2 W := Representation.BinaryGroupAction.elementary
  let : FaithfulSMul H W := Representation.BinaryGroupAction.faithful
    (sourceRepresentation hX) (Representation.NormalElementaryQuotient.representation_injective _ _ _ _)
  let : ∀ D : sourceFiveFactors hX, IsElementaryAbelian 5 D.val := fun D => by
    let : IsCyclic D.val := ChapterD.smallSupportFactor_isCyclic (Or.inr rfl) D.property
    refine { exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    simpa only [D.property.2.1] using (pow_card_eq_one' (x := x))
  change IsElementaryAbelian 5 ↥(sSup (sourceFiveFactors hX))
  rw [sSup_eq_iSup']
  apply IsElementaryAbelian.iSup_of_le_centralizer
  intro D E
  exact ChapterD.smallSupportFactors_commutingFamily (G := H) (V := W)
    (Or.inr rfl) D.val D.property E.val E.property

theorem sourceOddImage_elementary (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hred : IsPReduced 2 (sourceModule T X))
    (hk : SourceKernelInFrattini hX)
    (hratio : Representation.BinaryOffender.cubicRatio (sourceRepresentation hX) ≤ 2)
    (hp : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X)) :
    IsElementaryAbelian 5 (sourceOddImage hX) :=
  sourceFiveGroup_eq_oddImage hX hT hred hk hratio hp ▸ sourceFiveGroup_elementary hX

theorem sourceFrattiniProjection_injective (hX : X ∈ Chapter1.Xi G T)
    (hT : IsPGroup 2 T) (hred : IsPReduced 2 (sourceModule T X))
    (hk : SourceKernelInFrattini hX)
    (hratio : Representation.BinaryOffender.cubicRatio (sourceRepresentation hX) ≤ 2)
    (hp : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X)) :
    Function.Injective (sourceFrattiniProjection hX hk) := by
  let := sourceOddImage_elementary hX hT hred hk hratio hp
  let : Fact (IsPGroup 5 (sourceOddImage hX)) := ⟨sourceOddImage_isPGroup hX hp⟩
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [sourceFrattiniProjection_ker_eq_frattini hX hk,
    frattini_eq_bot_of_isElementaryAbelian (p := 5)]

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
