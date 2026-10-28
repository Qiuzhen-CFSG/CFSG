module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationAction
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixCorePoint
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.PairQuotient
public import Theory.GroupTheory.PResidual.SylowCentralizer
public import Theory.GroupTheory.PResidual.TwoKernelComparison
public import Theory.GroupTheory.PResidual.TwoThreeComparison
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Embedding
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The original augmentation point parabolic and its two-rank

In the ordinary A₆ row, C_L(z)/O₂(C_L(z)) is S₃. Its two-residual is
therefore its prime-to-three residual; adjoining the original Sylow
subgroup identifies the literal L₁T with C_LT(z). This checks both the
residual convention and the actual subgroup in the source.

The five-dimensional normalizer marking supplies an action of LT with
kernel O₂(LT). The augmentation point-radical calculation proves there are
no strong offenders, and B.2.4.3 gives m₂(O₂(L₁T))=m₂(O₂(LT)) and
V≤J(O₂(L₁T)). Every quotient map, relative normality witness and module
coordinate in this application comes from the original ChosenModule and
CoreMarking. Both nonconstant weight orbits are retained.

This discharges the rank and offender preliminary for the nonsolvable
branch's augmentation Baumann argument. The characteristic-normal versus
short-block alternative, the remaining row exclusions and the comparison,
commutator and graph assembly remain with qt-d-1341-nonsolvable-source.
Earlier structural and module-classification inputs remain explicit.

Source: Aschbacher–Smith Notation 13.2.1 and 13.2.2(6), printed p.877;
application to the doubled row in 13.4.10, printed pp.907–908.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Stellmacher
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- In the ordinary row the original L1T is precisely the point centralizer
in LT. The cubic and two-residual conventions agree in the S3 quotient. -/
theorem ordinary_augmentation_point_parabolic
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) =
      (L ⊔ (T : Subgroup G)) ⊓ centralizer ({z.val} : Set G) := by
  have hcore : IsPGroup 2 (centralCore L) := by
    rw [Solvable.centralCore_eq_twoCore_of_ordinary eL]
    exact pCore_isPGroup
  obtain ⟨e⟩ := Solvable.component_centralizer_quotient D m hcore z hzL
  let C := L ⊓ centralizer ({z.val} : Set G)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))).ker
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hs : pResidual 2 (Equiv.Perm (Fin 3)) = primeToResidual 3 (Equiv.Perm (Fin 3)) := by
    apply twoResidual_eq_primeToResidual_three
    rw [IsPiGroup_iff]
    intro p hp
    rw [Nat.card_perm,Nat.card_fin] at hp
    have hp' : p.val ∣ 2 * 3 := hp
    change p.val = 2 ∨ p.val = 3
    rcases p.property.dvd_mul.mp hp' with h2 | h3
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left p.property.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left p.property.ne_one)
  have hr := twoResidual_eq_primeToResidual_three_of_two_kernel f hf hk hs
  rw [Solvable.firstCentralizerResidual_eq,←hr]
  exact embedded_pointResidual_sup_sylow T L D.sylow_normalizes_component z.val
    (Solvable.original_sylow_le_centralizer hzT)

/-- The original five-space satisfies the full-rank conclusion of13.2.2(6)
on the literal R=O2(L1T), for either escaping weight. -/
theorem ordinary_augmentation_point_rank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    ChapterB.twoRank R = ChapterB.twoRank ((L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      V ≤ elementaryAbelianMaxJ R := by
  let X := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf X
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  have hXV : X ≤ normalizer (V : Set G) :=
    sup_le D.normalizes (((structural G T L h).2.2 V D).1)
  let : U.Normal := normal_subgroupOf_of_le_normalizer hXV
  let : IsElementaryAbelian 2 U := by
    let := D.elementary
    exact IsElementaryAbelian.subgroupOf hVX
  let eu : U ≃* V := subgroupOfEquivOfLe hVX
  let e := eu.trans m.coordinate
  let zi : U := eu.symm z
  obtain ⟨q,hq,hqL,him,hker⟩ := exists_core_product_permutation D m h structural eL
  have he (x : X) (v : U) : (e (MulAut.conjNormal x v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q x) (e v).toAdd := by
    exact hq x (eu v)
  have hY : alternatingGroup (Fin 6) ≤ q.range := by
    rw [←him]
    exact (L.subgroupOf X).map_le_range q
  have hz : ¬ ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) a (e zi).toAdd = (e zi).toAdd := by
    intro hz
    apply hzL
    apply (m.mem_fixed_iff z).mpr
    apply (BinaryPermutation.core_fixed_iff_constant (by simp) _).mp
    change ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.coreRepresentation (Fin 6) a.val (e zi).toAdd = (e zi).toAdd at hz
    simpa only [e,zi,MulEquiv.trans_apply,eu.apply_symm_apply] using hz
  have hh := ChapterB.Offenders.SixCorePoint.pointRadical_rank_and_module U q e he hker hY zi hz
  let C : Subgroup X := centralizer ({zi.val} : Set X)
  have hCm : C.map X.subtype = Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) := by
    rw [ordinary_augmentation_point_parabolic D m eL z hzT hzL]
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      refine ⟨a.property,mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha)
    · rintro ⟨hx,hz⟩
      refine ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr ?_,rfl⟩
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hz)
  have hRm : (C.pCoreIn 2).map X.subtype =
      (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ _ X.subtype_injective,hCm]
  refine ⟨?_,?_⟩
  · rw [←hRm,ChapterB.twoRank_map_injective X.subtype X.subtype_injective]
    change ChapterB.twoRank (C.pCoreIn 2) = ChapterB.twoRank ((pCore 2 X).map X.subtype)
    rw [ChapterB.twoRank_map_injective X.subtype X.subtype_injective]
    exact hh.1.symm
  · have hhV := map_mono (f := X.subtype) hh.2
    rw [map_subgroupOf_eq_of_le hVX,←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,hRm] at hhV
    exact hhV
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
