module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearLayer
public import Theory.Representation.BinaryAlternatingFiveFixedPoint.Coordinates
public import Theory.Representation.SemisimpleCoinvariants.FixedFree
public import Theory.GroupTheory.ReducedNormal.Representation
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearResidualComplete

/-!
# Decomposition of the entire exceptional field-four layer

Mark the literal L/O₂(L) action on all of R₂(LT). The deleted A₅ module
is projective and injective, so its full isotypic component has a canonical
complement: the intersection of kernels of all maps to the deleted type.
Automorphism twists preserve this complement, hence the original Sylow
normalizes it. A nonzero complement meets Ω₁(Z(T)); Borel fixation and the
five-point orbit map put that point in the deleted isotypic component too,
a contradiction. Thus the entire module has positive finite-copy coordinates.
Its now-proved semisimplicity and vanishing fixed space imply [R₂(LT),L]=R₂(LT).

The source application discharges residual maximality and nonfaithfulness
using their existing producer. Only the field-four exponent and Borel
centralization remain explicit here; qt-d-1222-linear-field-four-borel owns
those inputs. This task retains the multiplicity bound and final exceptional
assembly. No chosen T-invariance, ambient semisimplicity, later Chapter 12
classification, or separate quotient marking on each copy is assumed.

Source: Aschbacher--Smith 5.1.14(3--4), 5.1.19 and I.1.6,
refs/quasithin.pdf, printed pp.638--639,643--644,408.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
namespace RankOneModule

/-- The original intrinsic reduced subgroup regarded as a binary space. -/
abbrev wholeSpace (T : Sylow 2 G) (L : Subgroup G) :=
  Additive (ReducedModule (L ⊔ (T : Subgroup G)))

/-- Restriction of the whole reduced action to the literal component. -/
def wholeComponentAction (T : Sylow 2 G) (L : Subgroup G) :
    Representation (ZMod 2) L (wholeSpace T L) :=
  (reducedRepresentation (L ⊔ (T : Subgroup G))).comp (L.inclusion le_sup_left)

/-- The component two-core centralizes the entire reduced subgroup. -/
theorem wholeComponentAction_core
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    pCore 2 L ≤ (wholeComponentAction T L).ker := by
  let J := L ⊔ (T : Subgroup G)
  let : (L.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer hTL)
  have hc : L.pCoreIn 2 ≤ J.pCoreIn 2 :=
    pCoreAmbient_mono_of_isSubnormalIn L J 2 le_sup_left
      (show (L.subgroupOf J).Normal from inferInstance).isSubnormal
  intro l hl
  apply LinearMap.ext
  intro v
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  change (l : G) * (v.toMul.val : G) * (l : G)⁻¹ = (v.toMul.val : G)
  obtain ⟨x,hx,he⟩ := hc (mem_map_of_mem L.subtype hl)
  have hh := reducedPSubgroup_le_centralizer_pCore 2 J v.toMul.property x hx
  have heq := congrArg Subtype.val hh
  change (x : G) * (v.toMul.val : G) = (v.toMul.val : G) * (x : G) at heq
  change (x : G) = (l : G) at he
  rw [he] at heq
  rw [heq,mul_inv_cancel_right]

/-- The whole action through the supplied L/O₂(L) marking. -/
def wholeMarkedAction
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    Representation (ZMod 2) (alternatingGroup (Fin 5)) (wholeSpace T L) :=
  (QuotientGroup.lift (pCore 2 L) (wholeComponentAction T L)
    (wholeComponentAction_core hTL)).comp e.symm.toMonoidHom

/-- The marked action agrees with the original quotient projection. -/
theorem wholeMarkedAction_mk
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (l : L) :
    wholeMarkedAction hTL e (e (QuotientGroup.mk' (pCore 2 L) l)) =
      wholeComponentAction T L l := by
  change QuotientGroup.lift (pCore 2 L) (wholeComponentAction T L)
    (wholeComponentAction_core hTL) (e.symm (e _)) = _
  rw [e.symm_apply_apply]
  rfl

/-- Conjugation by the original Sylow acts through an automorphism of the
same marked quotient; the vector action stays on the entire reduced group. -/
theorem wholeMarkedAction_sylow_covariance
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (t : T) :
    ∃ a : MulAut (alternatingGroup (Fin 5)), ∀ g v,
      reducedRepresentation (L ⊔ (T : Subgroup G)) ⟨t,Subgroup.mem_sup_right t.property⟩
        (wholeMarkedAction hTL e g v) =
      wholeMarkedAction hTL e (a g)
        (reducedRepresentation (L ⊔ (T : Subgroup G)) ⟨t,Subgroup.mem_sup_right t.property⟩ v) := by
  let α := L.normalizerMonoidHom ⟨t,hTL t.property⟩
  have hα : (pCore 2 L).map α.toMonoidHom = pCore 2 L :=
    characteristic_iff_map_eq.mp inferInstance α
  let β := QuotientGroup.congr (pCore 2 L) (pCore 2 L) α hα
  let a := e.symm.trans (β.trans e)
  refine ⟨a, ?_⟩
  intro g v
  obtain ⟨l,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
  have ha : a (e (QuotientGroup.mk' (pCore 2 L) l)) =
      e (QuotientGroup.mk' (pCore 2 L) (α l)) := by
    change e (β (e.symm (e _))) = _
    rw [e.symm_apply_apply]
    exact congrArg e (QuotientGroup.congr_mk' (pCore 2 L) (pCore 2 L) α hα l)
  dsimp only [Function.comp_apply]
  rw [ha,wholeMarkedAction_mk,wholeMarkedAction_mk]
  let ρ := reducedRepresentation (L ⊔ (T : Subgroup G))
  change ρ _ (ρ _ v) = ρ _ (ρ _ v)
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 2
  apply Subtype.ext
  change (t : G) * (l : G) = (α l : G) * (t : G)
  rw [normalizerMonoidHom_apply_apply_coe]
  group

/-- The canonical deleted-type complement is normalized by the actual Sylow. -/
theorem wholeMarkedAction_reject_sylow_stable
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (t : T)
    (v : wholeSpace T L)
    (hv : v ∈ Representation.typeReject (wholeMarkedAction hTL e)
      (BinaryPermutation.alternatingCoreRepresentation (Fin 5))) :
    reducedRepresentation (L ⊔ (T : Subgroup G)) ⟨t,Subgroup.mem_sup_right t.property⟩ v ∈
      Representation.typeReject (wholeMarkedAction hTL e)
        (BinaryPermutation.alternatingCoreRepresentation (Fin 5)) := by
  obtain ⟨a,ha⟩ := wholeMarkedAction_sylow_covariance hTL e t
  obtain ⟨c,hc⟩ := BinaryAlternatingFiveFixedPoint.core_twist a
  exact Representation.typeReject_stable_of_covariance _ _ _ a c ha hc v hv

/-- Vanishing of the literal group centralizer is vanishing of invariants
for the entire marked representation. -/
theorem wholeMarkedAction_invariants_eq_bot
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hfixed : wholeReduced T L ⊓ centralizer (L : Set G) = ⊥) :
    (wholeMarkedAction hTL e).invariants = ⊥ := by
  apply bot_unique
  intro v hv
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  apply mem_bot.mp
  rw [← hfixed]
  refine ⟨mem_map_of_mem _ v.toMul.property, ?_⟩
  intro l hl
  have hh := hv (e (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩))
  rw [wholeMarkedAction_mk] at hh
  have hh' := congrArg (fun x : wholeSpace T L => (x.toMul.val : G)) hh
  change l * (v.toMul.val : G) * l⁻¹ = (v.toMul.val : G) at hh'
  exact mul_inv_eq_iff_eq_mul.mp hh'

/-- Borel fixation eliminates the canonical complement on the entire
reduced group. A nonzero complement would contain a Sylow-central point,
which the five-point orbit map places in the complementary deleted span. -/
theorem wholeMarkedAction_typeReject_eq_bot
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hfixed : wholeReduced T L ⊓ centralizer (L : Set G) = ⊥)
    (hB : Chapter6.Source.RankOneGeneric.localBorel T L ≤
      Chapter6.Source.RankOneGeneric.omegaCentralizer T) :
    Representation.typeReject (wholeMarkedAction hTL e)
      (BinaryPermutation.alternatingCoreRepresentation (Fin 5)) = ⊥ := by
  let J := L ⊔ (T : Subgroup G)
  let ρ := wholeMarkedAction hTL e
  let S := Representation.typeReject ρ
    (BinaryPermutation.alternatingCoreRepresentation (Fin 5))
  have hσ := wholeMarkedAction_invariants_eq_bot hTL e hfixed
  have hcompl := BinaryAlternatingFiveFixedPoint.isCompl_core_typeSpan_typeReject ρ
  by_contra hs
  have hS0 : S.toSubmodule ≠ ⊥ := fun hz =>
    hs (Subrepresentation.toSubmodule_injective hz)
  let W := ReducedNormal.subspaceImage J S.toSubmodule
  have hW0 : W ≠ ⊥ := ReducedNormal.subspaceImage_ne_bot J S.toSubmodule hS0
  have hWT : W ≤ (T : Subgroup G) :=
    (ReducedNormal.subspaceImage_le_reduced J S.toSubmodule).trans wholeReduced_le_sylow
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) := by
    apply ReducedNormal.subspaceImage_normalizes J (T : Subgroup G) le_sup_right
    apply BinaryOffender.le_subspaceStabilizer
    intro t ht v hv
    exact wholeMarkedAction_reject_sylow_stable hTL e ⟨t.val,ht⟩ v hv
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hW0 hWT hTW)
  have hzW : (z : G) ∈ W := z.property.1
  have hzΩ : (z : G) ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    let := ReducedNormal.subspaceImage_elementary J S.toSubmodule
    exact ⟨hWT hzW, elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) hzW,
      z.property.2.2⟩
  obtain ⟨w,⟨u,hu,rfl⟩,huz⟩ := hzW
  change (u.val : G) = (z : G) at huz
  let v : wholeSpace T L := Additive.ofMul u
  have hv0 : v ≠ 0 := by
    intro hz
    apply hz1
    apply Subtype.ext
    rw [← huz]
    have hu0 : u = 1 := congrArg Additive.toMul hz
    rw [hu0]
    rfl
  let f : L →* alternatingGroup (Fin 5) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  let Q := P.mapSurjective hf
  obtain ⟨i,hi⟩ :=
    Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer Q
  have hN : (normalizer (P : Set L)).map f =
      MulAction.stabilizer (alternatingGroup (Fin 5)) i :=
    (P.normalizer_map_surjective f hf).trans hi
  have hvfix : ∀ b : alternatingGroup (Fin 5), b.val i = i → ρ b v = v := by
    intro b hb
    obtain ⟨l,hl,hfl⟩ := hN.ge hb
    rw [← hfl]
    change wholeMarkedAction hTL e (e (QuotientGroup.mk' (pCore 2 L) l)) v = v
    rw [wholeMarkedAction_mk]
    have hlB : (l : G) ∈ Chapter6.Source.RankOneGeneric.localBorel T L := by
      rw [Chapter6.Source.RankOneGeneric.localBorel_eq_map, ← hP]
      exact mem_map_of_mem L.subtype hl
    have hc := hB hlB z hzΩ
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (l : G) * (u.val : G) * (l : G)⁻¹ = (u.val : G)
    rw [huz]
    rw [← hc,mul_inv_cancel_right]
  obtain ⟨F,_,hvF⟩ := BinaryAlternatingFiveFixedPoint.core_embedding_of_point_fixed
    ρ v hv0 hσ i hvfix
  have hvspan : v ∈ typeSpan ρ (BinaryPermutation.alternatingCoreRepresentation (Fin 5)) :=
    (show F.range ≤ typeSpan ρ _ from le_iSup _ F) hvF
  have hz : v = 0 := hcompl.disjoint.le_bot ⟨hvspan,hu⟩
  exact hv0 hz

/-- Finite copies on all of R₂(LT), with a single fixed quotient marking. -/
theorem wholeMarkedAction_exists_coordinates
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hfixed : wholeReduced T L ⊓ centralizer (L : Set G) = ⊥)
    (hB : Chapter6.Source.RankOneGeneric.localBorel T L ≤
      Chapter6.Source.RankOneGeneric.omegaCentralizer T) :
    ∃ k : ℕ, ∃ c : wholeSpace T L ≃ₗ[ZMod 2]
        (Fin k → BinaryPermutation.natural (Fin 5)),
      ∀ (l : L) v, c (wholeComponentAction T L l v) =
        Chapter6.Source.a5Copies k (e (QuotientGroup.mk' (pCore 2 L) l)) (c v) := by
  obtain ⟨k,c,hc⟩ := BinaryAlternatingFiveFixedPoint.exists_natural_coordinates_of_typeReject_eq_bot
    (wholeMarkedAction hTL e) (wholeMarkedAction_typeReject_eq_bot hTL e hfixed hB)
  refine ⟨k,c,fun l v => ?_⟩
  have hh := hc (e (QuotientGroup.mk' (pCore 2 L) l)) v
  rw [wholeMarkedAction_mk] at hh
  exact hh

/-- The inclusion from the intrinsic reduced group to its ambient image. -/
def wholeSpaceEquiv (T : Sylow 2 G) (L : Subgroup G) :
    Multiplicative (wholeSpace T L) ≃* wholeReduced T L :=
  (ReducedModule (L ⊔ (T : Subgroup G))).equivMapOfInjective
    (L ⊔ (T : Subgroup G)).subtype Subtype.val_injective

omit [Finite G] in
/-- Coordinates on the entire intrinsic module give the literal ambient
conjugation model, retaining the supplied L/O₂(L) marking. -/
theorem whole_model_of_coordinates
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) {k : ℕ}
    (c : wholeSpace T L ≃ₗ[ZMod 2] (Fin k → BinaryPermutation.natural (Fin 5)))
    (hc : ∀ (l : L) v, c (wholeComponentAction T L l v) =
      Chapter6.Source.a5Copies k (e (QuotientGroup.mk' (pCore 2 L) l)) (c v)) :
    Chapter6.Source.IsConjugationModel L (wholeReduced T L) (Chapter6.Source.a5Copies k) := by
  let b := wholeSpaceEquiv T L
  let f := b.symm.trans c.toAddEquiv.toMultiplicative
  refine ⟨e,f,?_⟩
  intro l v
  let v' : wholeSpace T L := (b.symm v).toAdd
  have hv : (v'.toMul.val : G) = (v : G) :=
    congrArg Subtype.val (b.apply_symm_apply v)
  change (b (Multiplicative.ofAdd (c.symm
    (Chapter6.Source.a5Copies k (e (QuotientGroup.mk' (pCore 2 L) l)) (c v')))) : G) = _
  rw [← hc, c.symm_apply_apply]
  change (l : G) * (v'.toMul.val : G) * (l : G)⁻¹ = _
  rw [hv]

/-- In the field-four Borel branch the whole reduced group is its literal
L-commutator layer. Semisimplicity is proved by canonical splitting first. -/
theorem wholeReduced_eq_commutatorLayer_of_marked_borel
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hfixed : wholeReduced T L ⊓ centralizer (L : Set G) = ⊥)
    (hB : Chapter6.Source.RankOneGeneric.localBorel T L ≤
      Chapter6.Source.RankOneGeneric.omegaCentralizer T) :
    wholeReduced T L = commutatorLayer T L := by
  let J := L ⊔ (T : Subgroup G)
  let σ := wholeMarkedAction hTL e
  let : IsSemisimpleModule (ZMod 2)[alternatingGroup (Fin 5)] σ.asModule :=
    BinaryAlternatingFiveFixedPoint.semisimple_of_typeReject_eq_bot σ
      (wholeMarkedAction_typeReject_eq_bot hTL e hfixed hB)
  have hc : Coinvariants.ker σ = ⊤ :=
    coinvariants_eq_top_of_semisimple_of_invariants_eq_bot σ
      (wholeMarkedAction_invariants_eq_bot hTL e hfixed)
  have hm : Coinvariants.ker σ ≤ BinaryOffender.subspaceCommutator
      (ReducedNormal.representation J) ⊤ (L.subgroupOf J) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    obtain ⟨l,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
    change wholeMarkedAction hTL e (e (QuotientGroup.mk' (pCore 2 L) l)) v - v ∈ _
    rw [wholeMarkedAction_mk]
    exact Submodule.subset_span ⟨⟨l,Subgroup.mem_sup_left l.property⟩,l.property,v,
      Submodule.mem_top,rfl⟩
  rw [hc] at hm
  have himage : ReducedNormal.subspaceImage J ⊤ = wholeReduced T L := by
    apply le_antisymm (ReducedNormal.subspaceImage_le_reduced J ⊤)
    rintro _ ⟨u,hu,rfl⟩
    exact ⟨u,⟨⟨u,hu⟩,by trivial,rfl⟩,rfl⟩
  have he := ReducedNormal.subspaceImage_eq_commutator J ⊤ L le_sup_left
    (BinaryOffender.le_subspaceStabilizer _ _ (by intros; trivial)) (top_unique hm)
  rwa [himage] at he

end RankOneModule
namespace ChosenModule
open Chapter6.Source.RankOneGeneric

/-- The whole-layer finite-copy decomposition in the original exceptional
source setup. Only the independently owned field-four and Borel conclusions
remain explicit; no chosen T-invariance or semisimplicity is assumed. -/
theorem rankOne_linear_layer_decomposition_of_borel
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    {n : ℕ} (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hn : n = 2)
    (hB : localBorel T L ≤ omegaCentralizer T) :
    RankOneModule.wholeReduced T L = RankOneModule.commutatorLayer T L ∧
      ∃ k : ℕ, 0 < k ∧ Chapter6.Source.IsConjugationModel L
        (RankOneModule.commutatorLayer T L) (Chapter6.Source.a5Copies k) := by
  obtain ⟨F,_,_,hF,⟨f⟩⟩ := hpsl
  have hfour : Nat.card F = 4 := by simpa [hn] using hF
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hfour
  let e := f.trans a
  have hfixed := D.rankOne_whole_fixed_eq_bot_of_linear_source h hH hK hnf
  have heq := RankOneModule.wholeReduced_eq_commutatorLayer_of_marked_borel
    D.sylow_normalizes_component e hfixed hB
  obtain ⟨k,c,hc⟩ := RankOneModule.wholeMarkedAction_exists_coordinates
    D.sylow_normalizes_component e hfixed hB
  have hk : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hz
    subst k
    have hvzero (v : RankOneModule.wholeSpace T L) : v = 0 :=
      c.injective (Subsingleton.elim _ _)
    apply D.ne_bot
    apply bot_unique
    intro x hx
    obtain ⟨u,hu,rfl⟩ := D.le_reduced hx
    exact congrArg (fun v : RankOneModule.wholeSpace T L => (v.toMul.val : G))
      (hvzero (Additive.ofMul ⟨u,hu⟩))
  refine ⟨heq,k,hk,?_⟩
  rw [← heq]
  exact RankOneModule.whole_model_of_coordinates e c hc
/-- Original Chapter 12 application with both residual assertions discharged.
The independent field-four/Borel producer supplies exactly the last two inputs;
this owner still has to bound the positive whole-layer multiplicity. -/
theorem rankOne_linear_layer_decomposition
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {n : ℕ} (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hn : n = 2)
    (hB : localBorel T L ≤ omegaCentralizer T) :
    RankOneModule.wholeReduced T L = RankOneModule.commutatorLayer T L ∧
      ∃ k : ℕ, 0 < k ∧ Chapter6.Source.IsConjugationModel L
        (RankOneModule.commutatorLayer T L) (Chapter6.Source.a5Copies k) := by
  obtain ⟨hK,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  exact D.rankOne_linear_layer_decomposition_of_borel h.toHypothesis1221 hH hK hnf hpsl hn hB

end ChosenModule

end CFSG.Quasithin.Chapter12.Section02
