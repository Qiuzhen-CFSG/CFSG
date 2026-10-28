module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.MultiplicativeNormalizer
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointAction
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.ConjugateSpanOrder
public import Mathlib.GroupTheory.Index
public import CFSG.Quasithin.Chapter14.Section02.SourceSetup
public import Theory.ElementaryAbelian.Injective
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Rank three in the original natural alternating-six branch

The four-dimensional block module has trivial central projection kernel.
The normalizer of its actual natural alternating action is the symmetric
six-letter action, so every automorphism of the block preserves the same
nondegenerate alternating form. The marked source plane lies in the
perpendicular of its marked point. The second parabolic centralizes that
point and moves the plane, hence its literal conjugate span has order eight.

The final source application derives point centrality from original 14.2.3
and block normalization from the selected component's normality. It retains
the compatible block-module and flag markings; their construction belongs
to the C.2.7 model comparison. Neither the other module branches nor the full
14.6.10(5) conclusion is asserted here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 14.6.10(5),
printed p.1029, the four-dimensional A₆ case; module convention C.1.7 and B.3.
-/

@[expose] public noncomputable section
open Subgroup BinaryPermutation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.RankThreeNaturalSix
open ChapterC Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry NaturalPairing
abbrev action := (naturalMulAction (Fin 6)).comp (alternatingGroup (Fin 6)).subtype

private theorem plane_le_hyperplane : canonicalPlane ≤ PointAction.Hyperplane := by
  intro v hv x hx
  obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hv
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hx
  have h01 : form (pairVector 4 5) (pairVector 0 1) = 0 := by
    change naturalPairing (Fin 6) (coreToNatural (Fin 6) ⟨Pi.single 4 1 + Pi.single 5 1, by simp [mem_core]; decide⟩) (coreToNatural (Fin 6) ⟨Pi.single 0 1 + Pi.single 1 1, by simp [mem_core]; decide⟩) = 0
    rw [naturalPairing_apply_core]
    decide
  have h23 : form (pairVector 4 5) (pairVector 2 3) = 0 := by
    change naturalPairing (Fin 6) (coreToNatural (Fin 6) ⟨Pi.single 4 1 + Pi.single 5 1, by simp [mem_core]; decide⟩) (coreToNatural (Fin 6) ⟨Pi.single 2 1 + Pi.single 3 1, by simp [mem_core]; decide⟩) = 0
    rw [naturalPairing_apply_core]
    decide
  simp only [map_add,map_smul,LinearMap.smul_apply,h01,h23,smul_zero,zero_add]

variable {L : Type*} [Group L]

def coordinates (m : BlockModuleModel L action) (hz : blockFixed L = ⊥) :
    blockU L ≃* Multiplicative (natural (Fin 6)) :=
  (MulEquiv.ofBijective (QuotientGroup.mk' (blockFixed L))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk',hz]),
      QuotientGroup.mk'_surjective _⟩).trans m.moduleIso

private theorem moduleAction_normalizes (m : BlockModuleModel L action) (a : MulAut L) :
    m.moduleAction a ∈ normalizer (action.range : Set (MulAut (Multiplicative (natural (Fin 6))))) := by
  apply mem_normalizer_iff.mpr
  intro u
  constructor
  · rintro ⟨g,rfl⟩
    refine ⟨m.quotientAction a g,?_⟩
    ext v : 1
    have he := m.actions_compatible a g ((m.moduleAction a).symm v)
    simpa only [MulEquiv.apply_symm_apply,MulAut.mul_apply,MulAut.inv_apply] using he.symm
  · intro hu
    obtain ⟨g,hg⟩ := hu
    refine ⟨(m.quotientAction a).symm g,?_⟩
    apply (MulAut.conj (m.moduleAction a)).injective
    have he : (m.moduleAction a) * action ((m.quotientAction a).symm g) *
        (m.moduleAction a)⁻¹ = action g := by
      ext v : 1
      have hh := m.actions_compatible a ((m.quotientAction a).symm g)
        ((m.moduleAction a).symm v)
      simpa only [MulEquiv.apply_symm_apply,MulAut.mul_apply,MulAut.inv_apply] using hh
    exact he.trans hg

private theorem coordinates_preserve_form (m : BlockModuleModel L action)
    (hz : blockFixed L = ⊥) (a : MulAut L) (v w : blockU L) :
    form (coordinates m hz (MulAut.characteristic (blockU L) a v)).toAdd
      (coordinates m hz (MulAut.characteristic (blockU L) a w)).toAdd =
    form (coordinates m hz v).toAdd (coordinates m hz w).toAdd := by
  obtain ⟨g,hg⟩ := Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.exists_permutation_of_normalizes_alternatingMulImage (m.moduleAction a)
      (moduleAction_normalizes m a)
  have hv : coordinates m hz (MulAut.characteristic (blockU L) a v) =
      naturalMulAction (Fin 6) g (coordinates m hz v) := by
    change m.moduleIso (QuotientGroup.mk' _ (MulAut.characteristic (blockU L) a v)) = _
    rw [← m.moduleAction_mk,hg]
    rfl
  have hw : coordinates m hz (MulAut.characteristic (blockU L) a w) =
      naturalMulAction (Fin 6) g (coordinates m hz w) := by
    change m.moduleIso (QuotientGroup.mk' _ (MulAut.characteristic (blockU L) a w)) = _
    rw [← m.moduleAction_mk,hg]
    rfl
  rw [hv,hw]
  exact form_invariant g _ _

variable {G : Type*} [Group G] (K : Subgroup G)
abbrev sourceModule : Subgroup G := (blockU K).map K.subtype

def sourceCoordinates (m : BlockModuleModel K action) (hz : blockFixed K = ⊥) :
    sourceModule K ≃* Multiplicative (natural (Fin 6)) :=
  ((blockU K).equivMapOfInjective K.subtype K.subtype_injective).symm.trans (coordinates m hz)

private theorem source_form_invariant
    (m : BlockModuleModel K action) (hz : blockFixed K = ⊥)
    (g : G) (hg : g ∈ normalizer (K : Set G))
    (v w : sourceModule K) (hv : g*v.val*g⁻¹ ∈ sourceModule K)
    (hw : g*w.val*g⁻¹ ∈ sourceModule K) :
    form (sourceCoordinates K m hz ⟨g*v.val*g⁻¹,hv⟩).toAdd
      (sourceCoordinates K m hz ⟨g*w.val*g⁻¹,hw⟩).toAdd =
      form (sourceCoordinates K m hz v).toAdd (sourceCoordinates K m hz w).toAdd := by
  let a := K.normalizerMonoidHom ⟨g,hg⟩
  let ev := ((blockU K).equivMapOfInjective K.subtype K.subtype_injective).symm v
  let ew := ((blockU K).equivMapOfInjective K.subtype K.subtype_injective).symm w
  have he (x : sourceModule K) (hx : g*x.val*g⁻¹ ∈ sourceModule K) :
      ((blockU K).equivMapOfInjective K.subtype K.subtype_injective).symm
        ⟨g*x.val*g⁻¹,hx⟩ =
      MulAut.characteristic (blockU K) a
        (((blockU K).equivMapOfInjective K.subtype K.subtype_injective).symm x) := by
    apply ((blockU K).equivMapOfInjective K.subtype K.subtype_injective).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    change g*x.val*g⁻¹ = g*((((blockU K).equivMapOfInjective K.subtype K.subtype_injective).symm x : blockU K) : K)*g⁻¹
    congr 2
    exact (congrArg Subtype.val (((blockU K).equivMapOfInjective K.subtype K.subtype_injective).apply_symm_apply x)).symm
  have hev := congrArg (coordinates m hz) (he v hv)
  have hew := congrArg (coordinates m hz) (he w hw)
  calc
    _ = form (coordinates m hz (MulAut.characteristic (blockU K) a ev)).toAdd
      (coordinates m hz (MulAut.characteristic (blockU K) a ew)).toAdd :=
        congrArg₂ (fun x y => form (Multiplicative.toAdd x) (Multiplicative.toAdd y)) hev hew
    _ = _ := coordinates_preserve_form m hz a ev ew


/-- In the four-dimensional natural A₆ branch, the literal conjugate span
of the marked source plane by a point-centralizing group which moves it is
an elementary eight-group. -/
theorem conjugate_span_card
    [Finite G] (m : BlockModuleModel K action) (hz : blockFixed K = ⊥)
    (V Z J : Subgroup G) (hVW : V ≤ sourceModule K)
    (hplane : (V.subgroupOf (sourceModule K)).map (sourceCoordinates K m hz).toMonoidHom =
      canonicalPlane.toAddSubgroup.toSubgroup)
    (hpoint : (Z.subgroupOf (sourceModule K)).map (sourceCoordinates K m hz).toMonoidHom =
      canonicalLine.toAddSubgroup.toSubgroup)
    (hJN : J ≤ normalizer (K : Set G)) (hJZ : J ≤ centralizer (Z : Set G))
    (hmove : ¬ J ≤ normalizer (V : Set G)) (hcard : Nat.card V = 4) :
    Nat.card (conjugateSpanBy V J) = 8 := by
  let W := sourceModule K
  let q := sourceCoordinates K m hz
  let P : Subgroup W := PointAction.Hyperplane.toAddSubgroup.toSubgroup.comap q.toMonoidHom
  let B : Subgroup G := P.map W.subtype
  have hBW : B ≤ W := map_subtype_le P
  have hmem (w : W) : w.val ∈ B ↔ (q w).toAdd ∈ PointAction.Hyperplane := by
    change w.val ∈ P.map W.subtype ↔ _
    rw [mem_map]
    constructor
    · rintro ⟨u,hu,he⟩
      exact (Subtype.ext he : u=w) ▸ hu
    · intro hw
      exact ⟨w,hw,rfl⟩
  have hVB : V ≤ B := by
    intro v hv
    apply (hmem ⟨v,hVW hv⟩).mpr
    apply plane_le_hyperplane
    have hh := mem_map_of_mem q.toMonoidHom (show (⟨v,hVW hv⟩ : W) ∈ V.subgroupOf W from hv)
    change q ⟨v,hVW hv⟩ ∈ (V.subgroupOf W).map q.toMonoidHom at hh
    rw [hplane] at hh
    exact hh
  obtain ⟨z,hzZ,hzq⟩ : ∃ z : W, z.val ∈ Z ∧ (q z).toAdd = pairVector 4 5 := by
    have hh : Multiplicative.ofAdd (pairVector 4 5) ∈
        (Z.subgroupOf W).map q.toMonoidHom := by
      rw [hpoint]
      change pairVector 4 5 ∈ canonicalLine
      exact Submodule.subset_span (Set.mem_singleton _)
    obtain ⟨z,hz,he⟩ := hh
    exact ⟨z,hz,congrArg Multiplicative.toAdd he⟩
  have hJW : J ≤ normalizer (W : Set G) := hJN.trans
    (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hJB : J ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    intro j hj v hv
    have hvW := hBW hv
    have hv' := le_normalizer_iff.mp hJW j hj v hvW
    apply (hmem ⟨j*v*j⁻¹,hv'⟩).mpr
    intro x hx
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hzfixed : j*z.val*j⁻¹ = z.val := by
      have hc := hJZ hj z hzZ
      exact mul_inv_eq_iff_eq_mul.mpr hc.symm
    have hzW : j*z.val*j⁻¹ ∈ W := hzfixed.symm ▸ z.property
    have he := source_form_invariant K m hz j (hJN hj) z ⟨v,hvW⟩ hzW hv'
    have hez : (⟨j*z.val*j⁻¹,hzW⟩ : W) = z := Subtype.ext hzfixed
    rw [hez] at he
    have hzv : form (q z).toAdd (q ⟨v,hvW⟩).toAdd = 0 := by
      rw [hzq]
      exact (hmem ⟨v,hvW⟩).mp hv _ (Submodule.subset_span (Set.mem_singleton _))
    change form (c • pairVector 4 5) (q ⟨j*v*j⁻¹,hv'⟩).toAdd = 0
    rw [map_smul,LinearMap.smul_apply,←hzq,he,hzv,smul_zero]
  have hspanB : conjugateSpanBy V J ≤ B := conjugateSpanBy_le hVB hJB
  have hBcard : Nat.card B = 8 := by
    have heP : Nat.card P = Nat.card (Multiplicative PointAction.Hyperplane) := by
      let f : P ≃ Multiplicative PointAction.Hyperplane := {
        toFun p := Multiplicative.ofAdd ⟨(q p.val).toAdd,p.property⟩
        invFun x := ⟨q.symm (Multiplicative.ofAdd x.toAdd.val), by
          change (q (q.symm (Multiplicative.ofAdd x.toAdd.val))).toAdd ∈ PointAction.Hyperplane
          rw [q.apply_symm_apply]
          exact x.toAdd.property⟩
        left_inv p := by apply Subtype.ext; exact q.symm_apply_apply p.val
        right_inv x := by
          apply Multiplicative.toAdd.injective
          apply Subtype.ext
          exact congrArg Multiplicative.toAdd (q.apply_symm_apply _) }
      exact Nat.card_congr f
    have heB : Nat.card B = Nat.card P :=
      (Nat.card_congr (P.equivMapOfInjective W.subtype W.subtype_injective).toEquiv).symm
    exact heB.trans (heP.trans PointAction.hyperplane_card)
  have hlo : 4 < Nat.card (conjugateSpanBy V J) := by
    apply lt_of_not_ge
    intro hc
    have he : V = conjugateSpanBy V J :=
      eq_of_le_of_card_ge (le_conjugateSpanBy V J) (by simpa [hcard] using hc)
    exact hmove (he ▸ le_normalizer_conjugateSpanBy V J)
  have hd : Nat.card (conjugateSpanBy V J) ∣ 8 :=
    hBcard ▸ card_dvd_of_le hspanB
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card (conjugateSpanBy V J) ∣ 2 ^ 3 from hd)
  interval_cases k <;> norm_num only [pow_zero,pow_one,show 2^2=4 from rfl,show 2^3=8 from rfl] at he <;> omega


/-- In the source branch with |U(K)|=16 the natural quotient has the same
order, so the central kernel of the block-module projection is trivial. -/
theorem fixed_eq_bot_of_card [Finite G] (m : BlockModuleModel K action)
    (hcard : Nat.card (sourceModule K) = 16) : blockFixed K = ⊥ := by
  have hU : Nat.card (blockU K) = 16 :=
    (Nat.card_congr ((blockU K).equivMapOfInjective K.subtype K.subtype_injective).toEquiv).trans hcard
  have hQ : Nat.card (BlockModule K) = 16 := by
    calc
      _ = Nat.card (natural (Fin 6)) := Nat.card_congr m.moduleIso.toEquiv
      _ = 16 := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
          finrank_natural_even (Fin 6) (by decide)]
        decide
  apply card_eq_one.mp
  have hc := (blockFixed K).card_mul_index
  change Nat.card (blockFixed K) * Nat.card (BlockModule K) = Nat.card (blockU K) at hc
  rw [hU,hQ] at hc
  omega

/-- Coordinates on the actual U(K), using its four-dimensional source branch. -/
def sourceCoordinatesOfCard [Finite G] (m : BlockModuleModel K action)
    (hcard : Nat.card (sourceModule K) = 16) :
    sourceModule K ≃* Multiplicative (natural (Fin 6)) :=
  sourceCoordinates K m (fixed_eq_bot_of_card K m hcard)

end CFSG.Quasithin.Chapter14.Section06.RankThreeNaturalSix

namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Theory.GroupTheory RankThreeNaturalSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The natural A₆ branch of original 14.6.10(5). The original local
hypotheses supply point centrality; normality of the selected component
supplies its module action. Only its compatible earlier-source module and
flag marks remain, with the actual escaping second parabolic. -/
theorem source_parabolic_naturalSix_rank_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (I I2 K : Subgroup G) (hKI : K ≤ I) (hKN : (K.subgroupOf I).Normal)
    (hI2I : I2 ≤ I) (hI2H : I2 ≤ H) (hI2M : ¬ I2 ≤ M)
    (m : BlockModuleModel K RankThreeNaturalSix.action)
    (hW : Nat.card (RankThreeNaturalSix.sourceModule K) = 16)
    (hVW : localModule T M ≤ RankThreeNaturalSix.sourceModule K)
    (hplane : ((localModule T M).subgroupOf (RankThreeNaturalSix.sourceModule K)).map
      (sourceCoordinatesOfCard K m hW).toMonoidHom = canonicalPlane.toAddSubgroup.toSubgroup)
    (hpoint : ((centralInvolutions T).subgroupOf (RankThreeNaturalSix.sourceModule K)).map
      (sourceCoordinatesOfCard K m hW).toMonoidHom = canonicalLine.toAddSubgroup.toSubgroup) :
    IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) I2) ∧
      Nat.card (conjugateSpanBy (localModule T M) I2) = 8 ∧
      primeRank 2 (conjugateSpanBy (localModule T M) I2) = 3 := by
  have hI2K : I2 ≤ normalizer (K : Set G) :=
    hI2I.trans ((normal_subgroupOf_iff_le_normalizer hKI).mp hKN)
  have hI2Z : I2 ≤ centralizer (centralInvolutions T : Set G) :=
    hI2H.trans (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e H hH.1 hH.2).2
  have hm : ¬ I2 ≤ normalizer (localModule T M : Set G) := by
    rwa [← InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1]
  have hc := conjugate_span_card K m (fixed_eq_bot_of_card K m hW)
    (localModule T M) (centralInvolutions T) I2 hVW hplane hpoint hI2K hI2Z hm hcard
  let W := RankThreeNaturalSix.sourceModule K
  let V0 := conjugateSpanBy (localModule T M) I2
  let : IsElementaryAbelian 2 (Multiplicative (natural (Fin 6))) :=
    Representation.BinaryGroupAction.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (sourceCoordinatesOfCard K m hW).toMonoidHom (sourceCoordinatesOfCard K m hW).injective
  let : IsElementaryAbelian 2 V0 := IsElementaryAbelian.of_le
    (conjugateSpanBy_le hVW (hI2K.trans
      (normalizer_le_normalizer_characteristic_image K (blockU K))))
  refine ⟨inferInstance,hc,?_⟩
  apply le_antisymm
  · exact IsElementaryAbelian.primeRank_le_of_card_le V0 (n := 3) (by rw [hc]; decide)
  · let : IsElementaryAbelian 2 (⊤ : Subgroup V0) := IsElementaryAbelian.of_injective
      (⊤ : Subgroup V0).subtype (⊤ : Subgroup V0).subtype_injective
    exact IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup V0)
      ((Nat.card_congr (topEquiv : (⊤ : Subgroup V0) ≃* V0).toEquiv).trans hc)

end CFSG.Quasithin.Chapter14.Section06
