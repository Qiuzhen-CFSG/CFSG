module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ShortRootLift
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot.CubicKernel
public import Theory.SpecificGroups.AlternatingFiveFixedCentralizer

/-!
# The original binary short-root centralizer bound

In the contrary case, I.8.5 recognizes the normal closure in C_G(t)/⟨t⟩ as
A₅. The elementary Sylow preimage supplies its actual normal A₅ lift. Let E
be the order-four subgroup of the original plane radical fixed by the
marked cubic. Its elements fix the lifted A₅ Sylow subgroup pointwise,
so their actions are inner by that Sylow subgroup. Commuting with the cubic
forces these inner conjugators into ⟨t⟩, whose intersection with A₅ is trivial.
Thus E centralizes A₅, contradicting the original solvable long-root
centralizer through the proved fixed-four obstruction.

This constructs E and A₅ from the original faithful completion and its
normalizer and centralizer hypotheses. The four-group is the cubic fixed
subgroup; no assertion about the full Levi fixed subgroup is used. The
marked full-centralizer equivalence and order are exported for F.4.43.
Source: Aschbacher–Smith, F.4.42, printed pp.295–296, ordinary U₄(2) case.
-/

open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourPlaneLocal UnitaryFourShortRoot
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.ShortRootCentralizer
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open CFSG.Quasithin.ChapterF.UnitaryTwo
open ShortRootFixedFour ShortRootQuotient ShortRootFusion ShortRootRecognition ShortRootLift
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "L" => L2Matrix 1 hn
local notation "X" => shortCentralizer F σ hσ
local notation "Q" => radical F σ hσ
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
  (amalgam 1 hn) (G := G0)) (i : G0 →* G)
local notation "H" => ambientShortCentralizer c i
local notation "A" => liftedA c i

def ambientCubic : H := shortCentralizerEmbedding c i (markedCubic F σ hσ)

def radicalIntoAmbient : Q →* H :=
  (shortCentralizerEmbedding c i).comp (inclusion (radical_le_shortCentralizer F σ hσ))

def ambientRadical : Subgroup H := (⊤ : Subgroup Q).map (radicalIntoAmbient c i)

instance ambientRadical_elementary : IsElementaryAbelian 2 (ambientRadical c i) := by
  let : IsElementaryAbelian 2 (⊤ : Subgroup Q) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup Q).subtype (⊤ : Subgroup Q).subtype_injective
  exact IsElementaryAbelian.map (radicalIntoAmbient c i)

omit [Finite G] in
theorem radicalIntoAmbient_injective (hi : Function.Injective i) :
    Function.Injective (radicalIntoAmbient c i) :=
  (shortCentralizerEmbedding_injective c i hi).comp (inclusion_injective _)

/-- The original cubic-fixed four-group, before transport to G. -/
def ambientFixedFour : Subgroup H := (fixedRadical F σ hσ).map (radicalIntoAmbient c i)

omit [Finite G] in
theorem ambientFixedFour_card (hi : Function.Injective i) : Nat.card (ambientFixedFour c i) = 4 := by
  rw [ambientFixedFour,card_map_of_injective (radicalIntoAmbient_injective c i hi),fixedRadical_card]
  exact matrixField_card 1 hn

omit [Finite G] in
theorem ambientEight_le_radical : ambientEight c i ≤ ambientRadical c i := by
  rintro a ⟨x,hx,rfl⟩
  exact ⟨⟨x.val,orthogonalRadical_le_radical F σ hσ hx⟩,mem_top _,rfl⟩

omit [Finite G] in
theorem ambientFixedFour_le_radical : ambientFixedFour c i ≤ ambientRadical c i := map_mono le_top

omit [Finite G] in
theorem ambientEight_cubic_fixed
    (hi : Function.Injective i) (x : H) (hx : x ∈ ambientEight c i)
    (hxc : x * ambientCubic c i = ambientCubic c i * x) :
    x ∈ ambientLine c i := by
  obtain ⟨a,ha,rfl⟩ := hx
  have hac : a * markedCubic F σ hσ = markedCubic F σ hσ * a := by
    apply shortCentralizerEmbedding_injective c i hi
    simpa only [map_mul,ambientCubic] using hxc
  obtain he | he := binary_orthogonal_cubic_centralizer F σ hσ
    (show Nat.card (FixedBy.subfield F σ) = 2 from PointLocal.fixedField_card 1 hn) a ha hac
  · rw [he,map_one]
    exact one_mem _
  · rw [he]
    exact mem_zpowers (ambientMark c i)

omit [Finite G] in
theorem ambientFixedFour_centralizes_cubic :
    ambientFixedFour c i ≤ centralizer ({ambientCubic c i} : Set H) := by
  rintro x ⟨r,hr,rfl⟩
  have hfix := (MulAut.mem_fixedSubgroup _ _).mp hr
  have he : (levi F σ hσ (cubic F)) * r.val * (levi F σ hσ (cubic F))⁻¹ = r.val :=
    congrArg (fun v : Q => v.val) hfix
  have heX : markedCubic F σ hσ * inclusion (radical_le_shortCentralizer F σ hσ) r *
      (markedCubic F σ hσ)⁻¹ = inclusion (radical_le_shortCentralizer F σ hσ) r := Subtype.ext he
  apply mem_centralizer_singleton_iff.mpr
  have heH := congrArg (shortCentralizerEmbedding c i) heX
  simp only [map_mul,map_inv] at heH
  exact (mul_inv_eq_iff_eq_mul.mp heH).symm

/-- The constructed four-group centralizes the actual lifted A₅. -/
theorem ambientFixedFour_centralizes_liftedA
    (hi : Function.Injective i)
    (e : quotientClosure c i ≃* alternatingGroup (Fin 5)) :
    ambientFixedFour c i ≤ centralizer (A : Set H) := by
  obtain ⟨eA⟩ := liftedA_equiv c i hi e
  have hP : (liftedSylow c i hi e : Subgroup A).map (A).subtype ≤ ambientRadical c i :=
    (liftedSylow_le_eight c i hi e).trans (ambientEight_le_radical c i)
  have hfix : ∀ a : A, a ∈ liftedSylow c i hi e →
      ambientCubic c i * a.val * (ambientCubic c i)⁻¹ = a.val → a = 1 := by
    intro a ha he
    have hV : a.val ∈ ambientEight c i := liftedSylow_le_eight c i hi e ⟨a,ha,rfl⟩
    have hU := ambientEight_cubic_fixed c i hi a.val hV (mul_inv_eq_iff_eq_mul.mp he).symm
    apply (liftedA_projection c i hi e).2
    change QuotientGroup.mk' (ambientLine c i) a.val = QuotientGroup.mk' (ambientLine c i) 1
    rw [map_one]
    exact (QuotientGroup.eq_one_iff _).mpr hU
  intro x hx
  apply alternating_five_fixed_centralizes A (ambientRadical c i) eA (liftedSylow c i hi e)
    hP (ambientCubic c i) hfix (ambientFixedFour_le_radical c i hx)
  exact mem_centralizer_singleton_iff.mp (ambientFixedFour_centralizes_cubic c i hx)

/-- The constructed E inside the original ambient G. -/
def sourceFixedFour : Subgroup G := (ambientFixedFour c i).map (H).subtype

omit [Finite G] in
theorem sourceFixedFour_card (hi : Function.Injective i) : Nat.card (sourceFixedFour c i) = 4 :=
  (card_map_of_injective (H).subtype_injective).trans (ambientFixedFour_card c i hi)

omit [Finite G] in
theorem sourceFixedFour_le_core : sourceFixedFour c i ≤ PlainFusion.sourcePlaneRootImage c i := by
  rintro x ⟨y,hy,rfl⟩
  obtain ⟨r,hr,rfl⟩ := hy
  rw [PlainFusion.sourcePlaneRootImage_eq,← radical_image]
  exact ⟨r.val,r.property,rfl⟩

omit [Finite G] in
theorem sourceFixedFour_centralizes_cubic :
    sourceFixedFour c i ≤ centralizer
      ({matrixPlaneEmbedding c i (levi F σ hσ (cubic F))} : Set G) := by
  rintro x ⟨y,hy,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg (fun h : H => h.val)
    (mem_centralizer_singleton_iff.mp (ambientFixedFour_centralizes_cubic c i hy))

/-- The actual normal A₅ lift, mapped into the original group G. -/
def sourceA : Subgroup G := (A).map (H).subtype

theorem sourceA_centralizes_fixedFour
    (hi : Function.Injective i)
    (e : quotientClosure c i ≃* alternatingGroup (Fin 5)) :
    sourceA c i ≤ centralizer (sourceFixedFour c i : Set G) := by
  rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩
  have hh := ambientFixedFour_centralizes_liftedA c i hi e hb a ha
  exact congrArg (fun h : H => h.val) hh.symm

theorem sourceA_equiv
    (hi : Function.Injective i)
    (e : quotientClosure c i ≃* alternatingGroup (Fin 5)) :
    Nonempty (sourceA c i ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨eA⟩ := liftedA_equiv c i hi e
  exact ⟨((A).equivMapOfInjective (H).subtype (H).subtype_injective).symm.trans eA⟩

/-- Original F.4.42 for the ordinary binary unitary-four completion: the
selected short-root centralizer is contained in the original plane endpoint.
The contrary branch constructs the normal A₅ and the actual cubic-fixed
four-group and closes the frozen long-root-centralizer obstruction. -/
theorem source_short_centralizer_le_plane
    (hi : Function.Injective i)
    (z : pointParabolic 1 hn) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range) :
    centralizer ({sourceShort c i} : Set G) ≤ (i.comp c.right).range := by
  by_contra hnot
  obtain ⟨e⟩ := source_quotient_normalClosure_alternating_five c i hi z hz hzroot hc hnorm hnot
  exact source_fixed_four_obstruction c i hi z hz hzroot hc (sourceFixedFour c i)
    (sourceFixedFour_le_core c i) (sourceFixedFour_centralizes_cubic c i)
    (sourceFixedFour_card c i hi) (sourceA c i)
    (sourceA_centralizes_fixedFour c i hi e) (sourceA_equiv c i hi e)

/-- The original marking identifies the full ambient short-root centralizer
with its literal matrix centralizer. This is the short-root input to F.4.43. -/
theorem shortCentralizerEmbedding_surjective
    (hi : Function.Injective i)
    (z : pointParabolic 1 hn) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range) :
    Function.Surjective (shortCentralizerEmbedding c i) := by
  intro a
  obtain ⟨p,hp⟩ := source_short_centralizer_le_plane c i hi z hz hzroot hc hnorm a.property
  change i (c.right p) = a.val at hp
  obtain ⟨x,hx⟩ := source_plane_short_centralizer c i hi p (hp.symm ▸ a.property)
  exact ⟨x,Subtype.ext (hx.trans hp)⟩

/-- The selected centralizer equivalence retains the actual endpoint embedding. -/
def sourceShortCentralizerEquiv
    (hi : Function.Injective i)
    (z : pointParabolic 1 hn) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range) :
    X ≃* H := MulEquiv.ofBijective (shortCentralizerEmbedding c i)
      ⟨shortCentralizerEmbedding_injective c i hi,
        shortCentralizerEmbedding_surjective c i hi z hz hzroot hc hnorm⟩

theorem sourceShortCentralizerEquiv_mark
    (hi : Function.Injective i)
    (z : pointParabolic 1 hn) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range) :
    sourceShortCentralizerEquiv c i hi z hz hzroot hc hnorm ShortRoot.mark = ambientMark c i := rfl

/-- The original ambient short-root centralizer has its model order 96. -/
theorem source_short_centralizer_card
    (hi : Function.Injective i)
    (z : pointParabolic 1 hn) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range) :
    Nat.card (centralizer ({sourceShort c i} : Set G)) = 96 :=
  (Nat.card_congr (sourceShortCentralizerEquiv c i hi z hz hzroot hc hnorm).symm.toEquiv).trans
    ShortRoot.centralizer_card


omit [Finite G] in
theorem sourceShort_order (hi : Function.Injective i) : orderOf (sourceShort c i) = 2 := by
  let f := (H).subtype.comp (shortCentralizerEmbedding c i)
  have hf : Function.Injective f := (H).subtype_injective.comp
    (shortCentralizerEmbedding_injective c i hi)
  exact (orderOf_injective f hf ShortRoot.mark).trans ShortRoot.mark_order

omit [Finite G] in
theorem sourceShort_mem_core : sourceShort c i ∈ PlainFusion.sourcePlaneRootImage c i := by
  rw [PlainFusion.sourcePlaneRootImage_eq,← radical_image]
  exact ⟨modelShort,
    (radicalEquiv F σ hσ (Multiplicative.ofAdd (shortParameter F σ))).property,rfl⟩

/-- The F.4.42 witness retains the selected short-root matrix, its involution
order, the original plane core, and the full ambient centralizer bound. -/
theorem source_marked_short_root
    (hi : Function.Injective i)
    (z : pointParabolic 1 hn) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range) :
    orderOf (sourceShort c i) = 2 ∧
    sourceShort c i ∈ PlainFusion.sourcePlaneRootImage c i ∧
    centralizer ({sourceShort c i} : Set G) ≤ (i.comp c.right).range :=
  ⟨sourceShort_order c i hi,sourceShort_mem_core c i,
    source_short_centralizer_le_plane c i hi z hz hzroot hc hnorm⟩

end CFSG.Quasithin.ChapterF.UnitaryTwo.ShortRootCentralizer
