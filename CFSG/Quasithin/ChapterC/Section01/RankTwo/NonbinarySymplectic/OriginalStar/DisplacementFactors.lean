module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.DisplacementRank
public import Theory.GroupTheory.Commutator.SeparatedActions

/-!
# Original automorphisms preserve or separate the center-action factors

Let C be the full minimum center, T the selected original star,
B = R intersect M, and Q₀ = T intersect O₂(H). The decomposition of C into
its moving and component-fixed parts separates the actions of B and Q₀.
Quadraticity gives the exact formula
|[C,bq]| = |[C,b]| |[C,q]| for b in B and q in Q₀. Since every nontrivial
actor moves at least q elements, an actor moving fewer than q squared
elements lies in one of the two action factors.

Every actor of B moves at most q elements. Restrictions of ORIGINAL
radical automorphisms preserve displacement orders and the star. Their
conjugates of the B action therefore lie in the union of the two factors.
A subgroup contained in that union lies in one factor; equal orders give
equality in the first case. Thus each original automorphism preserves the
B action or carries it entirely into the fixed-core action. Comparing
literal conjugation images carries the same dichotomy to D = [C,B]: its
image is D or lies in E = [C,Q₀] and is disjoint from D.

The consumer constructs the same marked, saturated source star from Input
and the given distance-two replacement. It retains the complete center,
all fixed attachments, the original quotient marking and arbitrary field
degree. The exchange alternative is not excluded. Minimum marked
preservation and saturation, the Sylow branch, the field restriction and
final block assembly remain open.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.7), pp.872--875, for the original-radical and full-kernel
comparison; Section 7, pp.932--933, for the separate minimum cut. The
factor dichotomy is a consequence of the established original inputs,
not an identification of the minimum cut with the source star.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- On the selected source star, small full-center actors lie in a single
factor. Every ORIGINAL radical automorphism either preserves the original
intersection action or carries it entirely into the fixed-core action.
The latter alternative is retained, with no fixed attachment discarded. -/
theorem exists_source_star_automorphism_factor_dichotomy
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      d.subgroup ≤ starCentralizer R Y ∧
      (((starCentralizer R Y).map R.subtype).subgroupOf K).map (componentProjection h) =
        (R.subgroupOf K).map (componentProjection h) ∧
      (let T := (starCentralizer R Y).map R.subtype
       let M := K ⊔ T
       (normalizer (T.subgroupOf M : Set M)).pCoreIn 2 = T.subgroupOf M) ∧
      (let T := starCentralizer R Y
       let B := d.overgroup.subgroupOf R
       let Q₀ := T ⊓ (pCore 2 H).comap R.subtype
       let C := minimumCenter d
       let θ := minimumCenterAction d
       (∀ b ∈ B, ∀ q ∈ Q₀,
         Nat.card (⁅C,zpowers (b*q)⁆ : Subgroup R) =
           Nat.card (⁅C,zpowers b⁆ : Subgroup R) * Nat.card (⁅C,zpowers q⁆ : Subgroup R)) ∧
       (∀ x ∈ T, Nat.card (⁅C,zpowers x⁆ : Subgroup R) < 2^(2*n) →
         θ x ∈ B.map θ ∨ θ x ∈ Q₀.map θ) ∧
       (∀ a : MulAut R,
         (B.map θ).map (MulAut.conj ((MulAut.characteristic C) a)).toMonoidHom = B.map θ ∨
         (B.map θ).map (MulAut.conj ((MulAut.characteristic C) a)).toMonoidHom ≤ Q₀.map θ) ∧
       (∀ a : MulAut R,
         (⁅C,B⁆).map a.toMonoidHom = ⁅C,B⁆ ∨
           (⁅C,B⁆).map a.toMonoidHom ≤ ⁅C,Q₀⁆ ∧
           Disjoint ((⁅C,B⁆).map a.toMonoidHom) ⁅C,B⁆)) := by
  obtain ⟨P,Y,hY,hn,hmin,hs,hquot,hrest,hsat,hmark,hfactor,hfirst,hD,
    hdis,hcard,hjoin,hthird,hEC,hEn,hDE,hCE,hquad⟩ :=
    exists_source_star_whole_core_layers h d g hb hnsyl hne
  have hsize := replacement_proper_nonsylow_card h d g hb hnsyl hne
  let T := starCentralizer R Y
  let B := d.overgroup.subgroupOf R
  let Q₀ := T ⊓ (pCore 2 H).comap R.subtype
  let C := minimumCenter d
  let θ := minimumCenterAction d
  let C₀ := d.ambient ⊓ centralizer (d.ambient : Set H)
  let V₀ := (blockU K).map K.subtype ⊓ centralizer (d.ambient : Set H)
  let A₀ := C₀ ⊓ centralizer (K : Set H)
  have hmC : C.map R.subtype = C₀ := by
    dsimp only [C,minimumCenter,C₀]
    rw [←map_inf_centralizer_of_injective _ R.subtype_injective]
  have hmB : B.map R.subtype = R ⊓ d.overgroup :=
    (subgroupOf_map_subtype _ _).trans (inf_comm _ _)
  have hmQ : Q₀.map R.subtype = T.map R.subtype ⊓ pCore 2 H := by
    rw [map_inf _ _ _ R.subtype_injective,map_comap_eq,range_subtype,
      ←inf_assoc,inf_eq_left.mpr (map_subtype_le _)]
  have hTBQ : T = B ⊔ Q₀ := by
    apply map_injective R.subtype_injective
    rw [Subgroup.map_sup,hmB,hmQ]
    exact hfactor
  have hBT : B ≤ T := le_sup_left.trans_eq hTBQ.symm
  have hQT : Q₀ ≤ T := inf_le_left
  have hquadR : ⁅⁅C,T⁆,T⁆ = ⊥ := by
    apply map_injective R.subtype_injective
    rw [map_commutator,map_commutator,hmC,Subgroup.map_bot]
    exact hquad
  have hDcard : Nat.card (⁅C,B⁆ : Subgroup R) = 2^n := by
    rw [←card_map_of_injective R.subtype_injective,map_commutator,hmC,hmB,←hD]
    exact hcard
  have hdisR : Disjoint ⁅C,B⁆ ⁅C,Q₀⁆ := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    apply R.subtype_injective
    have hxD : (x:H) ∈ ⁅C₀,R ⊓ d.overgroup⁆ := by
      rw [←hmC,←hmB,←map_commutator]
      exact mem_map_of_mem _ hx.1
    have hxE : (x:H) ∈ ⁅C₀,T.map R.subtype ⊓ pCore 2 H⁆ := by
      rw [←hmC,←hmQ,←map_commutator]
      exact mem_map_of_mem _ hx.2
    exact disjoint_iff_inf_le.mp hDE ⟨hD.symm ▸ hxD,hxE⟩
  obtain ⟨hdec,hAM,hAn⟩ := minimum_center_decomposition h d g hb hsize
  change C₀ = V₀ ⊔ A₀ at hdec
  let := hAn
  let V := V₀.subgroupOf R
  let A := A₀.subgroupOf R
  have hVC : V₀ ≤ C₀ := le_sup_left.trans_eq hdec.symm
  have hVR : V₀ ≤ R := hVC.trans (hmC.symm.trans_le (map_subtype_le _))
  have hAR : A₀ ≤ R := inf_le_left.trans (hmC.symm.trans_le (map_subtype_le _))
  have hsplit : C = V ⊔ A := by
    have he : C = C₀.subgroupOf R := by rw [←hmC,subgroupOf_map_subtype_eq]
    rw [he,hdec,subgroupOf_sup hVR hAR]
  let : IsElementaryAbelian 2 C := minimum_center_elementary h d g hb
  have hproduct (b : R) (hbb : b ∈ B) (q : R) (hqq : q ∈ Q₀) :
      Nat.card (⁅C,zpowers (b*q)⁆ : Subgroup R) =
        Nat.card (⁅C,zpowers b⁆ : Subgroup R) * Nat.card (⁅C,zpowers q⁆ : Subgroup R) := by
    apply separated_cyclic_displacement_card C V A T hsplit hquadR b q (hBT hbb) (hQT hqq)
    · intro a ha
      apply R.subtype_injective
      exact (hAM ha b hbb).symm
    · intro v hv
      apply R.subtype_injective
      exact (original_whole_core_centralizer h d g hb).ge hqq.2 v hv.1
    · exact hdisR.mono (commutator_mono le_rfl (zpowers_le.mpr hbb))
        (commutator_mono le_rfl (zpowers_le.mpr hqq))
  have hgap (x : R) (hx : x ∈ T) (hmove : θ x ≠ 1) :
      2^n ≤ Nat.card (⁅C,zpowers x⁆ : Subgroup R) :=
    star_center_actor_displacement_card_ge h d g hb P Y hY hmin hrest hsize x hx hmove
  have hQnormal : Q₀.Normal := by dsimp only [Q₀,T]; infer_instance
  let := hQnormal
  have hsmall (x : R) (hx : x ∈ T)
      (hsmallx : Nat.card (⁅C,zpowers x⁆ : Subgroup R) < 2^(2*n)) :
      θ x ∈ B.map θ ∨ θ x ∈ Q₀.map θ := by
    rw [hTBQ] at hx
    obtain ⟨b,hbb,q,hqq,rfl⟩ := mem_sup_of_normal_right.mp hx
    by_cases hb0 : θ b = 1
    · right
      rw [map_mul,hb0,one_mul]
      exact mem_map_of_mem _ hqq
    by_cases hq0 : θ q = 1
    · left
      rw [map_mul,hq0,mul_one]
      exact mem_map_of_mem _ hbb
    have hlo := Nat.mul_le_mul (hgap b (hBT hbb) hb0) (hgap q (hQT hqq) hq0)
    rw [←hproduct b hbb q hqq,←pow_add,←two_mul] at hlo
    exact False.elim ((not_lt_of_ge hlo) hsmallx)
  have hfactorAut (a : MulAut R) :
      (B.map θ).map (MulAut.conj ((MulAut.characteristic C) a)).toMonoidHom = B.map θ ∨
      (B.map θ).map (MulAut.conj ((MulAut.characteristic C) a)).toMonoidHom ≤ Q₀.map θ := by
    let χ := MulAut.conj ((MulAut.characteristic C) a)
    have he (b : R) : χ (θ b) = θ (a b) := by
      apply MulEquiv.ext
      intro c
      apply Subtype.ext
      change a (b * a.symm (c:R) * b⁻¹) = a b * (c:R) * (a b)⁻¹
      rw [map_mul,map_mul,map_inv,a.apply_symm_apply]
    have hfield : 2^n < 2^(2*n) := by
      apply Nat.pow_lt_pow_right (by decide)
      have := h.nonbinary
      omega
    have hmem : ((B.map θ).map χ.toMonoidHom : Set (MulAut C)) ⊆
        (B.map θ : Set (MulAut C)) ∪ (Q₀.map θ : Set (MulAut C)) := by
      rintro _ ⟨_,⟨b,hbb,rfl⟩,rfl⟩
      change χ (θ b) ∈ (B.map θ : Set (MulAut C)) ∪ (Q₀.map θ : Set (MulAut C))
      rw [he]
      apply hsmall (a b)
      · exact characteristic_iff_le_comap.mp (inferInstance : T.Characteristic) a (hBT hbb)
      · have hrow : Nat.card (⁅C,zpowers b⁆ : Subgroup R) ≤ 2^n := by
          rw [←hDcard]
          exact Nat.card_le_card_of_injective
            (inclusion (commutator_mono le_rfl (zpowers_le.mpr hbb))) (inclusion_injective _)
        have hm : (⁅C,zpowers b⁆).map a.toMonoidHom = ⁅C,zpowers (a b)⁆ := by
          rw [map_commutator,MonoidHom.map_zpowers,characteristic_iff_map_eq.mp inferInstance a]
          rfl
        rw [←hm,card_map_of_injective a.injective]
        exact hrow.trans_lt hfield
    rcases SubgroupClass.subset_union.mp hmem with hleft | hright
    · left
      apply eq_of_le_of_card_ge hleft
      exact (card_map_of_injective (K := B.map θ) (f := χ.toMonoidHom) χ.injective).ge
    · exact Or.inr hright
  have hdisplacementAut (a : MulAut R) :
      (⁅C,B⁆).map a.toMonoidHom = ⁅C,B⁆ ∨
        (⁅C,B⁆).map a.toMonoidHom ≤ ⁅C,Q₀⁆ ∧
        Disjoint ((⁅C,B⁆).map a.toMonoidHom) ⁅C,B⁆ := by
    let χ := MulAut.conj ((MulAut.characteristic C) a)
    have he : θ.comp a.toMonoidHom = χ.toMonoidHom.comp θ := by
      apply MonoidHom.ext
      intro b
      apply MulEquiv.ext
      intro c
      apply Subtype.ext
      change a b * (c:R) * (a b)⁻¹ = a (b * a.symm (c:R) * b⁻¹)
      rw [map_mul,map_mul,map_inv,a.apply_symm_apply]
    have hm : (B.map a.toMonoidHom).map θ = (B.map θ).map χ.toMonoidHom := by
      rw [map_map,map_map,he]
    have hmove : (⁅C,B⁆).map a.toMonoidHom = ⁅C,B.map a.toMonoidHom⁆ := by
      rw [map_commutator,characteristic_iff_map_eq.mp inferInstance a]
    rcases hfactorAut a with hpres | hexchange
    · left
      rw [hmove]
      have him : (B.map a.toMonoidHom).map θ = B.map θ := hm.trans hpres
      exact le_antisymm
        (commutator_le_of_conjNormal_image_le C _ _ him.le)
        (commutator_le_of_conjNormal_image_le C _ _ him.ge)
    · have hle : (⁅C,B⁆).map a.toMonoidHom ≤ ⁅C,Q₀⁆ := by
        rw [hmove]
        exact commutator_le_of_conjNormal_image_le C _ _ (hm.trans_le hexchange)
      exact Or.inr ⟨hle,hdisR.symm.mono hle le_rfl⟩
  exact ⟨P,Y,hY,hn,hmin,hmark,hsat,hproduct,hsmall,hfactorAut,hdisplacementAut⟩
end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
