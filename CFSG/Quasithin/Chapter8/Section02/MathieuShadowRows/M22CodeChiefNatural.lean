module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeChiefSeed
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeChiefNatural
import all CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeFrattiniGeometry
import all Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFrattiniGeometry

/-!
# A natural displacement on the original selected M22 chief

The chosen active chief contains the entire moved four-space and its
denominator misses it. The original residual kernel makes the I and R
operators commute. Source case I confines V-displacement to the seed;
the native theorem therefore supplies a natural four-dimensional image
for an actual involution from V. Both original quotient actor maps and the
full kernel of the original A5 marking are retained. The same image is
preserved by every normalizer of the literal seed, for the next Clifford step.

The internal imports share the literal section-embedding implementation.
Source: Aschbacher--Smith 8.2.9, printed p.721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open NoncentralChiefRefinement
open scoped IsMulCommutative commutatorElement MonoidAlgebra MatrixGroups
open Sporadic.Mathieu MathieuCode MathieuCode.M22Quintet MathieuCode.M22Quintet.CocodeTransfer
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE HermitianSource Offenders.Parabolic.Construction
  Normalizer.SmallOvergroups Normalizer.ParabolicReduction.RankSieve
open MathieuCode.NormalizedShadowRows.M22CodeSection
set_option backward.isDefEq.respectTransparency false

private theorem local_actions_commute_of_commutator_core
    {G Z : Type*} [Group G] [Finite G] [AddCommGroup Z] [Module (ZMod 2) Z]
    (R I H U : Subgroup G) [IsElementaryAbelian 2 U]
    (hIH : I ≤ H) (hHR : H ≤ normalizer (R : Set G))
    (hRU : R ≤ normalizer (U : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hcomm : ⁅R,I⁆ ≤ R.pCoreIn 2)
    (a : R →* SmallRows.localImage U (R ⊔ H))
    (t : I →* SmallRows.localImage U (R ⊔ H))
    (ha : ∀ r, (a r : normalizer (U : Set G) ⧸ U.subgroupOf (normalizer (U : Set G))) =
      QuotientGroup.mk' (U.subgroupOf (normalizer (U : Set G))) ⟨r.val,hRU r.property⟩)
    (ht : ∀ i, (t i : normalizer (U : Set G) ⧸ U.subgroupOf (normalizer (U : Set G))) =
      QuotientGroup.mk' (U.subgroupOf (normalizer (U : Set G))) ⟨i.val,hHU (hIH i.property)⟩)
    (ρ : Representation (ZMod 2) (SmallRows.localImage U (R ⊔ H)) Z)
    (hkill : pCore 2 (SmallRows.localImage U (R ⊔ H)) ≤ ρ.ker) :
    ∀ (i : I) (r : R), Commute (ρ (t i)) (ρ (a r)) := by
  let N := normalizer (U : Set G)
  let q := QuotientGroup.mk' (U.subgroupOf N)
  let J := SmallRows.localImage U (R ⊔ H)
  have hcore : R.pCoreIn 2 ≤ (R ⊔ H).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le R.le_normalizer hHR)
  intro i r
  let rN : N := ⟨r.val,hRU r.property⟩
  let iN : N := ⟨i.val,hHU (hIH i.property)⟩
  have hcG : ⁅(r : G),(i : G)⁆ ∈ (R ⊔ H).pCoreIn 2 :=
    hcore (hcomm (commutator_mem_commutator r.property i.property))
  have hcq : (⁅a r,t i⁆ : J).val ∈ J.pCoreIn 2 := by
    rw [←localImage_twoCore (sup_le hRU hHU)]
    refine ⟨⁅rN,iN⁆,hcG,?_⟩
    change q ⁅rN,iN⁆ = ⁅(a r).val,(t i).val⁆
    rw [map_commutatorElement,ha,ht]
  have hcoreJ : ⁅a r,t i⁆ ∈ pCore 2 J :=
    (mem_map_iff_mem J.subtype_injective).mp hcq
  have hcunits : Commute (ρ.asGroupHom (a r)) (ρ.asGroupHom (t i)) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    apply Units.ext
    exact hkill hcoreJ
  exact (congrArg Units.val hcunits.eq).symm

private theorem m22_five_chief_natural_displacement
    {G : Type*} [Group G] [Finite G]
    (B R I H U : Subgroup G) [IsElementaryAbelian 2 U]
    (fq : R →* MathieuCode.M22Quintet.Q) (hs : M22FiveSection R B U fq)
    (hBL : B ≤ R ⊔ H) (hIH : I ≤ H)
    (hHR : H ≤ normalizer (R : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hcomm : ⁅R,I⁆ ≤ R.pCoreIn 2)
    (t : I →* SmallRows.localImage U (R ⊔ H))
    (ht : ∀ i, (t i : normalizer (U : Set G) ⧸ U.subgroupOf (normalizer (U : Set G))) =
      QuotientGroup.mk' (U.subgroupOf (normalizer (U : Set G))) ⟨i.val,hHU (hIH i.property)⟩)
    (K C : NormalNode (SmallRows.localImage U (R ⊔ H)))
    [IsElementaryAbelian 2 (Section K C)]
    (hkill : pCore 2 (SmallRows.localImage U (R ⊔ H)) ≤ (binarySectionRepresentation K C).ker)
    (hWC : ⁅(SmallRows.localImage U B).subgroupOf (SmallRows.localImage U (R ⊔ H)),
      (SmallRows.localImage U R).subgroupOf (SmallRows.localImage U (R ⊔ H))⁆ ≤ C.val)
    (hWK : ⁅(SmallRows.localImage U B).subgroupOf (SmallRows.localImage U (R ⊔ H)),
      (SmallRows.localImage U R).subgroupOf (SmallRows.localImage U (R ⊔ H))⁆ ⊓ K.val = ⊥)
    (v : I) (hv : binarySectionRepresentation K C (t v) ≠ 1)
    (hmove : ⁅C.val,zpowers (t v)⁆ ≤
      ⁅(SmallRows.localImage U B).subgroupOf (SmallRows.localImage U (R ⊔ H)),
        (SmallRows.localImage U R).subgroupOf (SmallRows.localImage U (R ⊔ H))⁆) :
    ∃ hRU : R ≤ normalizer (U : Set G),
      ∃ (a : R →* SmallRows.localImage U (R ⊔ H)) (r : R →* alternatingGroup (Fin 5)),
        (∀ x, (a x : normalizer (U : Set G) ⧸ U.subgroupOf (normalizer (U : Set G))) =
          QuotientGroup.mk' (U.subgroupOf (normalizer (U : Set G))) ⟨x.val,hRU x.property⟩) ∧
        Function.Surjective r ∧ r.ker = pCore 2 R ∧
        (∀ x, (r x).val = NaturalQuotient.q (fq x)) ∧
        M22NaturalChiefDisplacement (binarySectionRepresentation K C) a r (t v) ∧
        M22ChiefDisplacementStable (binarySectionRepresentation K C) (t v)
          ⁅(SmallRows.localImage U B).subgroupOf (SmallRows.localImage U (R ⊔ H)),
            (SmallRows.localImage U R).subgroupOf (SmallRows.localImage U (R ⊔ H))⁆ := by
  obtain ⟨hRB,hRU,hBU,r,eB,hrs,hrker,hrval,hact,_,hEl,σ,hσ,_,_,_⟩ := hs
  let := hBU
  let := hEl
  obtain ⟨j,a,hji,hjr,har,hjq,haq,hja⟩ :=
    literal_section_embedding B R U (R ⊔ H) hRB hRU hBL le_sup_left (sup_le hRU hHU)
  have hjσ (x : R) (b : B ⧸ U.subgroupOf B) :
      j ((σ x (Additive.ofMul b)).toMul) = a x * j b * (a x)⁻¹ := by
    rw [hσ]
    exact hja x b
  let J := SmallRows.localImage U (R ⊔ H)
  let W := ⁅(SmallRows.localImage U B).subgroupOf J,(SmallRows.localImage U R).subgroupOf J⁆
  have hW : (Coinvariants.ker σ).toAddSubgroup.toSubgroup'.map j = W := by
    rw [moved_image_commutator σ j a hjσ,hjr,har]
  let e : Additive (B ⧸ U.subgroupOf B) ≃ₗ[ZMod 2] Additive MathieuCode.M22Quintet.K :=
    LinearEquiv.ofBijective (eB.toAdditive.toAddMonoidHom.toZModLinearMap 2) eB.bijective
  have he (r' : R) (b : Additive (B ⧸ U.subgroupOf B)) : e (σ r' b) = fiveAction (r r') (e b) :=
    (congrArg (fun w => Additive.ofMul (eB w.toMul)) (hσ r' b.toMul)).trans (hact r' b.toMul)
  have hcomm' := local_actions_commute_of_commutator_core R I H U hIH hHR hRU hHU
    hcomm a t haq ht (binarySectionRepresentation K C) hkill v
  exact ⟨hRU,a,r,haq,hrs,hrker,hrval,
    marked_chief_natural_displacement σ r hrs e he j hji a hjσ W hW K C hWC hWK
      (t v) hv hcomm' hmove⟩

/-- The actual active chief selected from the normal closure has a natural
four-dimensional displacement under an involution from the original V.
The original A5 marking, its full kernel and both quotient actors are retained. -/
theorem selected_m22_active_chief_natural_displacement
    {G : Type*} [Group G] [Finite G]
    {V H M I R U : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 U]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hHR : H ≤ normalizer (R : Set G))
    (hRP : R ≤ normalizer (I.pCoreIn 2 : Set G))
    (hPH : I.pCoreIn 2 ≤ H.pCoreIn 2)
    (hHU : H ≤ normalizer (U : Set G))
    (hinter : V ⊓ I.pCoreIn 2 = V ⊓ H.pCoreIn 2)
    (hcomm : ⁅R,I⁆ ≤ R.pCoreIn 2)
    {fq : R →* MathieuCode.M22Quintet.Q}
    (hs : M22FiveSection R (V ⊓ I.pCoreIn 2) U fq)
    (hm : M22CodePairMultiplicityAction R I V U i fq)
    (hc : Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2))) :
    let N := normalizer (U : Set G)
    let J := SmallRows.localImage U (R ⊔ H)
    let B := SmallRows.localImage U (V ⊓ I.pCoreIn 2)
    let D := SmallRows.localImage U R
    let W := ⁅B.subgroupOf J,D.subgroupOf J⁆
    let E := normalClosure (W : Set J)
    let hVI : V ≤ I := s.generate ▸ le_sup_left
    ∃ t : I →* J,
      (∀ x, (t x : N ⧸ U.subgroupOf N) = QuotientGroup.mk' (U.subgroupOf N)
        ⟨x.val,hHU (s.family.le_ambient x.property)⟩) ∧
      ∃ A C : NormalNode J,
        (frattini E).map E.subtype ≤ A.val ∧ A ⋖ C ∧ C.val ≤ E ∧
          C.val ≤ pCore 2 J ∧
          (NoncentralChiefRefinement.sectionAction A C).comp
            (t.comp (pResidual 2 I).subtype) ≠ 1 ∧
          W ≤ C.val ∧ W ⊓ A.val = ⊥ ∧
          ∃ hEl : IsElementaryAbelian 2 (Section A C), letI := hEl
            ∃ hRU : R ≤ normalizer (U : Set G),
              ∃ (a : R →* J) (r : R →* alternatingGroup (Fin 5)),
                (∀ x, (a x : N ⧸ U.subgroupOf N) = QuotientGroup.mk' (U.subgroupOf N)
                  ⟨x.val,hRU x.property⟩) ∧
                Function.Surjective r ∧ r.ker = pCore 2 R ∧
                (∀ x, (r x).val = NaturalQuotient.q (fq x)) ∧
                ∃ v : V, (t (inclusion hVI v))^2=1 ∧
                  M22NaturalChiefDisplacement (binarySectionRepresentation A C) a r (t (inclusion hVI v)) ∧
                  M22ChiefDisplacementStable (binarySectionRepresentation A C)
                    (t (inclusion hVI v)) W := by
  let N := normalizer (U : Set G)
  let J := SmallRows.localImage U (R ⊔ H)
  let B := SmallRows.localImage U (V ⊓ I.pCoreIn 2)
  let D := SmallRows.localImage U R
  let W := ⁅B.subgroupOf J,D.subgroupOf J⁆
  let E := normalClosure (W : Set J)
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  obtain ⟨t,ht,A,C,hφA,hAC,hCE,hCcore,hactive,hWC,hWA,v,hv⟩ :=
    selected_m22_active_chief_seed s hH hTV hHR hRP hPH hHU hinter hs hm hc
  have hCp : IsPGroup 2 C.val := pCore_isPGroup.to_le hCcore
  let hEl := chief_elementary A C hAC hCp
  let := hEl
  let ρ := binarySectionRepresentation A C
  let : IsIrreducible ρ := binarySection_irreducible A C hAC
  have hkill : pCore 2 J ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  have hv' : ρ (t (inclusion hVI v)) ≠ 1 := by
    intro he
    apply hv
    apply MulEquiv.ext
    intro x
    exact congrArg Additive.toMul (LinearMap.congr_fun he (Additive.ofMul x))
  have hvJ : t (inclusion hVI v) ∈ (SmallRows.localImage U V).subgroupOf J := by
    refine ⟨⟨v.val,hHU (s.family.le_ambient (hVI v.property))⟩,v.property,?_⟩
    exact (ht (inclusion hVI v)).symm
  have hmove : ⁅C.val,zpowers (t (inclusion hVI v))⁆ ≤ W :=
    (commutator_mono hCE (zpowers_le.mpr hvJ)).trans
      (selected_m22_normalClosure_displacement s hH hTV hHR hRP hPH hHU hinter hs)
  have hBL : V ⊓ I.pCoreIn 2 ≤ R ⊔ H :=
    inf_le_right.trans ((pCoreIn_le 2 I).trans (s.family.le_ambient.trans le_sup_right))
  obtain ⟨hRU,a,r,ha,hrs,hrker,hrval,hnat⟩ :=
    m22_five_chief_natural_displacement (V ⊓ I.pCoreIn 2) R I H U fq hs hBL
      s.family.le_ambient hHR hHU hcomm t ht A C hkill hWC hWA
      (inclusion hVI v) hv' hmove
  have hv2 : v^2=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 V) v
  have hy2 : (t (inclusion hVI v))^2=1 := by
    rw [←map_pow,←map_pow,hv2,map_one,map_one]
  exact ⟨t,ht,A,C,hφA,hAC,hCE,hCcore,hactive,hWC,hWA,hEl,hRU,a,r,ha,hrs,hrker,hrval,v,hy2,hnat⟩

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
