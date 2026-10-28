module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeChiefNatural
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeChiefHomogeneous
import all CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeChiefNatural

/-!
# Homogeneous natural coordinates on the original selected M22 chief

The original R-image is normal in the image of RH. The original I-action
commutes with it modulo its full two-core, and source case I makes T
preserve B=V∩O₂(H), hence the moved commutator seed. Since H is generated
by the unchanged I and T, the natural chief displacement yields homogeneous
coordinates with at least two natural copies. All original markings,
quotient maps, kernels, chosen pair and chief interval are retained.

The internal import shares the literal quotient-commutation transport.
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

private theorem local_actor_range
    {G : Type*} [Group G] (U L X : Subgroup G)
    (hXN : X ≤ normalizer (U : Set G))
    (a : X →* SmallRows.localImage U L)
    (ha : ∀ x, (a x : normalizer (U : Set G) ⧸ U.subgroupOf (normalizer (U : Set G))) =
      QuotientGroup.mk' (U.subgroupOf (normalizer (U : Set G))) ⟨x.val,hXN x.property⟩) :
    a.range = (SmallRows.localImage U X).subgroupOf (SmallRows.localImage U L) := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨⟨x.val,hXN x.property⟩,x.property,(ha x).symm⟩
  · rintro ⟨x,hx,hxz⟩
    refine ⟨⟨x.val,hx⟩,?_⟩
    apply Subtype.ext
    exact (ha ⟨x.val,hx⟩).trans hxz

private theorem local_image_normalizes
    {G : Type*} [Group G] (U B P : Subgroup G)
    (hPB : P ≤ normalizer (B : Set G)) :
    SmallRows.localImage U P ≤ normalizer (SmallRows.localImage U B : Set _) := by
  let N := normalizer (U : Set G)
  have hn : P.subgroupOf N ≤ normalizer (B.subgroupOf N : Set N) :=
    (subgroupOf_mono N hPB).trans (le_normalizer_comap N.subtype)
  exact (map_mono hn).trans (le_normalizer_map (QuotientGroup.mk' (U.subgroupOf N)))

private theorem normalizes_commutator_of_normalizes
    {A : Type*} [Group A] (P B D : Subgroup A)
    (hPB : P ≤ normalizer (B : Set A)) (hPD : P ≤ normalizer (D : Set A)) :
    P ≤ normalizer ((⁅B,D⁆ : Subgroup A) : Set A) := by
  intro z hz
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hPB hz),
    mem_normalizer_iff_map_conj_eq.mp (hPD hz)]

private theorem selected_m22_chief_homogeneous_coordinates
    {G Z : Type*} [Group G] [Finite G] [AddCommGroup Z] [Module (ZMod 2) Z]
    [FiniteDimensional (ZMod 2) Z]
    {V H M I R U : Subgroup G} {T : Sylow 2 G}
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 U]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hHR : H ≤ normalizer (R : Set G))
    (hHU : H ≤ normalizer (U : Set G)) (hRU : R ≤ normalizer (U : Set G))
    (hinter : V ⊓ I.pCoreIn 2 = V ⊓ H.pCoreIn 2)
    (hcomm : ⁅R,I⁆ ≤ R.pCoreIn 2)
    (ρ : Representation (ZMod 2) (SmallRows.localImage U (R ⊔ H)) Z) [IsIrreducible ρ]
    (hkill : pCore 2 (SmallRows.localImage U (R ⊔ H)) ≤ ρ.ker)
    (a : R →* SmallRows.localImage U (R ⊔ H))
    (t : I →* SmallRows.localImage U (R ⊔ H))
    (ha : ∀ x, (a x : normalizer (U : Set G) ⧸ U.subgroupOf (normalizer (U : Set G))) =
      QuotientGroup.mk' (U.subgroupOf (normalizer (U : Set G))) ⟨x.val,hRU x.property⟩)
    (ht : ∀ x, (t x : normalizer (U : Set G) ⧸ U.subgroupOf (normalizer (U : Set G))) =
      QuotientGroup.mk' (U.subgroupOf (normalizer (U : Set G)))
        ⟨x.val,hHU (s.family.le_ambient x.property)⟩)
    (r : R →* alternatingGroup (Fin 5)) (y : SmallRows.localImage U (R ⊔ H))
    (hnat : M22NaturalChiefDisplacement ρ a r y)
    (hstable : M22ChiefDisplacementStable ρ y
      ⁅(SmallRows.localImage U (V ⊓ I.pCoreIn 2)).subgroupOf (SmallRows.localImage U (R ⊔ H)),
        (SmallRows.localImage U R).subgroupOf (SmallRows.localImage U (R ⊔ H))⁆) :
    ∃ m : ℕ, ∃ e : Z ≃ₗ[ZMod 2] (Fin m → (Fin 2 → GaloisField 2 2)),
      (∀ x z, e (ρ (a x) z) =
        fun j => specialLinearNatural 2 (fiveMovedSL2Marking (r x)) (e z j)) ∧
      Module.finrank (ZMod 2) Z = m * 4 := by
  let N := normalizer (U : Set G)
  let q := QuotientGroup.mk' (U.subgroupOf N)
  let J := SmallRows.localImage U (R ⊔ H)
  let Bq := SmallRows.localImage U (V ⊓ I.pCoreIn 2)
  let Dq := SmallRows.localImage U R
  let Iq := SmallRows.localImage U I
  let Pq := SmallRows.localImage U (T : Subgroup G)
  let P := Pq.subgroupOf J
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hIN : I ≤ N := s.family.le_ambient.trans hHU
  have hTN : (T : Subgroup G) ≤ N := hTH.trans hHU
  have har : a.range = Dq.subgroupOf J := local_actor_range U (R ⊔ H) R hRU a ha
  have htr : t.range = Iq.subgroupOf J := local_actor_range U (R ⊔ H) I hIN t ht
  have hDJ : Dq ≤ J := map_mono (subgroupOf_mono N le_sup_left)
  have hIJ : Iq ≤ J := map_mono (subgroupOf_mono N (s.family.le_ambient.trans le_sup_right))
  have hPJ : Pq ≤ J := map_mono (subgroupOf_mono N (hTH.trans le_sup_right))
  have hJD : J ≤ normalizer (Dq : Set _) :=
    local_image_normalizes U R (R ⊔ H) (sup_le R.le_normalizer hHR)
  let : a.range.Normal := har ▸ (normal_subgroupOf_iff_le_normalizer hDJ).mpr hJD
  have hgen : (a.range ⊔ t.range) ⊔ P = ⊤ := by
    rw [har,htr]
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hDJ,map_subgroupOf_eq_of_le hIJ,
      map_subgroupOf_eq_of_le hPJ,←MonoidHom.range_eq_map,range_subtype]
    change ((R.subgroupOf N).map q ⊔ (I.subgroupOf N).map q) ⊔
      ((T : Subgroup G).subgroupOf N).map q = ((R ⊔ H).subgroupOf N).map q
    rw [←Subgroup.map_sup,←Subgroup.map_sup,←subgroupOf_sup hRU hIN,
      ←subgroupOf_sup (sup_le hRU hIN) hTN,sup_assoc,selected_generates_hstar s hH]
  have hC : ∀ c ∈ t.range, ∀ x : R, Commute (ρ c) (ρ (a x)) := by
    rintro c ⟨x,rfl⟩ r'
    exact local_actions_commute_of_commutator_core R I H U s.family.le_ambient hHR
      hRU hHU hcomm a t ha ht ρ hkill x r'
  have hTB : (T : Subgroup G) ≤ normalizer ((V ⊓ I.pCoreIn 2 : Subgroup G) : Set G) := by
    rw [hinter]
    exact (le_inf hTV (hTH.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))).trans
        inf_normalizer_le_normalizer_inf
  have hPB : P ≤ normalizer (Bq.subgroupOf J : Set J) :=
    (subgroupOf_mono J (local_image_normalizes U _ _ hTB)).trans (le_normalizer_comap J.subtype)
  have hPD : P ≤ normalizer (Dq.subgroupOf J : Set J) :=
    (subgroupOf_mono J (local_image_normalizes U _ _ (hTH.trans hHR))).trans
      (le_normalizer_comap J.subtype)
  have hPW := normalizes_commutator_of_normalizes P (Bq.subgroupOf J) (Dq.subgroupOf J) hPB hPD
  exact M22NaturalChiefDisplacement.homogeneous_coordinates ρ a r y hnat t.range P hgen hC (fun p hp => hstable p (hPW hp))

theorem selected_m22_active_chief_homogeneous
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
                    (t (inclusion hVI v)) W ∧
                  M22NaturalHomogeneousCoordinates (binarySectionRepresentation A C) a r := by
  obtain ⟨t,ht,A,C,hφA,hAC,hCE,hCcore,hactive,hWC,hWA,hEl,hRU,a,r,ha,hrs,hrker,hrval,v,hy2,hnat,hstable⟩ :=
    selected_m22_active_chief_natural_displacement s hH hTV hHR hRP hPH hHU hinter hcomm hs hm hc
  let := hEl
  let ρ := binarySectionRepresentation A C
  let : IsIrreducible ρ := binarySection_irreducible A C hAC
  have hkill := normal_p_subgroup_le_ker ρ (pCore 2 _) pCore_isPGroup
  obtain ⟨m,e,he,hd⟩ := selected_m22_chief_homogeneous_coordinates s hH hTV hHR hHU hRU
    hinter hcomm ρ hkill a t ha ht r _ hnat hstable
  have hfour : Module.finrank (ZMod 2) (LinearMap.range (ρ (t (inclusion (s.generate ▸ le_sup_left) v))-1))=4 :=
    hnat.choose_spec.2.2.1
  have hcoord := natural_homogeneous_coordinates_of_marking ρ a r hrs hrker _ hy2 hfour m e he hd
  exact ⟨t,ht,A,C,hφA,hAC,hCE,hCcore,hactive,hWC,hWA,hEl,hRU,a,r,ha,hrs,hrker,hrval,
    v,hy2,hnat,hstable,hcoord⟩

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
