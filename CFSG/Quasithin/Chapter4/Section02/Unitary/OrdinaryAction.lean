module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.OrdinaryOrder
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.PCoreImage
/-!
# The faithful module action in the original ordinary component quotient

The component center is a two-group. Restricting its quotient map therefore
preserves the original seed quotient by O₂, with its formula on every seed
element. The image of the source module centralizes the image seed's two-core.
When the seed is normal in the original local subgroup, simplicity and full
movement make this two-core exactly the conjugation kernel. The resulting
faithful action image is identified with the original G₂(2)′ marking.

These are local action and transport steps for the remaining J₄/Rudvalis
inspection, not a recognition of either row. The actual original odd-actor
consumer is OriginalOddNormalizer.MarkedAction.
Source: Aschbacher–Smith C.3.1 and 4.2.12–13, pp.149–151,610–612.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}
local notation "D" => commutator (Atlas.G2.Model (ZMod 2))

/-- The seed quotient survives the literal central quotient, with its marking. -/
theorem unitary_ordinary_seed_quotient
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D)
    (K : Subgroup H) (hK : IsComponent H K) :
    let A := (L.subgroupOf H).subgroupOf K
    let q := QuotientGroup.mk' (center K)
    let B := A.map q
    ∃ b : B ⧸ pCore 2 B ≃* D,
      ∀ x : A, b (QuotientGroup.mk' (pCore 2 B) (q.subgroupMap A x)) =
        a (QuotientGroup.mk' (pCore 2 L)
          ⟨x.val.val.val,x.property⟩) := by
  let A := (L.subgroupOf H).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  let B := A.map q
  have hLH := h.component_le.trans h.local_le
  let d : A ≃* L := (subgroupOfEquivOfLe (h.ordinary_component_contains_original K hK)).trans
    (subgroupOfEquivOfLe hLH)
  let f : A →* B := q.subgroupMap A
  have hf := q.subgroupMap_surjective A
  let := hK.2
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)
  have hk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk',hz]
    exact pCore_isPGroup.comap_subtype
  let b := (f.pCoreQuotientEquiv hf hk).symm.trans
    ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans a)
  refine ⟨b,?_⟩
  intro x
  have he : (f.pCoreQuotientEquiv hf hk) (QuotientGroup.mk' (pCore 2 A) x) =
      QuotientGroup.mk' (pCore 2 B) (f x) := rfl
  change b (QuotientGroup.mk' (pCore 2 B) (f x)) = _
  rw [←he]
  change a ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d))
    ((f.pCoreQuotientEquiv hf hk).symm
      ((f.pCoreQuotientEquiv hf hk) (QuotientGroup.mk' (pCore 2 A) x)))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The literal full module image centralizes the source span image two-core. -/
theorem ordinary_module_image_core_centralizes
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) :
    let q := QuotientGroup.mk' (center K)
    let B := (((conjugateSpanBy L M).subgroupOf H).subgroupOf K).map q
    let E := ((V.subgroupOf H).subgroupOf K).map q
    B.pCoreIn 2 ≤ centralizer (E : Set (K ⧸ center K)) := by
  let X := conjugateSpanBy L M
  let A := (X.subgroupOf H).subgroupOf K
  let U := (V.subgroupOf H).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let d : A ≃* X := (subgroupOfEquivOfLe (h.ordinary_span_le K hK)).trans
    (subgroupOfEquivOfLe hXH)
  have hCR : X.pCoreIn 2 ≤ R := by
    rw [←h.span_join_core]
    exact pCoreIn_mono_of_normalizes le_sup_left
      (sup_le X.le_normalizer (h.radical_le.trans (le_normalizer_conjugateSpanBy L M)))
  have hUA : U ≤ centralizer (A.pCoreIn 2 : Set K) := by
    rintro w hw z ⟨x,hx,rfl⟩
    have hx' : d x ∈ pCore 2 X := by
      rw [←pCore_map_iso 2 d]
      exact mem_map_of_mem d.toMonoidHom hx
    have hxR : (x : G) ∈ R := hCR (mem_map_of_mem X.subtype hx')
    obtain ⟨v,hv,hev⟩ := h.module_le_center_radical hw
    have hcomm := congrArg R.subtype (mem_center_iff.mp hv ⟨(x : G),hxR⟩)
    change (x : G) * (v : G) = (v : G) * (x : G) at hcomm
    change (v : G) = (w : G) at hev
    rw [hev] at hcomm
    apply K.subtype_injective
    apply H.subtype_injective
    exact hcomm
  let := hK.2
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk',hz]
    exact pCore_isPGroup
  apply le_centralizer_iff.mp
  change U.map q ≤ centralizer ((A.map q).pCoreIn 2 : Set (K ⧸ center K))
  rw [←map_pCoreIn_of_ker_isPGroup q hk A]
  exact (map_mono hUA).trans (map_centralizer_le_centralizer_image _ _)


/-- The actual module action has kernel O₂ and retains the original quotient map. -/
theorem unitary_ordinary_faithful_module_action
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal) (a : L ⧸ pCore 2 L ≃* D)
    (K : Subgroup H) (hK : IsComponent H K) :
    let A := (L.subgroupOf H).subgroupOf K
    let q := QuotientGroup.mk' (center K)
    let B := A.map q
    let E := ((V.subgroupOf H).subgroupOf K).map q
    ∃ hBE : B ≤ normalizer (E : Set (K ⧸ center K)),
      let ρ := E.normalizerMonoidHom.comp (inclusion hBE)
      ρ.ker = pCore 2 B ∧
      ∃ d : ρ.range ≃* D,
        ∀ x : A, d (ρ.rangeRestrict (q.subgroupMap A x)) =
          a (QuotientGroup.mk' (pCore 2 L) ⟨x.val.val.val,x.property⟩) := by
  let A := (L.subgroupOf H).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  let B := A.map q
  let E := ((V.subgroupOf H).subgroupOf K).map q
  have hspan : conjugateSpanBy L M = L :=
    h.normalized_span_eq ((normal_subgroupOf_iff_le_normalizer h.component_le).mp hn)
  obtain ⟨hperfect,hel,hBE,hmove,hcard,_⟩ := h.unitary_ordinary_module_image a K hK
  rw [hspan] at hperfect hBE hmove
  change B ≤ normalizer (E : Set (K ⧸ center K)) at hBE
  change E = ⁅E,B⁆ at hmove
  change 64 ≤ Nat.card E at hcard
  let ρ := E.normalizerMonoidHom.comp (inclusion hBE)
  have hcore := h.ordinary_module_image_core_centralizes K hK
  dsimp only at hcore
  rw [hspan] at hcore
  have hP : pCore 2 B ≤ ρ.ker := by
    intro b hb
    change inclusion hBE b ∈ E.normalizerMonoidHom.ker
    rw [normalizerMonoidHom_ker]
    exact hcore (mem_map_of_mem B.subtype hb)
  obtain ⟨b,hb⟩ := h.unitary_ordinary_seed_quotient a K hK
  let : IsSimpleGroup D := Atlas.G2.isSimple_commutator_binary
  let : IsSimpleGroup (B ⧸ pCore 2 B) := b.isSimpleGroup
  let ψ := QuotientGroup.lift (pCore 2 B) ρ hP
  have hinj : Function.Injective ψ := by
    apply (MonoidHom.ker_eq_bot_iff ψ).mp
    rcases (inferInstance : ψ.ker.Normal).eq_bot_or_eq_top with hh | hh
    · exact hh
    · have hBC : B ≤ centralizer (E : Set (K ⧸ center K)) := by
        intro x hx
        have hfix : ρ ⟨x,hx⟩ = 1 := by
          exact (show QuotientGroup.mk' (pCore 2 B) ⟨x,hx⟩ ∈ ψ.ker from hh.symm ▸ mem_top _)
        change inclusion hBE ⟨x,hx⟩ ∈ E.normalizerMonoidHom.ker at hfix
        rwa [normalizerMonoidHom_ker] at hfix
      have hz : E = ⊥ := hmove.trans
        (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hBC))
      rw [hz,card_bot] at hcard
      omega
  have hker : ρ.ker = pCore 2 B :=
    ((QuotientGroup.injective_lift_iff _ _ _).mp hinj).symm
  let d : ρ.range ≃* D := (QuotientGroup.quotientKerEquivRange ρ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans b)
  refine ⟨hBE,hker,d,?_⟩
  intro x
  have he : ρ.rangeRestrict (q.subgroupMap A x) =
      (QuotientGroup.quotientKerEquivRange ρ)
        (QuotientGroup.mk' ρ.ker (q.subgroupMap A x)) := rfl
  rw [he]
  change b ((QuotientGroup.quotientMulEquivOfEq hker)
    ((QuotientGroup.quotientKerEquivRange ρ).symm
      ((QuotientGroup.quotientKerEquivRange ρ)
        (QuotientGroup.mk' ρ.ker (q.subgroupMap A x))))) = _
  rw [MulEquiv.symm_apply_apply]
  exact hb x

end CFSG.Quasithin.ChapterC.HypothesisC28
