module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSeedCoordinates
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSeedPlane
public import Theory.Representation.BinaryParabolicExteriorSquare.PointAlignment
public import Theory.Representation.BinaryConjugationSection.DisplacementBound

/-!
# Forced images in the compatible natural and exterior markings

The first tensor gives |U₀:V|=16, so the original orders |V|=16 and
|U_H|=32 make U₀/U_H a three-space. Its actual K₂ actors fill the
point parabolic in the same natural marking. The exterior point-parabolic
calculation therefore forces its image to be 01,02,03.

The index-two V₃ section and H-generation of V_H make the image of V a
nonzero line. The original seed normalizer preserves that line. Three
of its natural plane transvections force the line to be 01. Applications
remove both separate image assumptions from the L₁ span calculation, and
remove the three-space and parabolic-actor assumptions from the literal
same-conjugator intersection.

The compatible exterior action itself is still explicit. Its construction
from the local B.4.13 hypotheses, the second tensor, extra-line movement,
and chief obstruction remain obligations of qt-d-138-linear-four-source.
These results do not complete 13.8.28. Earlier 13.8.27 retains its source
producer qt-d-138-six-g2-source and final 13.8.1 assembly retains
qt-d-1381-source.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.29(3),(5) and 13.8.30, printed p.964.
-/

public section

open Subgroup Representation
open scoped MatrixGroups
open Atlas.Order20160A8.Bivectors (exteriorMap)
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open Representation.BinaryParabolicExteriorSquare.PlaneSpan
open BinaryLinear.OuterCyclic BinaryLinear.FlagCoordinates
variable {G : Type*} [Group G] [Finite G]

/-- The original first-tensor index and point actors force its exterior image. -/
theorem source_U0_exterior_image
    (H UH V1 V2 V : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hπ : Function.Surjective π)
    (hnatural : ∀ h x, ρ h x = (π h).val.mulVec x)
    (h12 : V1 ≤ V2) (h2U : V2 ≤ UH)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {Pi.single 0 1})
    (ξ : Representation (ZMod 2) H Six)
    (p : BinaryConjugationSection H (Source.VH H V) UH ξ)
    (hact : ∀ h x, ξ h x = exteriorMap (π h).val x)
    (hUV : U0 UH V2 ≤ Source.VH H V) (hVU : V ≤ U0 UH V2)
    (hindex : V.relIndex (U0 UH V2) = 16)
    (hV : Nat.card V = 16) (hU : Nat.card UH = 32) :
    p.imageSpace (U0 UH V2) = firstSpace := by
  have hc := relIndex_mul_card_of_le hVU
  rw [hindex,hV] at hc
  have hi := relIndex_mul_card_of_le (UH_le_U0 UH V2)
  rw [hU,←hc] at hi
  have hdim := p.imageSpace_finrank_of_index (U0 UH V2) hUV 3 (by omega)
  apply BinaryParabolicExteriorSquare.PointAlignment.eq_first_of_finrank_three _ _ hdim
  intro i j hj hij x hx
  obtain ⟨k,hk⟩ := source_K2_point_actors H UH V1 V2 ρ d π hπ hnatural
    h12 h2U hpoint i j hj hij
  have hh := p.imageSpace_apply_mem (U0 UH V2)
    (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left) k)
    (G2_normalizes_U0 UH V2 ((K2_le_localNormalizer H V2).trans inf_le_right k.property)) x hx
  rwa [hact,hk] at hh

/-- The original seed plane forces the V-image to be the wedge line 01.
Its one-dimensionality follows from |V:V3|=2 and H-generation of VH. -/
theorem source_V_exterior_image
    (H UH V1 V3 V : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hπ : Function.Surjective π)
    (hnatural : ∀ h x, ρ h x = (π h).val.mulVec x)
    (h13 : V1 ≤ V3) (h3U : V3 ≤ UH)
    (hplane : d.imageSpace V3 = plane)
    (hNV : H ⊓ normalizer (V3:Set G) ≤ normalizer (V:Set G))
    (hindex : V3.relIndex V = 2)
    (ξ : Representation (ZMod 2) H Six)
    (p : BinaryConjugationSection H (Source.VH H V) UH ξ)
    (hact : ∀ h x, ξ h x = exteriorMap (π h).val x) :
    p.imageSpace V = pointSpace := by
  have hne : p.imageSpace V ≠ ⊥ := by
    intro hz
    have ht := p.generated_image_le V rfl (⊥ : Subrepresentation ξ) (by simp [hz])
    change (⊥ : Submodule (ZMod 2) Six) = ⊤ at ht
    have hh := congrArg (fun P : Submodule (ZMod 2) Six => Module.finrank (ZMod 2) P) ht
    simp [BinaryParabolicExteriorSquare.PlaneSpan.Six] at hh
  have hc := p.imageSpace_card_le_relative_index V V3 h3U
  rw [hindex,Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod] at hc
  have hdim : Module.finrank (ZMod 2) (p.imageSpace V) = 1 := by
    have hp : Module.finrank (ZMod 2) (p.imageSpace V) ≠ 0 :=
      fun hz => hne (Submodule.finrank_eq_zero.mp hz)
    have hb : Module.finrank (ZMod 2) (p.imageSpace V) ≤ 1 :=
      (pow_le_pow_iff_right₀ (by decide : (1:ℕ) < 2)).mp hc
    omega
  have hfixed (a : H) (ha : (a:G) ∈ normalizer (V3:Set G))
      (w : Six) (hw : w ∈ p.imageSpace V) : ξ a w = w := by
    by_cases hw0 : w = 0
    · simp [hw0]
    have hs := eq_span_singleton_of_mem_of_finrank_eq_one hdim hw hw0
    have hh := p.imageSpace_apply_mem V a (hNV ⟨a.property,ha⟩) w hw
    rw [hs] at hh
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hh
    have hc0 : c ≠ 0 := by
      intro he
      have hz : ξ a w = 0 := by simpa [he] using hc.symm
      have hz' := congrArg (ξ a⁻¹) hz
      rw [Representation.inv_self_apply,map_zero] at hz'
      exact hw0 hz'
    have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
    simpa only [hc1,one_smul] using hc.symm
  let φ := (slEquivLinear 4).toMonoidHom.comp π
  have hn (a : H) : (a:G) ∈ normalizer (V3:Set G) ↔ φ a ∈ BinaryLinear.parabolic plane := by
    rw [←hplane]
    exact d.natural_normalizer_iff φ
      (fun a w => (hnatural a w).trans (slEquivLinear_apply 4 (π a) w).symm) V3 h3U h13 a
  have htrans (i j : Fin 4) (hi : i = 0 ∨ i = 1) (hij : i ≠ j)
      (w : Six) (hw : w ∈ p.imageSpace V) :
      exteriorMap (Matrix.transvection i j (1:ZMod 2)) w = w := by
    obtain ⟨a,ha⟩ := hπ (Matrix.SpecialLinearGroup.transvection hij 1)
    have haN : (a:G) ∈ normalizer (V3:Set G) := by
      apply (hn a).mpr
      intro v
      change (slEquivLinear 4 (π a)) v ∈ plane ↔ v ∈ plane
      rw [ha,slEquivLinear_apply]
      rcases hi with rfl | rfl <;>
        simp [plane,Matrix.SpecialLinearGroup.transvection_coe,
          Matrix.add_mulVec,Matrix.single_mulVec_eq]
    have hh := hfixed a haN w hw
    rwa [hact,ha,Matrix.SpecialLinearGroup.transvection_coe] at hh
  have hle : p.imageSpace V ≤ pointSpace := by
    intro w hw
    exact BinaryParabolicExteriorSquare.PointAlignment.mem_point_of_fixed w
      (htrans 0 1 (Or.inl rfl) (by decide) w hw)
      (htrans 1 0 (Or.inr rfl) (by decide) w hw)
      (htrans 0 2 (Or.inl rfl) (by decide) w hw)
  obtain ⟨w,hw,hw0⟩ := (Submodule.ne_bot_iff _).mp hne
  have hwP := hle hw
  have hw01 : w 0 = 1 := by
    have h0 : w 0 ≠ 0 := by
      intro he
      apply hw0
      ext i
      fin_cases i <;> simp_all [pointSpace]
    exact ((by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (w 0)).resolve_left h0
  have hwE : w = Pi.single 0 1 := by
    ext i
    fin_cases i <;> simp_all [pointSpace]
  apply le_antisymm hle
  intro x hx
  have he : x = x 0 • w := by
    rw [hwE]
    ext i
    fin_cases i <;> simp_all [pointSpace]
  rw [he]
  exact Submodule.smul_mem _ _ hw

open SourceCompletion TransvectionRecognition.Component.ModelExtension
variable {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}

/-- The original seed tensor now gives the literal VH intersection without
assuming its exterior three-space or separate parabolic lifts. The same π₄
marks the natural and exterior actions, and g is the supplied source actor. -/
theorem source_tensor_intersection_with_forced_exterior_image
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    {K U : Type*} [Group K] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (H UH A L2 : Subgroup G) [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 (Source.VH H V)]
    (hH : H = normalizer (V₁:Set G))
    (hK : ((K2 H V₂).subgroupOf (G2 V₂)).Normal)
    (hG : G2 V₂ = K2 H V₂ ⊔ L2 ⊔ (T:Subgroup G))
    (hV : L2 ⊔ (T:Subgroup G) ≤ normalizer (V:Set G))
    (π : G2 V₂ →* K × Equiv.Perm (Fin 3)) (hπ : Function.Surjective π)
    (hπker : π.ker = pCore 2 (G2 V₂)) (hcore : Q2 V₂ ≤ H)
    (σ : Representation (ZMod 2) K U)
    (κ : ↥(H ⊓ G2 V₂) →* K)
    (dU : BinaryConjugationSection (H ⊓ G2 V₂) UH V₂ (σ.comp κ))
    (hκker : κ.ker = pCore 2 ↥(H ⊓ G2 V₂))
    (hκ : Function.Surjective (κ.comp (inclusion (K2_le_localNormalizer H V₂))))
    (hπK : ∀ k : K2 H V₂,
      π (inclusion ((K2_le_localNormalizer H V₂).trans inf_le_right) k) =
        (κ (inclusion (K2_le_localNormalizer H V₂) k),1))
    (eI : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (hAcore : A.pCoreIn 2 = A ⊓ centralizer (V₂:Set G))
    (hALT : A ≤ L ⊔ (T:Subgroup G)) (hVA : V ≤ A) (hAG : A ≤ G2 V₂)
    (hπI : ∀ a : A, π (inclusion hAG a) = (1,eI (QuotientGroup.mk' (pCore 2 A) a)))
    (h3U : V₃ ≤ UH) (hgen : UH = conjugateSpanBy V₃ (K2 H V₂))
    (hdim : Module.finrank (ZMod 2) U = 3)
    (g : A) (hg : (g:G) ∉ H)
    (ξ : Representation (ZMod 2) H BinaryParabolicExteriorSquare.PlaneSpan.Six)
    (dx : BinaryConjugationSection H (Source.VH H V) UH ξ)
    (π₄ : H →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (hπ₄ : Function.Surjective π₄)
    (ρ₄ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d₄ : BinaryConjugationSection H UH V₁ ρ₄)
    (hnatural : ∀ h x, ρ₄ h x = (π₄ h).val.mulVec x)
    (hpoint : d₄.imageSpace V₂ = Submodule.span (ZMod 2) {Pi.single 0 1})
    (hUcard : Nat.card UH = 32)
    (hact : ∀ h x, ξ h x = Atlas.Order20160A8.Bivectors.exteriorMap (π₄ h).val x)
    (hne : Source.VH H V ≠ ⊥)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T:Subgroup G) ≤ N → N = M)
    (hHM : ¬ H ≤ M) (hgenerate : L ⊔ (T:Subgroup G) ≤ H ⊔ zpowers (g:G)) :
    Source.VH H V ⊓ (Source.VH H V).conjBy ((g:G)⁻¹) = U0 UH V₂ := by
  obtain ⟨_,_,hVS,_,_,_,_,_,hprod,_,hindex⟩ := source_tensor_from_original_seed d
    H UH A L2 hH hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK
    eI hAcore hALT hVA hAG hπI h3U hgen hdim g hg
  have hUV := source_U0_le_VH_of_normal_factors H UH V₂ V₃ V L2 (T:Subgroup G)
    hK hG hV hgen d.seed_le
  have hVcard : Nat.card V = 16 := by
    rw [Nat.card_congr d.coordinate.toEquiv]
    change Nat.card (BinaryPermutation.natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    rfl
  have hfirst := source_U0_exterior_image H UH V₁ V₂ V ρ₄ d₄ π₄ hπ₄ hnatural
    d.line_le_plane dU.kernel_le hpoint ξ dx hact hUV hVS hindex hVcard hUcard
  have hactors := fun (i j : Fin 4) (_ : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) =>
    source_K2_point_actors H UH V₁ V₂ ρ₄ d₄ π₄ hπ₄ hnatural
      d.line_le_plane dU.kernel_le hpoint i j hj hij
  have hk : π.ker ≤ H.subgroupOf (G2 V₂) := by
    rw [hπker]
    intro x hx
    exact hcore (mem_map_of_mem (G2 V₂).subtype hx)
  have hseed : V₃.conjBy ((g:G)⁻¹) ≤ V := by
    rintro x ⟨v,hv,rfl⟩
    exact (mem_normalizer_iff.mp (d.normalizes_V (hALT g⁻¹.property)) v).mp (d.seed_le hv)
  exact source_tensor_intersection_of_product L (T:Subgroup G) H M UH V₂ V₃ V π hk
    (fun k => congrArg Prod.snd (hπK k)) (inclusion hAG g)
    (congrArg Prod.fst (hπI g)) hgen d.seed_le hseed hprod ξ dx π₄ hact hfirst hactors
    (IsElementaryAbelian.isPGroup 2 _) hne hu hHM hgenerate



open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement

/-- The original normalizer and first tensor force both exterior images and
feed the actual L₁-conjugate span and index-64 calculation. -/
theorem source_cubic_span_with_forced_exterior_images
    {H : Subgroup G}
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π : H →* SL(4,ZMod 2))
    (hker : π.ker = (Source.QH H).subgroupOf H)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hpoint : d.imageSpace V₂ = Submodule.span (ZMod 2) {Pi.single 0 1})
    (hplane : d.imageSpace V₃ = plane)
    (ξ : Representation (ZMod 2) H Six)
    (p : BinaryConjugationSection H (Source.VH H V) (Source.UH H V₃) ξ)
    (hexterior : ∀ h w, ξ h w = exteriorMap (π h).val w)
    (hUV : U0 (Source.UH H V₃) V₂ ≤ Source.VH H V)
    (hVU : V ≤ U0 (Source.UH H V₃) V₂)
    (hindex : V.relIndex (U0 (Source.UH H V₃) V₂) = 16)
    (hUcard : Nat.card (Source.UH H V₃) = 32) :
    p.imageSpace V = pointSpace ∧
    p.imageSpace (U0 (Source.UH H V₃) V₂) = firstSpace ∧
    p.imageSpace (conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁)) = planeSpace ∧
    V.relIndex (conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁)) = 64 := by
  have hVcard : Nat.card V = 16 := by
    rw [Nat.card_congr s.coordinate.toEquiv]
    change Nat.card (BinaryPermutation.natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    rfl
  have hi : V₃.relIndex V = 2 := by
    have hh := relIndex_mul_card_of_le s.seed_le
    rw [s.seed_card,hVcard] at hh
    omega
  have hNV : H ⊓ normalizer (V₃:Set G) ≤ normalizer (V:Set G) :=
    (source_seed_normalizer_le_LT s h hH hcentral ρ d π hker hnatural).trans s.normalizes_V
  have hv := source_V_exterior_image H (Source.UH H V₃) V₁ V₃ V
    ρ d π honto hnatural (s.line_le_plane.trans s.plane_le_seed)
    (le_conjugateSpanBy _ _) hplane hNV hi ξ p hexterior
  have hf := source_U0_exterior_image H (Source.UH H V₃) V₁ V₂ V
    ρ d π honto hnatural s.line_le_plane (s.plane_le_seed.trans (le_conjugateSpanBy _ _))
    hpoint ξ p hexterior hUV hVU hindex hVcard hUcard
  have hk : IsPGroup 2 π.ker := by
    rw [hker]
    exact (isPGroup_pCoreIn 2 H).comap_subtype
  exact ⟨hv,hf,source_cubic_span_of_original_seed s h hH hcentral ρ d π hk honto
    hnatural hplane ξ p hexterior hUV hf hVU hindex⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour
