module
public import Theory.SpecificGroups.BinaryLinear.RadicalHyperplane
public import Theory.Representation.BinaryConjugationSection.NaturalNormalizer
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.StrictImages
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.EdgeCores

/-!
# The critical upper image from the actual seed-normalizer two-core

The natural marking identifies N_H(V₃)'s image with the stabilizer of the
literal plane V₃/V₁. Its two-core acts in that plane's geometric radical.
Fixing the reciprocal natural hyperplane bounds the upper critical image
by four; strict containment of the image of order two gives equality.
This constructs the reciprocal exterior hyperplane and proves 13.8.32.

The actual CriticalPair application uses the proved F.9 edge-core theorem
on its shortest path. The inverse of its retained conjugator transports
the terminal edge core into the original seed normalizer. Both endpoint
containments, strict image inclusion and the kernel commutator are derived.
The terminal application uses the resulting indices and critical line in
the original H_C/V_H chief-section contradiction.

The natural/exterior markings, excluded lines, earlier seed-normalizer
bound N_H(V₃) ≤ LT and the 13.8.31 chief obstruction remain explicit. The
marking and chief-factor work remains with qt-d-138-linear-four-source;
earlier 13.8.27 setup belongs to qt-d-138-six-g2-source, and final 13.8.1
assembly to qt-d-1381-source. This increment does not complete 13.8.28.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
F.9.13(1–2) and 13.8.32(3), printed pp.322,965–966.
-/

public noncomputable section
open Subgroup Representation
open BinaryLinear.OuterCyclic
open scoped MatrixGroups
open Atlas.Order20160A8.Bivectors (exteriorMap)
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G : Type*} [Group G] [Finite G]

/-- The literal seed-normalizer two-core and fixed axis give the upper
critical image of order four through the original natural quotient. -/
theorem source_critical_upper_image_four_of_seed_core
    (H UH V1 V3 DH QH Uγ Vγ : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hV1V3 : V1 ≤ V3) (hV3U : V3 ≤ UH) (hplane : V1.relIndex V3 = 4)
    (hV1D : V1 ≤ DH) (hDU : DH ≤ UH) (hindex : DH.relIndex UH = 2)
    (hUγH : Uγ ≤ H) (hVγH : Vγ ≤ H)
    (hstar : QH.relIndex Uγ = 2)
    (hstrict : (Uγ.subgroupOf H).map π < (Vγ.subgroupOf H).map π)
    (hcentral : Vγ ≤ centralizer (DH:Set G))
    (hcore : Vγ ≤ (H ⊓ normalizer (V3:Set G)).pCoreIn 2) :
    QH.relIndex Vγ = 4 := by
  let f := (slEquivLinear 4).toMonoidHom.comp π
  let P := d.imageSpace V3
  let D := d.imageSpace DH
  let A := (Vγ.subgroupOf H).map f
  have hp : Module.finrank (ZMod 2) P = 2 :=
    d.imageSpace_finrank_of_index V3 hV3U 2 (by simpa using hplane)
  have hd : Module.finrank (ZMod 2) D + 1 = Module.finrank (ZMod 2) (Fin 4 → ZMod 2) :=
    d.imageSpace_codimension_of_index DH hDU hV1D 1 (by simpa using hindex)
  have hrad : A ≤ BinaryLinear.radical P :=
    (map_mono (subgroupOf_mono H hcore)).trans
      (d.natural_normalizer_core_image f hnatural ((slEquivLinear 4).surjective.comp honto)
        V3 hV3U hV1V3)
  have hfix (a : A) (w : Fin 4 → ZMod 2) (hw : w ∈ D) : a.val w = w := by
    obtain ⟨b,hb,he⟩ := a.property
    obtain ⟨x,hx,hxw⟩ := (d.mem_imageSpace_iff DH w).mp hw
    have heq : (⟨(b:G)*x*(b:G)⁻¹,
        (mem_normalizer_iff.mp (d.normalized b.property) x).mp x.property⟩ : UH) = x := by
      apply Subtype.ext
      have hc : (x:G)*(b:G) = (b:G)*x := hcentral hb x hx
      change (b:G)*(x:G)*(b:G)⁻¹ = (x:G)
      rw [←hc,mul_assoc,mul_inv_cancel,mul_one]
    have hh := d.equivariant b x
    rw [heq,hxw,hnatural] at hh
    change w = f b w at hh
    rw [he] at hh
    exact hh.symm
  have hc := BinaryLinear.radical_fixed_hyperplane_card_bound P D hd A hrad hfix
  have heA : Nat.card A = QH.relIndex Vγ := by
    change Nat.card ((Vγ.subgroupOf H).map ((slEquivLinear 4).toMonoidHom.comp π)) = _
    rw [←map_map,card_map_of_injective (slEquivLinear 4).injective,
      ←relIndex_ker,hker,relIndex_subgroupOf hVγH]
  rw [hp,heA] at hc
  have hsmall : Nat.card ((Uγ.subgroupOf H).map π) = 2 := by
    rw [←relIndex_ker,hker,relIndex_subgroupOf hUγH,hstar]
  have hbig : Nat.card ((Vγ.subgroupOf H).map π) = QH.relIndex Vγ := by
    rw [←relIndex_ker,hker,relIndex_subgroupOf hVγH]
  have hne : QH.relIndex Vγ ≠ 2 := by
    intro he
    exact hstrict.ne (eq_of_le_of_card_ge hstrict.le (by rw [hsmall,hbig,he]))
  have hdvd := card_dvd_of_le hstrict.le
  rw [hsmall,hbig] at hdvd
  have hpos := Nat.card_pos (α := (Vγ.subgroupOf H).map π)
  rw [hbig] at hpos
  norm_num at hc
  omega

/-- The reciprocal seed two-core supplies the upper bound in the actual critical geometry. -/
theorem source_critical_geometry_of_seed_core
    (H UH V1 V3 V QH VH : Subgroup G) [IsElementaryAbelian 2 UH]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (ξ : Representation (ZMod 2) H (Fin 6 → ZMod 2))
    (dx : BinaryConjugationSection H VH UH ξ)
    (hexterior : ∀ h w, ξ h w = exteriorMap (π h).val w)
    (hV1 : Nat.card V1 = 2) (hVQ : VH ≤ QH)
    (hspanU : UH = conjugateSpanBy V3 H) (hspanV : VH = conjugateSpanBy V H)
    (hseed : ⁅centralizer (V3:Set G),V⁆ ≤ V1)
    (hV1V3 : V1 ≤ V3) (hV3U : V3 ≤ UH) (hplane : V1.relIndex V3 = 4)
    (y : G) (hforward : VH.conjBy y ≤ H) (hback : VH.conjBy y⁻¹ ≤ H)
    (houtside : ¬ UH.conjBy y ≤ QH)
    (hline : ¬ V1.conjBy y ≤ UH) (hbackline : ¬ V1 ≤ UH.conjBy y)
    (hstrict : ((UH.conjBy y⁻¹).subgroupOf H).map π <
      ((VH.conjBy y⁻¹).subgroupOf H).map π)
    (hcore : VH.conjBy y⁻¹ ≤ (H ⊓ normalizer (V3:Set G)).pCoreIn 2)
    (hcommE : ⁅UH.conjBy y,VH ⊓ QH.conjBy y⁆ ≤ V1.conjBy y) :
    QH.relIndex (UH.conjBy y) = 2 ∧
      8 ≤ Nat.card (UH.conjBy y ⊓ VH : Subgroup G) ∧ V1.conjBy y ≤ VH := by
  let : IsElementaryAbelian 2 (UH.conjBy y) := IsElementaryAbelian.map _
  have hf : UH.conjBy y ≤ H := (map_mono dx.kernel_le).trans hforward
  have hb : UH.conjBy y⁻¹ ≤ H := (map_mono dx.kernel_le).trans hback
  have hn : VH ≤ normalizer (UH.conjBy y : Set G) :=
    by
      have hh := (map_mono (f := (MulAut.conj y).toMonoidHom) (hback.trans d.normalized)).trans
        (UH.le_normalizer_map (MulAut.conj y).toMonoidHom)
      change (VH.conjBy y⁻¹).conjBy y ≤ _ at hh
      rwa [conjBy_inv'] at hh
  have hm : UH.conjBy y ⊓ UH ≠ ⊥ := d.inf_ne_bot_of_action_kernel QH (UH.conjBy y)
    (source_natural_action_kernel H QH ρ π hker hnatural) hf (dx.kernel_le.trans hn) houtside
  have hc : ⁅UH.conjBy y,VH⁆ ≤ UH.conjBy y ⊓ VH := le_inf
    (le_normalizer_iff_commutator_le_left.mp hn)
    (le_normalizer_iff_commutator_le_right.mp (hf.trans dx.normalized))
  have hindices := source_critical_indices_of_mutual_markings H UH V1 QH VH
    ρ d π hker hnatural ξ dx hexterior hV1 hVQ y hf hback houtside
  have hbackoutside := source_inverse_critical_image_nontrivial H UH V1 QH
    ρ d π hker hnatural hV1 y hf hb houtside hline
  have hreverse := source_critical_indices_of_mutual_markings H UH V1 QH VH
    ρ d π hker hnatural ξ dx hexterior hV1 hVQ y⁻¹ hb (by simpa using hforward) hbackoutside
  have hlower : (QH.conjBy y).relIndex UH = 2 := by
    have hh := relIndex_map_map_of_injective (f := (MulAut.conj y).toMonoidHom)
      QH (UH.conjBy y⁻¹) (MulAut.conj y).injective
    change (QH.conjBy y).relIndex ((UH.conjBy y⁻¹).conjBy y) = _ at hh
    rw [conjBy_inv',hreverse.1] at hh
    exact hh
  have hn1 : H ≤ normalizer (V1:Set G) :=
    (normal_subgroupOf_iff_le_normalizer (d.kernel_le.trans d.section_le)).mp d.kernel_normal_actor
  have hcent1 : H ≤ centralizer (V1:Set G) :=
    hn1.trans (normalizer_le_centralizer_of_card_two V1 hV1)
  let DR := (UH.conjBy y ⊓ QH).conjBy y⁻¹
  obtain ⟨hV1D,hDU,hDindex,haxis⟩ := source_reciprocal_natural_axis H UH V1 QH
    ρ d π hker hnatural hV1 hcent1 y hf hb hbackline hindices.1
  have hbackline' : ¬ V1.conjBy y⁻¹ ≤ UH := by
    intro hh
    have ht := map_mono (f := (MulAut.conj y).toMonoidHom) hh
    change (V1.conjBy y⁻¹).conjBy y ≤ UH.conjBy y at ht
    rw [conjBy_inv'] at ht
    exact hbackline ht
  have hcentral : VH.conjBy y⁻¹ ≤ centralizer (DR:Set G) := by
    rw [hspanV]
    exact conjugateSpanBy_centralizes_axis_of_line_not_le H UH V1 V3 V DR hDU
      d.normalized hn1 hspanU hseed hV1 y⁻¹ (by rwa [←hspanV]) haxis hbackline'
  have hU : Nat.card (UH.conjBy y) = 32 := by
    change Nat.card (UH.map _) = 32
    rw [card_map_of_injective (MulAut.conj y).injective,d.card_section,hV1]
    norm_num
  have hA : Nat.card (V1.conjBy y) = 2 :=
    (card_map_of_injective (MulAut.conj y).injective).trans hV1
  have hu := source_critical_upper_image_four_of_seed_core H UH V1 V3 DR QH
    (UH.conjBy y⁻¹) (VH.conjBy y⁻¹) ρ d π hker honto hnatural hV1V3 hV3U hplane
    hV1D hDU hDindex hb hback hreverse.1 hstrict hcentral hcore
  have hi := relIndex_map_map_of_injective (f := (MulAut.conj y).toMonoidHom)
    QH (VH.conjBy y⁻¹) (MulAut.conj y).injective
  change (QH.conjBy y).relIndex ((VH.conjBy y⁻¹).conjBy y) = _ at hi
  rw [conjBy_inv',hu] at hi
  have hh := source_reciprocal_hyperplane_index UH VH (QH.conjBy y)
    dx.kernel_le (dx.section_le.trans d.normalized) hi hlower
  have hcomm := source_hyperplane_commutator H UH (VH ⊓ QH.conjBy y)
    (UH.conjBy y) (V1.conjBy y) d.normalized (inf_le_left.trans dx.section_le) hf hcommE
  exact source_critical_geometry_of_exterior_action H VH UH QH (UH.conjBy y)
    (VH ⊓ QH.conjBy y ⊔ UH) (V1.conjBy y) ξ π hker hexterior dx hf houtside hc
    hVQ hU hm le_sup_right (sup_le inf_le_left dx.kernel_le) hh hcomm
    ((map_mono d.kernel_le).trans hf) hA

open CriticalGeometry NoncentralChiefRefinement

/-- F.9's original terminal edge core transports back by the inverse of
this same critical conjugator into the actual seed-normalizer two-core. -/
theorem source_inverse_critical_seed_core
    (F : ChapterF.Section09.Setup G) (hF : F.Hypothesis)
    (c : CriticalPair F.L (F.T:Subgroup G) F.H F.V) (hb : 3 ≤ c.path.length)
    (hcontrol : F.H ⊓ normalizer (F.Vplus:Set G) ≤ F.LT) :
    (Source.VH F.H F.V).conjBy (c.gb:G)⁻¹ ≤
      (F.H ⊓ normalizer (F.Vplus:Set G)).pCoreIn 2 := by
  have he : F.L₁ ⊔ (F.T:Subgroup G) = F.H ⊓ normalizer (F.Vplus:Set G) := by
    apply le_antisymm (le_inf hF.local_le hF.local_normalizes)
    rw [←hF.LT_inf_H_eq]
    exact le_inf hcontrol inf_le_left
  have hc := (SourceCompletion.f9_endpoint_edge_cores F hF c hb).1
  change Source.VH F.H F.V ≤
    (vertexGroup _ _ _ c.previous ⊓ vertexGroup _ _ _ c.gamma).pCoreIn 2 at hc
  rw [inf_comm] at hc
  change Source.VH F.H F.V ≤ (edgeGroup _ _ _ c.gamma c.previous).pCoreIn 2 at hc
  rw [c.edgeGroup_eq F.L₁ hF.LT_inf_H_eq,←map_pCoreIn_of_ker_isPGroup
    (MulAut.conj (c.gb:G)).toMonoidHom
    (IsPGroup.ker_isPGroup_of_injective (MulAut.conj (c.gb:G)).injective)] at hc
  have hm := map_mono (f := (MulAut.conj (c.gb:G)⁻¹).toMonoidHom) hc
  change (Source.VH F.H F.V).conjBy (c.gb:G)⁻¹ ≤
    (((F.L₁ ⊔ (F.T:Subgroup G)).pCoreIn 2).conjBy (c.gb:G)).conjBy (c.gb:G)⁻¹ at hm
  rwa [conjBy_inv,he] at hm

/-- The source edge cores supply both endpoint containments and the
parabolic bound. Only the original markings and excluded-line inputs
remain in this application of all three clauses of 13.8.32. -/
theorem source_critical_pair_geometry_of_seed_normalizer
    (F : ChapterF.Section09.Setup G) (hF : F.Hypothesis)
    (c : CriticalPair F.L (F.T:Subgroup G) F.H F.V) (hb : 3 ≤ c.path.length)
    [IsElementaryAbelian 2 (Source.VH F.H F.V)]
    (ρ : Representation (ZMod 2) F.H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection F.H (Source.UH F.H F.Vplus) F.V₁ ρ)
    (π : F.H →* SL(4,ZMod 2)) (hker : π.ker = (Source.QH F.H).subgroupOf F.H)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (ξ : Representation (ZMod 2) F.H (Fin 6 → ZMod 2))
    (dx : BinaryConjugationSection F.H (Source.VH F.H F.V) (Source.UH F.H F.Vplus) ξ)
    (hexterior : ∀ h w, ξ h w = exteriorMap (π h).val w)
    (hseed : ⁅centralizer (F.Vplus:Set G),F.V⁆ ≤ F.V₁)
    (hseedcard : Nat.card F.Vplus = 8)
    (hcontrol : F.H ⊓ normalizer (F.Vplus:Set G) ≤ F.LT)
    (houtside : ¬ c.Ugamma F.Vplus ≤ Source.QH F.H)
    (hline : ¬ c.Aone F.V₁ ≤ Source.UH F.H F.Vplus)
    (hbackline : ¬ F.V₁ ≤ c.Ugamma F.Vplus) :
    (Source.QH F.H).relIndex (c.Ugamma F.Vplus) = 2 ∧
      8 ≤ Nat.card (c.Ugamma F.Vplus ⊓ Source.VH F.H F.V : Subgroup G) ∧
      c.Aone F.V₁ ≤ Source.VH F.H F.V := by
  let : IsElementaryAbelian 2 (Source.UH F.H F.Vplus) := IsElementaryAbelian.of_le dx.kernel_le
  have hcores := SourceCompletion.f9_endpoint_edge_cores F hF c hb
  have hf : c.Vgamma ≤ F.H := by
    have hh := hcores.2.trans ((pCoreIn_le 2 _).trans inf_le_left)
    rwa [vertexGroup_base] at hh
  have hb' : (Source.VH F.H F.V).conjBy (c.gb:G)⁻¹ ≤ F.H :=
    (source_inverse_critical_seed_core F hF c hb hcontrol).trans
      ((pCoreIn_le 2 _).trans inf_le_left)
  have hVQ : Source.VH F.H F.V ≤ Source.QH F.H :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _) dx.section_le dx.normalized
  have hQH : Source.QH F.H ≤ F.H := pCoreIn_le 2 F.H
  have hstrict := source_inverse_critical_images_strict F.H (Source.UH F.H F.Vplus) F.V₁
    (Source.QH F.H) (Source.VH F.H F.V) ρ d π hker hnatural ξ dx hexterior hF.point_card
    hQH (c.gb:G) ((map_mono dx.kernel_le).trans hf) hb' houtside
  have hcomm := source_critical_kernel_commutator F.H (Source.UH F.H F.Vplus) F.V₁
    (Source.QH F.H) (Source.VH F.H F.V) ρ d π hker hnatural hQH (c.gb:G)
  have hplane : F.V₁.relIndex F.Vplus = 4 := by
    have hh := (F.V₁.subgroupOf F.Vplus).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hF.point_lt.le).toEquiv,
      hF.point_card,hseedcard] at hh
    change 2 * F.V₁.relIndex F.Vplus = 8 at hh
    omega
  exact source_critical_geometry_of_seed_core F.H (Source.UH F.H F.Vplus) F.V₁ F.Vplus F.V
    (Source.QH F.H) (Source.VH F.H F.V) ρ d π hker honto hnatural ξ dx hexterior
    hF.point_card hVQ rfl rfl hseed hF.point_lt.le (le_conjugateSpanBy _ _) hplane
    (c.gb:G) hf hb' houtside hline hbackline hstrict
    (source_inverse_critical_seed_core F hF c hb hcontrol) hcomm

/-- Terminal exclusion using the source edge two-core, with no separate
plane-radical placement, endpoint containment, strict-image or commutator premise. -/
theorem source_linear_four_exclusion_of_seed_normalizer
    (F : ChapterF.Section09.Setup G) (hF : F.Hypothesis)
    (c : CriticalPair F.L (F.T:Subgroup G) F.H F.V) (hb : 3 ≤ c.path.length)
    (Q R K : Subgroup G)
    [IsElementaryAbelian 2 (Source.VH F.H F.V)]
    (ρ : Representation (ZMod 2) F.H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection F.H (Source.UH F.H F.Vplus) F.V₁ ρ)
    (π : F.H →* SL(4,ZMod 2)) (hker : π.ker = (Source.QH F.H).subgroupOf F.H)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (ξ : Representation (ZMod 2) F.H (Fin 6 → ZMod 2))
    (dx : BinaryConjugationSection F.H (Source.VH F.H F.V) (Source.UH F.H F.Vplus) ξ)
    (hexterior : ∀ h w, ξ h w = exteriorMap (π h).val w)
    (hH : F.H = normalizer (F.V₁:Set G))
    (hseed : ⁅centralizer (F.Vplus:Set G),F.V⁆ ≤ F.V₁)
    (hseedcard : Nat.card F.Vplus = 8)
    (hcontrol : F.H ⊓ normalizer (F.Vplus:Set G) ≤ F.LT)
    (houtside : ¬ c.Ugamma F.Vplus ≤ Source.QH F.H)
    (hline : ¬ c.Aone F.V₁ ≤ Source.UH F.H F.Vplus) (hbackline : ¬ F.V₁ ≤ c.Ugamma F.Vplus)
    (hQR : Source.QH F.H ≤ R) (hindex : Q.relIndex R = 4)
    (hcent : Q ⊓ Source.QH F.H ≤ centralizer (F.Vplus:Set G))
    (hdual : (Source.QH F.H ⊓ centralizer (F.Vplus:Set G)).relIndex (Source.QH F.H) = 4)
    (hQV : Q ≤ centralizer (F.V:Set G))
    (hcover : IsSQTK KnownSimple.IsKnownSimple F.H)
    (e : (F.H ⧸ pCore 2 F.H) ≃* LinearGroup 4)
    (hKH : K ≤ F.H) (hK : IsPPerfect 2 K)
    (hmove : ¬ ⁅Source.HC F.H F.Vplus,K⁆ ≤ Source.VH F.H F.V)
    (hKonto : Function.Surjective
      ((QuotientGroup.mk' (pCore 2 F.H)).comp (K.subgroupOf F.H).subtype))
    (hnotfour : ∀ s : ChiefSeries F.H,
      s.head.val.map F.H.subtype = Source.VH F.H F.V → s.last.val.map F.H.subtype = Source.HC F.H F.Vplus →
      (∀ i : Fin s.length, ∀ D : Subgroup (Section (s i.castSucc) (s i.succ)),
        (∀ k : K.subgroupOf F.H, ∀ x, x ∈ D →
          sectionAction (s i.castSucc) (s i.succ) k x ∈ D) → D = ⊥ ∨ D = ⊤) →
      s.restrictedNoncentralCount (K.subgroupOf F.H) = 1 → ∀ i : Fin s.length,
        (¬ ∀ k : K.subgroupOf F.H, ∀ x,
          sectionAction (s i.castSucc) (s i.succ) k x = x) →
          Nat.card (Section (s i.castSucc) (s i.succ)) ≠ 16) : False := by
  let : IsElementaryAbelian 2 (Source.UH F.H F.Vplus) := IsElementaryAbelian.of_le dx.kernel_le
  let : IsElementaryAbelian 2 (c.Ugamma F.Vplus) := IsElementaryAbelian.map _
  have hCQ : Source.HC F.H F.Vplus ≤ Source.QH F.H :=
    d.centralizer_le_of_action_kernel (Source.QH F.H)
      (source_natural_action_kernel F.H (Source.QH F.H) ρ π hker hnatural)
  have hVC : Source.VH F.H F.V ≤ Source.HC F.H F.Vplus := le_inf dx.section_le
    ((commutator_eq_bot_iff_le_centralizer.mp (commutator_self_eq_bot_iff.mpr
      (inferInstance : IsMulCommutative (Source.VH F.H F.V)))).trans (centralizer_le dx.kernel_le))
  obtain ⟨hstar,hintersection,hAV⟩ := source_critical_pair_geometry_of_seed_normalizer
    F hF c hb ρ d π hker honto hnatural ξ dx hexterior hseed hseedcard hcontrol
    houtside hline hbackline
  have hforward : c.Vgamma ≤ F.H := by
    have hh := (SourceCompletion.f9_endpoint_edge_cores F hF c hb).2.trans
      ((pCoreIn_le 2 _).trans inf_le_left)
    rwa [vertexGroup_base] at hh
  have hUγH : c.Ugamma F.Vplus ≤ F.H := (map_mono dx.kernel_le).trans hforward
  have hU : Nat.card (c.Ugamma F.Vplus) = 32 := by
    change Nat.card ((Source.UH F.H F.Vplus).map _) = 32
    rw [card_map_of_injective (MulAut.conj (c.gb:G)).injective,d.card_section,hF.point_card]
    norm_num
  have hCseed : Source.HC F.H F.Vplus ≤ centralizer (F.Vplus:Set G) :=
    inf_le_right.trans (centralizer_le (le_conjugateSpanBy F.Vplus F.H))
  have hHC : F.H ≤ normalizer (Source.HC F.H F.Vplus : Set G) :=
    (le_inf F.H.le_normalizer (d.normalized.trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  let Gγ := normalizer (c.Aone F.V₁ : Set G)
  have hA : Nat.card (c.Aone F.V₁) = 2 :=
    (card_map_of_injective (MulAut.conj (c.gb:G)).injective).trans hF.point_card
  have hGγ : Gγ = centralizer (c.Aone F.V₁ : Set G) :=
    le_antisymm (normalizer_le_centralizer_of_card_two _ hA) (Subgroup.centralizer_le_normalizer _)
  have hGn : Gγ ≤ normalizer (c.Ugamma F.Vplus : Set G) := by
    have he : Gγ = F.H.conjBy (c.gb:G) := by
      exact (map_equiv_normalizer_eq F.V₁ (MulAut.conj (c.gb:G))).symm.trans
        (congrArg (fun B : Subgroup G => B.conjBy (c.gb:G)) hH.symm)
    rw [he]
    exact (map_mono d.normalized).trans ((Source.UH F.H F.Vplus).le_normalizer_map _)
  exact source_linear_four_exclusion F.H Q (Source.QH F.H) (Source.HC F.H F.Vplus) F.Vplus F.V
    (Source.VH F.H F.V) R (c.Aone F.V₁) (c.Ugamma F.Vplus) Gγ K rfl hVC hQR hindex
    hcent hdual hCQ hCseed hHC hQV rfl hAV hGγ hGn hUγH hU hstar hintersection
    hcover e hKH hK hmove hKonto hnotfour

end CFSG.Quasithin.Chapter13.Section08.LinearFour
