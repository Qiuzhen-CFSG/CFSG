module

public import CFSG.Quasithin.ChapterH.Section13To16.M22Local.ElementaryFour.Basic
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.ElementaryFour.QuintetLifts

/-!
# Ordinary lifts in the hexad quotient of the outer M22

For every outer elementary subgroup of order sixteen whose image lies in the
three-transposition cube, the image has order two or more than two. In the
larger case, the sign map produces an inner involution outside the hexad
kernel. Its kernel centralizer has order four, exactly the intersection of
the two kernels; involutory lifts and their commuting subgroups therefore lie
in the quintet kernel. This supplies an actual ambient fusion witness.

For an order-two image, an actual hexad conjugator moves the image to the
marked transposition. The involution in the geometric splitting then lies in
the conjugated subgroup, and its supplement is the order-eight intersection
with the kernel. The earlier five-dimensional hexad action is retained by an
intertwining equivalence. The exceptional S6 marking turns the transposition
into a triple transposition on the deleted permutation module, giving fixed
dimension three. The fixed spaces of dimensions five and seven then span a
space of dimension nine in the ten-dimensional cocode.

The earlier H.14 group and geometric splitting facts, H.14.4 displacement,
and H.15.2 action and noncyclic fixed-space facts remain explicit in
`QuintetKernelData`, `HexadSplitGeometry`, and `OrdinaryModuleInput`. No witness
of these earlier inputs is asserted here. H.15.4 supplies the last module
clauses of the fused alternative. No maximality hypothesis or elementary
subgroup classification is assumed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), H.14.1(4),
H.14.3--4, H.15.2(2),(5), and the ordinary branches of H.15.5, printed p.401
(PDF p.412). The parent assembly retains the exceptional quotient branch
and discharge of the earlier inputs.
-/

@[expose] public section


open Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders
namespace CFSG.Quasithin.ChapterH.Section13To16.M22ElementaryFour.QuintetLifts

private def evenConjugator (j : Fin 8) : Equiv.Perm (Fin 6) :=
  if j = 5 then Equiv.swap 2 4 * Equiv.swap 3 5
  else if j = 6 then Equiv.swap 0 4 * Equiv.swap 1 5 else 1

private theorem even_words (j : Fin 8)
    (hs : Equiv.Perm.sign (Six.dWords j) = 1) (hne : Six.dWords j ≠ 1) :
    Six.dWords j = (MulAut.conj (evenConjugator j)) (kleinFirst 6 (by decide)) := by
  revert j
  decide +kernel

theorem even_cube_fixed_card (s : Equiv.Perm (Fin 6))
    (hs : s ∈ D 6) (heven : s ∈ alternatingGroup (Fin 6)) (hne : s ≠ 1) :
    Nat.card (fixedSpace (naturalRepresentation (Fin 6)) (Subgroup.zpowers s)) = 4 := by
  obtain ⟨j, rfl⟩ := (Six.mem_disjointTranspositions_iff 3 s).mp hs
  change Equiv.Perm.sign (Six.dWords j) = 1 at heven
  have he := even_words j heven hne
  have hz : Subgroup.zpowers (Six.dWords j) =
      Six.double.map (MulAut.conj (evenConjugator j)).toMonoidHom := by
    rw [Six.double, ← Subgroup.zpowers_eq_closure, MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers he
  have hd : Module.finrank (ZMod 2)
      (fixedSpace (naturalRepresentation (Fin 6)) (Subgroup.zpowers (Six.dWords j))) = 2 := by
    rw [hz, ← (fixedSpaceConjEquiv (naturalRepresentation (Fin 6)) Six.double
      (evenConjugator j)).finrank_eq]
    exact Six.finrank_fixedSpace_double.2.2.2
  change Nat.card (fixedSpace (naturalRepresentation (Fin 6)) (Subgroup.zpowers (Six.dWords j))) = 4
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hd]
  norm_num [Nat.card_eq_fintype_card]

theorem exists_even_ne_one (E : Subgroup (Equiv.Perm (Fin 6)))
    (hc : 2 < Nat.card E) : ∃ s ∈ E, s ∈ alternatingGroup (Fin 6) ∧ s ≠ 1 := by
  by_contra! hn
  have hi : Function.Injective (Equiv.Perm.sign.comp E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    apply Subtype.ext
    exact hn s s.property hs
  have hb := Nat.card_le_card_of_injective _ hi
  have hc2 : Nat.card ℤˣ = 2 := by simp [Nat.card_eq_fintype_card]
  rw [hc2] at hb
  omega

end CFSG.Quasithin.ChapterH.Section13To16.M22ElementaryFour.QuintetLifts

open Representation.BinaryOffender BinaryPermutation
open MathieuCode MathieuCode.M22ElementaryFour
open MathieuCode.M22ElementaryFour.QuintetLifts
open CFSG.Quasithin.ChapterB.Offenders
namespace CFSG.Quasithin.ChapterH.Section13To16.M22ElementaryFour.QuintetLifts

/-- The earlier H.14.3 quintet two-core, in the compatible common Sylow arrangement. -/
structure QuintetKernelData : Prop where
  le_hexad : QuintetKernel ≤ Hexad
  elementary : IsElementaryAbelian 2 QuintetKernel
  card : Nat.card QuintetKernel = 32

variable {T : Sylow 2 Ambient} (d : HexadQuotientData T)

theorem kernel_elementary : IsElementaryAbelian 2 d.quotientMap.ker :=
  elementary_kernel_of_coordinates d.quotientMap d.coordinates d.coordinates_mul

theorem quintet_intersection_card (hQ : QuintetKernelData) :
    Nat.card ((QuintetKernel.subgroupOf Hexad) ⊓ d.quotientMap.ker : Subgroup Hexad) = 4 := by
  have h := card_image_mul_card_inf_kernel d.quotientMap (QuintetKernel.subgroupOf Hexad)
  have hcard : Nat.card (QuintetKernel.subgroupOf Hexad) = 32 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ.le_hexad).toEquiv).trans hQ.card
  have hD : Nat.card (D 6) = 8 := Six.card_disjointTranspositions 3
  rw [d.quintet_image, hcard, hD] at h
  omega

theorem even_lift_kernelCentralizer_le (hQ : QuintetKernelData) (x : Hexad)
    (hx : x ∈ QuintetKernel.subgroupOf Hexad)
    (heven : d.quotientMap x ∈ alternatingGroup (Fin 6)) (hne : d.quotientMap x ≠ 1) :
    kernelCentralizer d.quotientMap x ≤ QuintetKernel.subgroupOf Hexad := by
  let := hQ.elementary
  let := IsElementaryAbelian.subgroupOf (p := 2) hQ.le_hexad
  apply kernelCentralizer_le_of_card d.quotientMap _ hx
  have hd : d.quotientMap x ∈ D 6 := d.quintet_image ▸ Subgroup.mem_map_of_mem d.quotientMap hx
  have hb := kernelCentralizer_card_le d.quotientMap
    (naturalRepresentation (Fin 6)) d.coordinates d.commuting_coordinates x
  rw [even_cube_fixed_card _ hd heven hne] at hb
  simpa only [quintet_intersection_card d hQ] using hb

theorem inner_involution_placement (hQ : QuintetKernelData) (a : Hexad)
    (ha : a ^ 2 = 1) (hcube : d.quotientMap a ∈ D 6)
    (heven : d.quotientMap a ∈ alternatingGroup (Fin 6)) (hne : d.quotientMap a ≠ 1) :
    a ∈ QuintetKernel.subgroupOf Hexad := by
  let := kernel_elementary d
  let := hQ.elementary
  let := IsElementaryAbelian.subgroupOf (p := 2) hQ.le_hexad
  obtain ⟨x, hx, hxa⟩ := (d.quintet_image.symm ▸ hcube)
  apply involution_mem_of_same_image d.quotientMap _ ha hx hxa.symm
  apply even_lift_kernelCentralizer_le d hQ x hx
  · rwa [hxa]
  · rwa [hxa]

theorem even_quintet_centralizer (hQ : QuintetKernelData) (a : Hexad)
    (ha : a ∈ QuintetKernel.subgroupOf Hexad)
    (heven : d.quotientMap a ∈ alternatingGroup (Fin 6)) (hne : d.quotientMap a ≠ 1) :
    ((QuintetKernel.subgroupOf Hexad).map d.quotientMap).comap d.quotientMap ⊓
      Subgroup.centralizer ({a} : Set Hexad) ≤ QuintetKernel.subgroupOf Hexad := by
  let := hQ.elementary
  let := IsElementaryAbelian.subgroupOf (p := 2) hQ.le_hexad
  exact centralizer_in_preimage_le d.quotientMap _ ha
    (even_lift_kernelCentralizer_le d hQ a ha heven hne)

/-- Inside the product of the two kernels, the full centralizer is the
quintet kernel. The product is expressed as a join inside the hexad stabilizer,
where the hexad kernel is normal. -/
theorem even_quintet_product_centralizer_eq (hQ : QuintetKernelData) (a : Hexad)
    (ha : a ∈ QuintetKernel.subgroupOf Hexad)
    (heven : d.quotientMap a ∈ alternatingGroup (Fin 6)) (hne : d.quotientMap a ≠ 1) :
    ((QuintetKernel.subgroupOf Hexad) ⊔ d.quotientMap.ker) ⊓
      Subgroup.centralizer ({a} : Set Hexad) = QuintetKernel.subgroupOf Hexad := by
  let := hQ.elementary
  let := IsElementaryAbelian.subgroupOf (p := 2) hQ.le_hexad
  have hle := even_quintet_centralizer d hQ a ha heven hne
  rw [Subgroup.comap_map_eq] at hle
  apply le_antisymm hle
  intro b hb
  exact ⟨(le_sup_left : QuintetKernel.subgroupOf Hexad ≤
    QuintetKernel.subgroupOf Hexad ⊔ d.quotientMap.ker) hb,
    Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_of_mem_elementary (QuintetKernel.subgroupOf Hexad) hb ha).eq⟩

/-- The sign map constructs an inner involution outside the hexad kernel
whenever the image has more than two elements. -/
theorem large_image_inner_involution (A : Subgroup Ambient) (hAH : A ≤ Hexad)
    (hA : IsElementaryAbelian 2 A)
    (hlarge : 2 < Nat.card ((A.subgroupOf Hexad).map d.quotientMap)) :
    ∃ a : Hexad, a ∈ A.subgroupOf Hexad ∧ a.val ∈ MathieuCode.M22ElementaryFour.Inner ∧
      a.val ∉ HexadKernel ∧ a ^ 2 = 1 ∧ orderOf a.val = 2 := by
  let := hA
  let := IsElementaryAbelian.subgroupOf (p := 2) hAH
  obtain ⟨s, hs, heven, hs1⟩ := exists_even_ne_one _ hlarge
  obtain ⟨a, ha, rfl⟩ := hs
  have hi : a.val ∈ MathieuCode.M22ElementaryFour.Inner := by
    change a ∈ MathieuCode.M22ElementaryFour.Inner.subgroupOf Hexad
    rw [← d.inner_preimage]
    exact heven
  have hk : a.val ∉ HexadKernel := by
    intro haK
    have hh : a ∈ d.quotientMap.ker := by
      rw [d.kernel_eq]
      exact haK
    exact hs1 hh
  have hsq : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  refine ⟨a, ha, hi, hk, hsq, orderOf_eq_prime (congrArg Subtype.val hsq) ?_⟩
  intro h1
  exact hk (h1 ▸ HexadKernel.one_mem)

theorem large_image_le_quintet (hQ : QuintetKernelData)
    (A : Subgroup Ambient) (hAH : A ≤ Hexad) (hA : IsElementaryAbelian 2 A)
    (hcube : (A.subgroupOf Hexad).map d.quotientMap ≤ D 6)
    (hlarge : 2 < Nat.card ((A.subgroupOf Hexad).map d.quotientMap)) :
    A ≤ QuintetKernel := by
  let := hA
  let := IsElementaryAbelian.subgroupOf (p := 2) hAH
  obtain ⟨a, ha, hainner, hakernel, hasq, _⟩ := large_image_inner_involution d A hAH hA hlarge
  have heven : d.quotientMap a ∈ alternatingGroup (Fin 6) := by
    change a ∈ (alternatingGroup (Fin 6)).comap d.quotientMap
    rw [d.inner_preimage]
    exact hainner
  have hs1 : d.quotientMap a ≠ 1 := by
    intro he
    have hk : a ∈ d.quotientMap.ker := he
    rw [d.kernel_eq] at hk
    exact hakernel hk
  have haQ := inner_involution_placement d hQ a hasq
    (hcube (Subgroup.mem_map_of_mem _ ha)) heven hs1
  have hcentral := (even_quintet_product_centralizer_eq d hQ a haQ heven hs1).le
  rw [← Subgroup.comap_map_eq] at hcentral
  intro b hb
  apply hcentral (x := (⟨b, hAH hb⟩ : Hexad))
  refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  · change d.quotientMap ⟨b, hAH hb⟩ ∈ (QuintetKernel.subgroupOf Hexad).map d.quotientMap
    rw [d.quintet_image]
    exact hcube (Subgroup.mem_map_of_mem _ hb)
  · exact (commute_of_mem_elementary (A.subgroupOf Hexad) hb ha).eq

theorem large_image_fused (hQ : QuintetKernelData)
    (A : Subgroup Ambient) (hAT : A ≤ (T : Subgroup Ambient)) (hA : IsElementaryAbelian 2 A)
    (hcube : (A.subgroupOf Hexad).map d.quotientMap ≤ D 6)
    (hlarge : 2 < Nat.card ((A.subgroupOf Hexad).map d.quotientMap)) :
    FusedIntoQuintet A := by
  refine ⟨1, ?_⟩
  change A.map (MonoidHom.id Ambient) ≤ QuintetKernel
  simpa using large_image_le_quintet d hQ A (hAT.trans d.compatible.le_hexad) hA hcube hlarge

theorem image_size_split (A : Subgroup Ambient) (hAT : A ≤ (T : Subgroup Ambient))
    (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16)
    (houter : ¬ A ≤ MathieuCode.M22ElementaryFour.Inner) :
    Nat.card ((A.subgroupOf Hexad).map d.quotientMap) = 2 ∨
      2 < Nat.card ((A.subgroupOf Hexad).map d.quotientMap) := by
  have hn := (d.image_offender A hAT hA hcard houter).1.1
  have hp := Nat.card_pos (α := ((A.subgroupOf Hexad).map d.quotientMap))
  have h1 : Nat.card ((A.subgroupOf Hexad).map d.quotientMap) ≠ 1 :=
    fun h => hn (Subgroup.card_eq_one.mp h)
  omega

end CFSG.Quasithin.ChapterH.Section13To16.M22ElementaryFour.QuintetLifts

open Representation.BinaryOffender BinaryPermutation
open MathieuCode MathieuCode.M22ElementaryFour
open MathieuCode.M22ElementaryFour.QuintetLifts
open CFSG.Quasithin.ChapterB.Offenders
namespace CFSG.Quasithin.ChapterH.Section13To16.M22ElementaryFour.QuintetLifts

noncomputable abbrev hexadCocodeRepresentation := m22OuterCocodeRepresentation.comp Hexad.subtype

/-- The split hexad extension comes from the point stabilizer in the affine
sixteen-point action of the octad stabilizer (H.14.1(4), H.14.3(3)). The last
field is precisely the non-fixed-point-free outer class of H.14.4(4). -/
structure HexadSplitGeometry {T : Sylow 2 Ambient} (d : HexadQuotientData T) where
  sectionMap : (Equiv.Perm (Fin 6)) →* Hexad
  section_right_inverse : ∀ s, d.quotientMap (sectionMap s) = s
  point : Fin 24
  section_fixes : ∀ s, (sectionMap s).val.val • point = point
  outer_fixed_octad : ∀ j : Ambient, j ^ 2 = 1 → j ∉ MathieuCode.M22ElementaryFour.Inner →
    (∃ p : Fin 24, j.val • p = p) → FixesDisjointOctad j

/-- Earlier H.14 geometry and H.15.2 action data, with the two S6 markings
explicitly related. None of these fields classifies an elementary subgroup. -/
structure OrdinaryModuleInput {T : Sylow 2 Ambient} (d : HexadQuotientData T)
    extends HexadSplitGeometry d where
  twist : (Equiv.Perm (Fin 6)) ≃* Equiv.Perm (Fin 6)
  twist_transposition : twist (pairSwap 6 0) = kleinFirst 6 (by decide) * pairSwap 6 2
  coordinates : fixedSpace hexadCocodeRepresentation d.quotientMap.ker ≃ₗ[ZMod 2]
    Deleted (Fin 6)
  intertwining : ∀ (g : Hexad) (v : Deleted (Fin 6)),
    hexadCocodeRepresentation g (coordinates.symm v : M22Cocode) =
      (coordinates.symm (deletedRepresentation (Fin 6) (twist (d.quotientMap g)) v) : M22Cocode)
  noncyclic_fixed : ∀ B : Subgroup Hexad, B ≤ d.quotientMap.ker → ¬ IsCyclic B →
    fixedSpace hexadCocodeRepresentation B = fixedSpace hexadCocodeRepresentation d.quotientMap.ker
  outer_displacement : ∀ j : Hexad, j ^ 2 = 1 → j.val ∉ MathieuCode.M22ElementaryFour.Inner →
    FixesDisjointOctad j.val → fixedCodim hexadCocodeRepresentation (Subgroup.zpowers j) = 3

/-- Choose the transposition in the geometric splitting; its point fixation
will distinguish the outer involution class. -/
noncomputable def OrdinaryModuleInput.involution {T : Sylow 2 Ambient}
    {d : HexadQuotientData T} (h : OrdinaryModuleInput d) : Hexad :=
  h.sectionMap (pairSwap 6 0)

theorem OrdinaryModuleInput.involution_image {T : Sylow 2 Ambient}
    {d : HexadQuotientData T} (h : OrdinaryModuleInput d) :
    d.quotientMap h.involution = pairSwap 6 0 := h.section_right_inverse _

theorem OrdinaryModuleInput.involution_square {T : Sylow 2 Ambient}
    {d : HexadQuotientData T} (h : OrdinaryModuleInput d) : h.involution ^ 2 = 1 := by
  change h.sectionMap (pairSwap 6 0) ^ 2 = 1
  rw [← map_pow, show (pairSwap 6 0) ^ 2 = 1 by decide +kernel, map_one]

theorem OrdinaryModuleInput.involution_outer {T : Sylow 2 Ambient}
    {d : HexadQuotientData T} (h : OrdinaryModuleInput d) :
    h.involution.val ∉ MathieuCode.M22ElementaryFour.Inner := by
  intro hi
  have hs : d.quotientMap h.involution ∈ alternatingGroup (Fin 6) := by
    change h.involution ∈ (alternatingGroup (Fin 6)).comap d.quotientMap
    rw [d.inner_preimage]
    exact hi
  rw [h.involution_image] at hs
  have hsign : Equiv.Perm.sign (pairSwap 6 0) = 1 := hs
  exact (by decide +kernel : Equiv.Perm.sign (pairSwap 6 0) ≠ 1) hsign

theorem OrdinaryModuleInput.involution_octad {T : Sylow 2 Ambient}
    {d : HexadQuotientData T} (h : OrdinaryModuleInput d) : FixesDisjointOctad h.involution.val :=
  h.outer_fixed_octad h.involution.val (congrArg Subtype.val h.involution_square)
    h.involution_outer ⟨h.point, h.section_fixes _⟩

theorem offender_card_two_conjugate (E : Subgroup (Equiv.Perm (Fin 6)))
    (hE : IsOffender (naturalRepresentation (Fin 6)) E) (hcard : Nat.card E = 2) :
    ∃ s, E.map (MulAut.conj s).toMonoidHom = disjointTranspositions 6 1 := by
  have hr : rank E = 1 := by norm_num [rank, hcard, Nat.log_eq_iff]
  rcases (Six.caseBFamily_iff E).mp ((Six.isOffender_natural_iff E).mp hE) with
    h | h | h | h | h | h
  · obtain ⟨s, hs⟩ := h.symm
    exact ⟨s, hs.symm⟩
  · have hh := h.rank_eq; rw [hr, Six.rank_A2] at hh; contradiction
  · have hh := h.rank_eq; rw [hr, Six.rank_D] at hh; contradiction
  · have hh := h.rank_eq; rw [hr, Six.rank_exceptional] at hh; contradiction
  · have hh := h.rank_eq; rw [hr, Six.rank_evenPart] at hh; contradiction
  · have hh := h.rank_eq; rw [hr, Six.rank_plus] at hh; contradiction

variable {T : Sylow 2 Ambient} (d : HexadQuotientData T)

theorem marked_involution_kernelCentralizer_card_le (h : OrdinaryModuleInput d) :
    Nat.card (kernelCentralizer d.quotientMap h.involution) ≤ 8 := by
  have hb := kernelCentralizer_card_le d.quotientMap (naturalRepresentation (Fin 6))
    d.coordinates d.commuting_coordinates h.involution
  have hline : Subgroup.zpowers (pairSwap 6 0) = disjointTranspositions 6 1 := by
    rw [Subgroup.zpowers_eq_closure]
    apply congrArg Subgroup.closure
    ext g
    simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro rfl; exact ⟨0, by decide, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      have hj0 : j = (0 : Fin (6 / 2)) := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj))
      rw [hj0]
  rw [h.involution_image, hline, Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace (naturalRepresentation (Fin 6)) (disjointTranspositions 6 1)),
    Six.finrank_fixedSpace_A1.2.2.2] at hb
  norm_num [Nat.card_eq_fintype_card] at hb ⊢
  exact hb

theorem marked_restricted_fixed_finrank (h : OrdinaryModuleInput d) :
    Module.finrank (ZMod 2)
      ↥(fixedSpace hexadCocodeRepresentation d.quotientMap.ker ⊓
        fixedSpace hexadCocodeRepresentation (Subgroup.zpowers h.involution)) = 3 := by
  have he := (restrictedFixedEquiv hexadCocodeRepresentation (deletedRepresentation (Fin 6))
    _ h.involution (h.twist (d.quotientMap h.involution)) h.coordinates
    (h.intertwining h.involution)).finrank_eq
  rw [h.involution_image, h.twist_transposition] at he
  have hz : Subgroup.zpowers (kleinFirst 6 (by decide) * pairSwap 6 2) = Six.triple := by
    rw [Subgroup.zpowers_eq_closure]
    rfl
  rw [hz] at he
  exact he.trans Six.finrank_fixedSpace_triple.2.1

theorem standard_line_module_case (h : OrdinaryModuleInput d)
    (B : Subgroup Hexad) (hB : IsElementaryAbelian 2 B) (hcard : Nat.card B = 16)
    (himage : B.map d.quotientMap = disjointTranspositions 6 1) :
    Module.finrank (ZMod 2) (fixedSpace hexadCocodeRepresentation B) = 3 ∧
      Module.finrank (ZMod 2) (M22Cocode ⧸ fixedSpaceSpan hexadCocodeRepresentation B) ≤ 1 := by
  let := hB
  let := kernel_elementary d
  have hcimage : Nat.card (B.map d.quotientMap) = 2 := by
    rw [himage]
    exact Six.card_disjointTranspositions 1
  have hiimage : d.quotientMap h.involution ∈ B.map d.quotientMap := by
    rw [h.involution_image, himage]
    exact pairSwap_mem 0 (by decide)
  have hi1 : d.quotientMap h.involution ≠ 1 := by
    rw [h.involution_image]
    decide +kernel
  obtain ⟨_, hsplit⟩ := supplement_at_involution d.quotientMap B hcard hcimage
    h.involution h.involution_square hiimage hi1 (marked_involution_kernelCentralizer_card_le d h)
  have hb8 := card_intersection_of_card_image_two d.quotientMap B hcard hcimage
  have hbne : B ⊓ d.quotientMap.ker ≠ ⊥ := by
    intro hb
    have hc1 := Subgroup.card_eq_one.mpr hb
    omega
  have hnc : ¬ IsCyclic (B ⊓ d.quotientMap.ker : Subgroup Hexad) := by
    intro hc
    let := hc
    have hp : Monoid.exponent (B ⊓ d.quotientMap.ker : Subgroup Hexad) ∣ 2 := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro b
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian b.val b.property.2
    rw [IsCyclic.exponent_eq_card, hb8] at hp
    norm_num at hp
  have hd := h.outer_displacement h.involution h.involution_square h.involution_outer h.involution_octad
  have hdi := fixedCodim_add_finrank hexadCocodeRepresentation (Subgroup.zpowers h.involution)
  have hU : Module.finrank (ZMod 2)
      (fixedSpace hexadCocodeRepresentation d.quotientMap.ker) = 5 := by
    rw [h.coordinates.finrank_eq, finrank_deleted]
    rfl
  apply rank_three_module_case hexadCocodeRepresentation B _ h.involution hsplit hbne
    (fun he => hi1 (he ▸ map_one d.quotientMap)) _
    (h.noncyclic_fixed _ inf_le_right hnc) finrank_m22Cocode hU
  · rw [hd, finrank_m22Cocode] at hdi
    omega
  · exact marked_restricted_fixed_finrank d h

/-- Surjectivity lifts the quotient conjugator to the actual hexad stabilizer. -/
theorem conjugate_to_transposition_image (A : Subgroup Ambient)
    (hAT : A ≤ (T : Subgroup Ambient)) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card A = 16) (houter : ¬ A ≤ MathieuCode.M22ElementaryFour.Inner)
    (himage : Nat.card ((A.subgroupOf Hexad).map d.quotientMap) = 2) :
    ∃ g : Hexad, ((A.subgroupOf Hexad).map (MulAut.conj g).toMonoidHom).map d.quotientMap =
      disjointTranspositions 6 1 := by
  obtain ⟨s, hs⟩ := offender_card_two_conjugate _ (d.image_offender A hAT hA hcard houter) himage
  obtain ⟨g, rfl⟩ := d.surjective s
  exact ⟨g, by rwa [map_conj_image]⟩

/-- The ordinary order-two case, transported from its constructed supplement
back to the literal ambient subgroup and cocode. -/
theorem image_card_two_case (h : OrdinaryModuleInput d) (A : Subgroup Ambient)
    (hAT : A ≤ (T : Subgroup Ambient)) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card A = 16) (houter : ¬ A ≤ MathieuCode.M22ElementaryFour.Inner)
    (himage : Nat.card ((A.subgroupOf Hexad).map d.quotientMap) = 2) :
    Nat.card (A ⊓ HexadKernel : Subgroup Ambient) = 8 ∧
    Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation A) = 3 ∧
    Module.finrank (ZMod 2) (M22Cocode ⧸ fixedSpaceSpan m22OuterCocodeRepresentation A) ≤ 1 := by
  have hAH := hAT.trans d.compatible.le_hexad
  let := hA
  let := IsElementaryAbelian.subgroupOf (p := 2) hAH
  obtain ⟨g, hg⟩ := conjugate_to_transposition_image d A hAT hA hcard houter himage
  let B := (A.subgroupOf Hexad).map (MulAut.conj g).toMonoidHom
  have hcAH : Nat.card (A.subgroupOf Hexad) = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv).trans hcard
  have hcB : Nat.card B = 16 :=
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).trans hcAH
  obtain ⟨hfix, hspan⟩ := standard_line_module_case d h B (IsElementaryAbelian.map _) hcB hg
  have hefix : fixedSpace hexadCocodeRepresentation (A.subgroupOf Hexad) =
      fixedSpace m22OuterCocodeRepresentation A := by
    change fixedSpace (m22OuterCocodeRepresentation.comp Hexad.subtype) _ = _
    rw [fixedSpace_comp_map, Subgroup.map_subgroupOf_eq_of_le hAH]
  have hf := (fixedSpaceConjEquiv hexadCocodeRepresentation (A.subgroupOf Hexad) g).finrank_eq
  rw [hefix] at hf
  have hs := fixedSpaceSpan_codim_conj hexadCocodeRepresentation (A.subgroupOf Hexad) g
  have ht := fixedSpaceSpan_codim_map_equivariant hexadCocodeRepresentation
    m22OuterCocodeRepresentation Hexad.subtype Hexad.subtype_injective
    (LinearEquiv.refl (ZMod 2) M22Cocode) (fun _ _ => rfl) (A.subgroupOf Hexad)
  rw [Subgroup.map_subgroupOf_eq_of_le hAH] at ht
  exact ⟨d.intersection_card_of_image_card_two A hAT hcard himage,
    hf.trans hfix, ht.symm.trans_le (hs.trans_le hspan)⟩

/-- The ordinary quotient-image branch covers every elementary subgroup of
order sixteen; no maximality assumption occurs. Earlier H.14 and H.15.2
inputs remain explicit for the chapter assembly owner. -/
theorem ordinary_cases (hQ : QuintetKernelData) (h : OrdinaryModuleInput d)
    (A : Subgroup Ambient) (hAT : A ≤ (T : Subgroup Ambient))
    (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16)
    (houter : ¬ A ≤ MathieuCode.M22ElementaryFour.Inner)
    (hcube : (A.subgroupOf Hexad).map d.quotientMap ≤ D 6) :
    (Nat.card (A ⊓ HexadKernel : Subgroup Ambient) = 8 ∧
      Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation A) = 3 ∧
      Module.finrank (ZMod 2) (M22Cocode ⧸ fixedSpaceSpan m22OuterCocodeRepresentation A) ≤ 1) ∨
    FusedIntoQuintet A := by
  rcases image_size_split d A hAT hA hcard houter with htwo | hlarge
  · exact Or.inl (image_card_two_case d h A hAT hA hcard houter htwo)
  · exact Or.inr (large_image_fused d hQ A hAT hA hcube hlarge)

/-- H.15.4 supplies the remaining module clauses in the fused alternative. -/
theorem ordinary_four_alternatives (hQ : QuintetKernelData) (h : OrdinaryModuleInput d)
    (hQmodule : ∀ B : Subgroup Ambient, B ≤ QuintetKernel → Nat.card B = 16 →
      Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation B) = 2 ∧
      fixedSpaceSpan m22OuterCocodeRepresentation B = ⊤)
    (A : Subgroup Ambient) (hAT : A ≤ (T : Subgroup Ambient))
    (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16)
    (houter : ¬ A ≤ MathieuCode.M22ElementaryFour.Inner)
    (hcube : (A.subgroupOf Hexad).map d.quotientMap ≤ D 6) : FourAlternatives A := by
  rcases ordinary_cases d hQ h A hAT hA hcard houter hcube with hfour | hfused
  · exact Or.inr (Or.inr (Or.inr hfour))
  · exact Or.inr (Or.inl ⟨hfused, quintet_module_case hQmodule A hcard hfused⟩)

end CFSG.Quasithin.ChapterH.Section13To16.M22ElementaryFour.QuintetLifts