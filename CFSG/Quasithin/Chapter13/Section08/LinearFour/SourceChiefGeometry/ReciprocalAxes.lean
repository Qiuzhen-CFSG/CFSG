module
public import Theory.Representation.BinaryConjugationSection.CentralizerKernel
public import Theory.GroupTheory.InvolutionCentralizerControl
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.HyperplaneExclusion
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Cosets

/-!
# Reciprocal axes from the actual critical pair

The natural action on U_H/V₁ identifies the centralizer kernel on each
critical subgroup. Mutual endpoint placement makes the groups normalize
one another, so a nontrivial image also forces a nontrivial intersection.
The exterior action then gives the index two at either end. Disjointness
from the central line identifies Uγ ∩ Q_H with C_{Uγ}(U_H); its conjugate
by the inverse of the same source transporter is the required natural
hyperplane. The seed centralizer bound makes Vγ centralize that axis.

Thus the existing parabolic calculation constructs the reciprocal
hyperplane in V_H and proves all three conclusions of 13.8.32 from the
marked actions and the earlier endpoint, line and parabolic premises.
The actual CriticalPair application obtains inverse endpoint placement
from the vertex stabilizer. Its terminal consumer also derives containment
and normality of H_C, abelianness consequences, the order of Uγ and the
normalizer of the critical group, using their literal source definitions.

The initial natural/exterior markings, excluded lines, strict image
inclusion, plane-radical placement and the 13.8.31 chief obstruction remain
explicit obligations of qt-d-138-linear-four-source. The earlier 13.8.27
setup belongs to qt-d-138-six-g2-source, and final 13.8.1 assembly to
qt-d-1381-source. These results do not complete Theorem 13.8.28.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
13.8.32 and the terminal argument, printed pp.965–966. The chosen critical
conjugator and both quotient maps are preserved throughout.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups
open Atlas.Order20160A8.Bivectors (exteriorMap)
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open BinaryParabolicExteriorSquare
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The original natural matrix marking has exactly the specified kernel. -/
theorem source_natural_action_kernel
    (H QH : Subgroup G) (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w) (h : H) :
    (∀ w, ρ h w = w) ↔ (h:G) ∈ QH := by
  have hk : (h:G) ∈ QH ↔ π h = 1 := by
    change h ∈ QH.subgroupOf H ↔ _
    rw [←hker]
    rfl
  rw [hk]
  constructor
  · intro hh
    apply Subtype.ext
    apply Matrix.mulVec_injective
    funext w
    rw [←hnatural,hh]
    exact (Matrix.one_mulVec w).symm
  · intro hh w
    rw [hnatural,hh]
    exact Matrix.one_mulVec w

private theorem source_line_disjoint (Z A : Subgroup G)
    (hZ : Nat.card Z = 2) (houtside : ¬ Z ≤ A) : A ⊓ Z = ⊥ := by
  have hd : Nat.card (A ⊓ Z : Subgroup G) ∣ 2 :=
    hZ ▸ card_dvd_of_le (inf_le_right : A ⊓ Z ≤ Z)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hc | hc
  · exact card_eq_one.mp hc
  · have he : A ⊓ Z = Z := eq_of_le_of_card_ge inf_le_right (by rw [hc,hZ])
    exact False.elim (houtside (he ▸ inf_le_left))

omit [Finite G] in
private theorem source_conjugate_normalizes
    (H U B : Subgroup G) (hHU : H ≤ normalizer (U:Set G))
    (y : G) (hback : B.conjBy y⁻¹ ≤ H) : B ≤ normalizer (U.conjBy y : Set G) := by
  have hh := (map_mono (f := (MulAut.conj y).toMonoidHom) (hback.trans hHU)).trans
    (U.le_normalizer_map (MulAut.conj y).toMonoidHom)
  change (B.conjBy y⁻¹).conjBy y ≤ _ at hh
  rwa [conjBy_inv'] at hh

omit [Finite G] in
private theorem source_conjugate_centralizes
    (U A : Subgroup G) (y : G)
    (hc : A ≤ centralizer (U:Set G)) :
    A.conjBy y ≤ centralizer (U.conjBy y : Set G) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  have hh := congrArg (fun B : Subgroup G => B.map (MulAut.conj y).toMonoidHom)
    (commutator_eq_bot_iff_le_centralizer.mpr hc)
  change ⁅A.map _,U.map _⁆ = ⊥
  simpa only [map_commutator,Subgroup.map_bot] using hh

/-- Mutual endpoint placement supplies normalization, the commutator containment
and nontrivial intersection required by the orthogonal index argument. -/
theorem source_critical_indices_of_mutual_markings
    (H UH V1 QH VH : Subgroup G) [IsElementaryAbelian 2 UH]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (ξ : Representation (ZMod 2) H (Fin 6 → ZMod 2))
    (dx : BinaryConjugationSection H VH UH ξ)
    (hexterior : ∀ h w, ξ h w = exteriorMap (π h).val w)
    (hV1 : Nat.card V1 = 2) (hVQ : VH ≤ QH)
    (y : G) (hforward : UH.conjBy y ≤ H) (hback : VH.conjBy y⁻¹ ≤ H)
    (houtside : ¬ UH.conjBy y ≤ QH) :
    QH.relIndex (UH.conjBy y) = 2 ∧
      8 ≤ Nat.card (UH.conjBy y ⊓ VH : Subgroup G) := by
  let : IsElementaryAbelian 2 (UH.conjBy y) := IsElementaryAbelian.map _
  have hn : VH ≤ normalizer (UH.conjBy y : Set G) :=
    source_conjugate_normalizes H UH VH d.normalized y hback
  have hm : UH.conjBy y ⊓ UH ≠ ⊥ := d.inf_ne_bot_of_action_kernel QH (UH.conjBy y)
    (source_natural_action_kernel H QH ρ π hker hnatural) hforward (dx.kernel_le.trans hn) houtside
  have hc : ⁅UH.conjBy y,VH⁆ ≤ UH.conjBy y ⊓ VH := le_inf
    (le_normalizer_iff_commutator_le_left.mp hn)
    (le_normalizer_iff_commutator_le_right.mp (hforward.trans dx.normalized))
  have hU : Nat.card (UH.conjBy y) = 32 := by
    change Nat.card (UH.map _) = 32
    rw [card_map_of_injective (MulAut.conj y).injective,d.card_section,hV1]
    norm_num
  exact source_critical_indices_of_exterior_action H VH UH QH (UH.conjBy y)
    ξ π hker hexterior dx hforward houtside hc hVQ hU hm

/-- The inverse critical image cannot vanish: disjointness from V₁ would
force actual centralization, contradicting the forward natural action. -/
theorem source_inverse_critical_image_nontrivial
    (H UH V1 QH : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hV1 : Nat.card V1 = 2) (y : G)
    (hforward : UH.conjBy y ≤ H) (hback : UH.conjBy y⁻¹ ≤ H)
    (houtside : ¬ UH.conjBy y ≤ QH) (hline : ¬ V1.conjBy y ≤ UH) :
    ¬ UH.conjBy y⁻¹ ≤ QH := by
  have hline' : ¬ V1 ≤ UH.conjBy y⁻¹ := by
    intro hh
    have hm := map_mono (f := (MulAut.conj y).toMonoidHom) hh
    change V1.conjBy y ≤ (UH.conjBy y⁻¹).conjBy y at hm
    rw [conjBy_inv'] at hm
    exact hline hm
  have hn : UH ≤ normalizer (UH.conjBy y⁻¹ : Set G) :=
    source_conjugate_normalizes H UH UH d.normalized y⁻¹ (by simpa using hforward)
  have he := d.inf_centralizer_eq_inf_action_kernel QH (UH.conjBy y⁻¹)
    (source_natural_action_kernel H QH ρ π hker hnatural) hback hn
    (source_line_disjoint V1 (UH.conjBy y⁻¹) hV1 hline')
  intro hh
  have hc : UH.conjBy y⁻¹ ≤ centralizer (UH:Set G) := by
    have hx : UH.conjBy y⁻¹ ≤ UH.conjBy y⁻¹ ⊓ centralizer (UH:Set G) := by
      rw [he,inf_eq_left.mpr hh]
    exact hx.trans inf_le_right
  have hc' := source_conjugate_centralizes UH (UH.conjBy y⁻¹) y hc
  rw [conjBy_inv'] at hc'
  exact houtside ((le_inf hforward (le_centralizer_iff.mp hc')).trans
    (d.centralizer_le_of_action_kernel QH (source_natural_action_kernel H QH ρ π hker hnatural)))

/-- Conjugating the actual forward kernel constructs the reciprocal natural
axis, including its index two, central line and centralization property. -/
theorem source_reciprocal_natural_axis
    (H UH V1 QH : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hV1 : Nat.card V1 = 2) (hcentral : H ≤ centralizer (V1:Set G))
    (y : G) (hforward : UH.conjBy y ≤ H) (hback : UH.conjBy y⁻¹ ≤ H)
    (hline : ¬ V1 ≤ UH.conjBy y) (hindex : QH.relIndex (UH.conjBy y) = 2) :
    let D := (UH.conjBy y ⊓ QH).conjBy y⁻¹
    V1 ≤ D ∧ D ≤ UH ∧ D.relIndex UH = 2 ∧
      D ≤ centralizer (UH.conjBy y⁻¹ : Set G) := by
  let D := (UH.conjBy y ⊓ QH).conjBy y⁻¹
  have hk := d.inf_centralizer_eq_inf_action_kernel QH (UH.conjBy y)
    (source_natural_action_kernel H QH ρ π hker hnatural) hforward
    (source_conjugate_normalizes H UH UH d.normalized y hback)
    (source_line_disjoint V1 (UH.conjBy y) hV1 hline)
  have hD : D ≤ UH := by
    have hm := map_mono (f := (MulAut.conj y⁻¹).toMonoidHom)
      (inf_le_left : UH.conjBy y ⊓ QH ≤ UH.conjBy y)
    change D ≤ (UH.conjBy y).conjBy y⁻¹ at hm
    rwa [conjBy_inv] at hm
  have haxis : D ≤ centralizer (UH.conjBy y⁻¹ : Set G) := by
    have hc : UH.conjBy y ⊓ QH ≤ centralizer (UH:Set G) := by rw [←hk]; exact inf_le_right
    exact source_conjugate_centralizes UH _ y⁻¹ hc
  have hZ : V1.conjBy y ≤ UH.conjBy y ⊓ QH := by
    have hc : V1 ≤ centralizer (UH.conjBy y⁻¹:Set G) :=
      le_centralizer_iff.mp (hback.trans hcentral)
    have hm := source_conjugate_centralizes (UH.conjBy y⁻¹) V1 y hc
    rw [conjBy_inv'] at hm
    rw [←hk]
    exact le_inf (map_mono d.kernel_le) hm
  have hV1D : V1 ≤ D := by
    have hm := map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hZ
    change (V1.conjBy y).conjBy y⁻¹ ≤ D at hm
    rwa [conjBy_inv] at hm
  have hi := relIndex_map_map_of_injective (f := (MulAut.conj y⁻¹).toMonoidHom)
    (UH.conjBy y ⊓ QH) (UH.conjBy y) (MulAut.conj y⁻¹).injective
  change D.relIndex ((UH.conjBy y).conjBy y⁻¹) = _ at hi
  rw [conjBy_inv,inf_relIndex_left,hindex] at hi
  exact ⟨hV1D,hD,hi,haxis⟩

/-- The natural and exterior markings construct both critical indices and
the reciprocal axis, then place the critical line in V_H. -/
theorem source_critical_geometry_of_mutual_markings
    (H UH V1 V3 V QH VH : Subgroup G) [IsElementaryAbelian 2 UH]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (ξ : Representation (ZMod 2) H (Fin 6 → ZMod 2))
    (dx : BinaryConjugationSection H VH UH ξ)
    (hexterior : ∀ h w, ξ h w = exteriorMap (π h).val w)
    (hV1 : Nat.card V1 = 2) (hVQ : VH ≤ QH)
    (hspanU : UH = conjugateSpanBy V3 H) (hspanV : VH = conjugateSpanBy V H)
    (hseed : ⁅centralizer (V3:Set G),V⁆ ≤ V1)
    (y : G) (hforward : VH.conjBy y ≤ H) (hback : VH.conjBy y⁻¹ ≤ H)
    (houtside : ¬ UH.conjBy y ≤ QH)
    (hline : ¬ V1.conjBy y ≤ UH) (hbackline : ¬ V1 ≤ UH.conjBy y)
    (hstrict : ((UH.conjBy y⁻¹).subgroupOf H).map π <
      ((VH.conjBy y⁻¹).subgroupOf H).map π)
    (g : SL(4,ZMod 2))
    (hradical : ((VH.conjBy y⁻¹).subgroupOf H).map π ≤ PlaneRadical.radical.conjBy g)
    (hcommE : ⁅UH.conjBy y,VH ⊓ QH.conjBy y⁆ ≤ V1.conjBy y) :
    QH.relIndex (UH.conjBy y) = 2 ∧
      8 ≤ Nat.card (UH.conjBy y ⊓ VH : Subgroup G) ∧ V1.conjBy y ≤ VH := by
  let : IsElementaryAbelian 2 (UH.conjBy y) := IsElementaryAbelian.map _
  have hf : UH.conjBy y ≤ H := (map_mono dx.kernel_le).trans hforward
  have hb : UH.conjBy y⁻¹ ≤ H := (map_mono dx.kernel_le).trans hback
  have hn : VH ≤ normalizer (UH.conjBy y : Set G) :=
    source_conjugate_normalizes H UH VH d.normalized y hback
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
  exact source_critical_geometry_of_reciprocal_parabolic H UH V1 DR QH VH
    (UH.conjBy y) (V1.conjBy y) ρ d π hker hnatural ξ dx hexterior hV1D hDU hDindex
    y hb hback hlower hstrict hcentral g hradical hf houtside hc hVQ hU hm hcommE
    ((map_mono d.kernel_le).trans hf) hA

open CriticalGeometry NoncentralChiefRefinement BinaryLinear.OuterCyclic

/-- The original critical pair supplies inverse endpoint placement through
its actual vertex stabilizer; all three conclusions concern this same pair. -/
theorem source_critical_pair_geometry_of_mutual_markings
    (L T H V V1 V3 : Subgroup G) (c : CriticalPair L T H V)
    [IsElementaryAbelian 2 (Source.UH H V3)]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V3) V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = (Source.QH H).subgroupOf H)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (ξ : Representation (ZMod 2) H (Fin 6 → ZMod 2))
    (dx : BinaryConjugationSection H (Source.VH H V) (Source.UH H V3) ξ)
    (hexterior : ∀ h w, ξ h w = exteriorMap (π h).val w)
    (hV1 : Nat.card V1 = 2) (hVQ : Source.VH H V ≤ Source.QH H)
    (hseed : ⁅centralizer (V3:Set G),V⁆ ≤ V1)
    (hforward : c.Vgamma ≤ H)
    (hendpoint : Source.VH H V ≤ vertexGroup L T H c.gamma)
    (houtside : ¬ c.Ugamma V3 ≤ Source.QH H)
    (hline : ¬ c.Aone V1 ≤ Source.UH H V3) (hbackline : ¬ V1 ≤ c.Ugamma V3)
    (hstrict : (((Source.UH H V3).conjBy (c.gb:G)⁻¹).subgroupOf H).map π <
      (((Source.VH H V).conjBy (c.gb:G)⁻¹).subgroupOf H).map π)
    (g : SL(4,ZMod 2))
    (hradical : (((Source.VH H V).conjBy (c.gb:G)⁻¹).subgroupOf H).map π ≤
      PlaneRadical.radical.conjBy g)
    (hcommE : ⁅c.Ugamma V3,Source.VH H V ⊓ c.Qgamma⁆ ≤ c.Aone V1) :
    (Source.QH H).relIndex (c.Ugamma V3) = 2 ∧
      8 ≤ Nat.card (c.Ugamma V3 ⊓ Source.VH H V : Subgroup G) ∧
      c.Aone V1 ≤ Source.VH H V := by
  have hb : (Source.VH H V).conjBy (c.gb:G)⁻¹ ≤ H := by
    rw [c.vertexGroup_gamma] at hendpoint
    have hh := map_mono (f := (MulAut.conj (c.gb:G)⁻¹).toMonoidHom) hendpoint
    change (Source.VH H V).conjBy (c.gb:G)⁻¹ ≤ (H.conjBy (c.gb:G)).conjBy (c.gb:G)⁻¹ at hh
    rwa [conjBy_inv] at hh
  exact source_critical_geometry_of_mutual_markings H (Source.UH H V3) V1 V3 V
    (Source.QH H) (Source.VH H V) ρ d π hker hnatural ξ dx hexterior hV1 hVQ
    rfl rfl hseed (c.gb:G) hforward hb houtside hline hbackline hstrict g hradical hcommE

/-- Apply the constructed geometry to the terminal chief-section contradiction.
The centralizer and normalizer premises follow from the source definitions;
the earlier markings and chief obstruction retain their existing owners. -/
theorem source_linear_four_exclusion_of_critical_pair_markings
    (L T H Q V V1 V3 R K : Subgroup G) (c : CriticalPair L T H V)
    [IsElementaryAbelian 2 (Source.VH H V)]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V3) V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = (Source.QH H).subgroupOf H)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (ξ : Representation (ZMod 2) H (Fin 6 → ZMod 2))
    (dx : BinaryConjugationSection H (Source.VH H V) (Source.UH H V3) ξ)
    (hexterior : ∀ h w, ξ h w = exteriorMap (π h).val w)
    (hH : H = normalizer (V1:Set G)) (hV1 : Nat.card V1 = 2)
    (hseed : ⁅centralizer (V3:Set G),V⁆ ≤ V1)
    (hforward : c.Vgamma ≤ H)
    (hendpoint : Source.VH H V ≤ vertexGroup L T H c.gamma)
    (houtside : ¬ c.Ugamma V3 ≤ Source.QH H)
    (hline : ¬ c.Aone V1 ≤ Source.UH H V3) (hbackline : ¬ V1 ≤ c.Ugamma V3)
    (hstrict : (((Source.UH H V3).conjBy (c.gb:G)⁻¹).subgroupOf H).map π <
      (((Source.VH H V).conjBy (c.gb:G)⁻¹).subgroupOf H).map π)
    (g : SL(4,ZMod 2))
    (hradical : (((Source.VH H V).conjBy (c.gb:G)⁻¹).subgroupOf H).map π ≤
      PlaneRadical.radical.conjBy g)
    (hcommE : ⁅c.Ugamma V3,Source.VH H V ⊓ c.Qgamma⁆ ≤ c.Aone V1)
    (hQR : Source.QH H ≤ R) (hindex : Q.relIndex R = 4)
    (hcent : Q ⊓ Source.QH H ≤ centralizer (V3:Set G))
    (hdual : (Source.QH H ⊓ centralizer (V3:Set G)).relIndex (Source.QH H) = 4)
    (hQV : Q ≤ centralizer (V:Set G))
    (hcover : IsSQTK KnownSimple.IsKnownSimple H)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (hKH : K ≤ H) (hK : IsPPerfect 2 K)
    (hmove : ¬ ⁅Source.HC H V3,K⁆ ≤ Source.VH H V)
    (hKonto : Function.Surjective
      ((QuotientGroup.mk' (pCore 2 H)).comp (K.subgroupOf H).subtype))
    (hnotfour : ∀ s : ChiefSeries H,
      s.head.val.map H.subtype = Source.VH H V → s.last.val.map H.subtype = Source.HC H V3 →
      (∀ i : Fin s.length, ∀ D : Subgroup (Section (s i.castSucc) (s i.succ)),
        (∀ k : K.subgroupOf H, ∀ x, x ∈ D →
          sectionAction (s i.castSucc) (s i.succ) k x ∈ D) → D = ⊥ ∨ D = ⊤) →
      s.restrictedNoncentralCount (K.subgroupOf H) = 1 → ∀ i : Fin s.length,
        (¬ ∀ k : K.subgroupOf H, ∀ x,
          sectionAction (s i.castSucc) (s i.succ) k x = x) →
          Nat.card (Section (s i.castSucc) (s i.succ)) ≠ 16) : False := by
  let : IsElementaryAbelian 2 (Source.UH H V3) := IsElementaryAbelian.of_le dx.kernel_le
  let : IsElementaryAbelian 2 (c.Ugamma V3) := IsElementaryAbelian.map _
  have hCQ : Source.HC H V3 ≤ Source.QH H :=
    d.centralizer_le_of_action_kernel (Source.QH H)
      (source_natural_action_kernel H (Source.QH H) ρ π hker hnatural)
  have hVC : Source.VH H V ≤ Source.HC H V3 := le_inf dx.section_le
    ((commutator_eq_bot_iff_le_centralizer.mp (commutator_self_eq_bot_iff.mpr
      (inferInstance : IsMulCommutative (Source.VH H V)))).trans (centralizer_le dx.kernel_le))
  obtain ⟨hstar,hintersection,hAV⟩ := source_critical_pair_geometry_of_mutual_markings
    L T H V V1 V3 c ρ d π hker hnatural ξ dx hexterior hV1 (hVC.trans hCQ)
    hseed hforward hendpoint houtside hline hbackline hstrict g hradical hcommE
  have hUγH : c.Ugamma V3 ≤ H := (map_mono dx.kernel_le).trans hforward
  have hU : Nat.card (c.Ugamma V3) = 32 := by
    change Nat.card ((Source.UH H V3).map _) = 32
    rw [card_map_of_injective (MulAut.conj (c.gb:G)).injective,d.card_section,hV1]
    norm_num
  have hCseed : Source.HC H V3 ≤ centralizer (V3:Set G) :=
    inf_le_right.trans (centralizer_le (le_conjugateSpanBy V3 H))
  have hHC : H ≤ normalizer (Source.HC H V3 : Set G) :=
    (le_inf H.le_normalizer (d.normalized.trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  let Gγ := normalizer (c.Aone V1 : Set G)
  have hA : Nat.card (c.Aone V1) = 2 :=
    (card_map_of_injective (MulAut.conj (c.gb:G)).injective).trans hV1
  have hGγ : Gγ = centralizer (c.Aone V1 : Set G) :=
    le_antisymm (normalizer_le_centralizer_of_card_two _ hA) (Subgroup.centralizer_le_normalizer _)
  have hGn : Gγ ≤ normalizer (c.Ugamma V3 : Set G) := by
    have he : Gγ = H.conjBy (c.gb:G) := by
      exact (map_equiv_normalizer_eq V1 (MulAut.conj (c.gb:G))).symm.trans
        (congrArg (fun B : Subgroup G => B.conjBy (c.gb:G)) hH.symm)
    rw [he]
    exact (map_mono d.normalized).trans ((Source.UH H V3).le_normalizer_map _)
  exact source_linear_four_exclusion H Q (Source.QH H) (Source.HC H V3) V3 V
    (Source.VH H V) R (c.Aone V1) (c.Ugamma V3) Gγ K rfl hVC hQR hindex
    hcent hdual hCQ hCseed hHC hQV rfl hAV hGγ hGn hUγH hU hstar hintersection
    hcover e hKH hK hmove hKonto hnotfour

end CFSG.Quasithin.Chapter13.Section08.LinearFour
