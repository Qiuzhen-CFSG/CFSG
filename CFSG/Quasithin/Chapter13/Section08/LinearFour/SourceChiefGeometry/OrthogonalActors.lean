module

public import Theory.Representation.BinaryPermutation.EightOrthogonalActors
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.Indices
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceExclusion
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.LineContainment
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.OrthogonalSix.Comparison
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.BinaryConjugationSection.Relabel
public import Theory.Representation.BinaryConjugationSection.tensorChief

/-!
# Orthogonal displacement and the critical indices

Every nonidentity even involution moves at least a plane on the actual binary
orthogonal six-space. An elementary group with all movement in one plane has
order at most two. Applied to the literal action on V_H/U_H, these facts give
the lower bound and equality case in 13.8.32(1)–(2); the intersection-index
argument then gives |Uγ : Uγ ∩ Q_H| = 2 and |Uγ ∩ V_H| ≥ 8.

An even involution cannot fix a hyperplane. For the source hyperplane
E = E_H U_H, its nonzero displacement and the commutator containment modulo
U_H recover A₁ ≤ V_H. Relative normality, derived from the original action,
permits lifting a displacement in A₁U_H/U_H to A₁ ∩ V_H.
The exterior-square/deleted-module equivalence transports the same quotient
kernel and both arguments. The final consumer uses all three conclusions in
the terminal contradiction on H_C/V_H.

The earlier setup, initial exterior marking, critical intersection and
hyperplane construction, and the 13.8.31 chief obstruction remain explicit.
Their discharge belongs to qt-d-138-linear-four-source, with the earlier
13.8.27 setup supplied by qt-d-138-six-g2-source; qt-d-1381-source owns final
assembly. These conditional applications do not yet establish 13.8.28.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.32 and the terminal argument, printed pp.965–966. The marked exceptional
isomorphism and its ATLAS attribution are inherited from
`ChapterK.Section01To04.Linear.OrthogonalSix.Comparison`.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G : Type*} [Group G] [Finite G]

/-- The marked orthogonal quotient and the actual commutator containment
give the displacement bound and its equality case used in 13.8.32. -/
theorem source_orthogonal_intersection_image
    (H VH UH QH Uγ : Subgroup G) [IsElementaryAbelian 2 Uγ]
    (π : H →* Equiv.Perm (Fin 8)) (heven : π.range ≤ alternatingGroup (Fin 8))
    (hker : π.ker = QH.subgroupOf H)
    (d : BinaryConjugationSection H VH UH
      ((BinaryPermutation.naturalRepresentation (Fin 8)).comp π))
    (hUH : Uγ ≤ H) (houtside : ¬ Uγ ≤ QH)
    (hcomm : ⁅Uγ,VH⁆ ≤ Uγ ⊓ VH) :
    4 ≤ UH.relIndex (Uγ ⊓ VH) ∧
    (UH.relIndex (Uγ ⊓ VH) = 4 → QH.relIndex Uγ = 2) := by
  let A := (Uγ.subgroupOf H).map π
  let P := d.imageSpace (Uγ ⊓ VH)
  have hcard : Nat.card P = UH.relIndex (Uγ ⊓ VH) :=
    d.imageSpace_card_eq_relIndex _ inf_le_right
  have hAcard : Nat.card A = QH.relIndex Uγ := by
    rw [← relIndex_ker, hker, relIndex_subgroupOf hUH]
  have hAe : A ≤ alternatingGroup (Fin 8) :=
    (map_le_range _ _).trans heven
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := by
    rintro _ ⟨a,ha,rfl⟩
    rw [← map_pow]
    have hh : a ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian a.val ha)
    rw [hh,map_one]
  have hmove : ∀ a ∈ A,
      (BinaryPermutation.naturalRepresentation (Fin 8) a - LinearMap.id).range ≤ P := by
    rintro _ ⟨a,ha,rfl⟩
    exact d.displacement_range_le_imageSpace_of_commutator_le Uγ (Uγ ⊓ VH) hcomm a ha
  obtain ⟨a,ha,hna⟩ := SetLike.not_le_iff_exists.mp houtside
  let aH : H := ⟨a,hUH ha⟩
  have haA : π aH ∈ A := mem_map_of_mem π ha
  have hne : π aH ≠ 1 := by
    intro hh
    have hm : aH ∈ π.ker := hh
    rw [hker] at hm
    exact hna hm
  have hlower := (BinaryPermutation.EightOrthogonalActors.two_le_displacement
    (π aH) (hAe haA) hne (hA2 _ haA)).trans (Submodule.finrank_mono (hmove _ haA))
  have hPcard : Nat.card P = 2 ^ Module.finrank (ZMod 2) P := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  constructor
  · rw [← hcard,hPcard]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hlower
  · intro he
    have hdim : Module.finrank (ZMod 2) P = 2 := by
      have hh : 2 ^ Module.finrank (ZMod 2) P = 2 ^ 2 := by
        rw [← hPcard,hcard,he]
        norm_num
      exact Nat.pow_right_injective (by decide) hh
    have hb := BinaryPermutation.EightOrthogonalActors.card_le_two_of_plane_displacement
      A hAe hA2 P hdim hmove
    rw [hAcard] at hb
    have hn : QH.relIndex Uγ ≠ 1 := fun hh => houtside (relIndex_eq_one.mp hh)
    have hp : QH.relIndex Uγ ≠ 0 := (QH.subgroupOf Uγ).index_ne_zero_of_finite
    omega

/-- The orthogonal geometry proves both literal intersection indices, without
assuming either the lower displacement bound or its equality case. -/
theorem source_critical_indices_of_orthogonal_action
    (H VH UH QH Uγ : Subgroup G) [IsElementaryAbelian 2 Uγ]
    (π : H →* Equiv.Perm (Fin 8)) (heven : π.range ≤ alternatingGroup (Fin 8))
    (hker : π.ker = QH.subgroupOf H)
    (d : BinaryConjugationSection H VH UH
      ((BinaryPermutation.naturalRepresentation (Fin 8)).comp π))
    (hUH : Uγ ≤ H) (houtside : ¬ Uγ ≤ QH)
    (hcomm : ⁅Uγ,VH⁆ ≤ Uγ ⊓ VH)
    (hVQ : VH ≤ QH) (hU : Nat.card Uγ = 32) (hmeet : Uγ ⊓ UH ≠ ⊥) :
    QH.relIndex Uγ = 2 ∧ 8 ≤ Nat.card (Uγ ⊓ VH : Subgroup G) := by
  obtain ⟨hi,he⟩ := source_orthogonal_intersection_image H VH UH QH Uγ
    π heven hker d hUH houtside hcomm
  exact source_critical_intersection_indices Uγ UH VH QH d.kernel_le hVQ
    hU houtside hmeet hi he

/-- An even involution cannot fix a hyperplane of the orthogonal quotient.
The source commutator into A1 modulo UH therefore places the order-two line in VH. -/
theorem source_line_le_of_orthogonal_hyperplane
    (H VH UH QH Uγ E A1 : Subgroup G) [IsElementaryAbelian 2 Uγ]
    (π : H →* Equiv.Perm (Fin 8)) (heven : π.range ≤ alternatingGroup (Fin 8))
    (hker : π.ker = QH.subgroupOf H)
    (d : BinaryConjugationSection H VH UH
      ((BinaryPermutation.naturalRepresentation (Fin 8)).comp π))
    (hUH : Uγ ≤ H) (houtside : ¬ Uγ ≤ QH)
    (hUE : UH ≤ E) (hEV : E ≤ VH) (hindex : E.relIndex VH = 2)
    (hcomm : ⁅Uγ,E⁆ ≤ A1 ⊔ UH) (hAH : A1 ≤ H)
    (hA : Nat.card A1 = 2) : A1 ≤ VH := by
  obtain ⟨a,ha,hna⟩ := SetLike.not_le_iff_exists.mp houtside
  let aH : H := ⟨a,hUH ha⟩
  have hne : π aH ≠ 1 := by
    intro hh
    have hm : aH ∈ π.ker := hh
    rw [hker] at hm
    exact hna hm
  have ha2 : (π aH)^2 = 1 := by
    rw [← map_pow]
    have hh : aH^2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian a ha)
    rw [hh,map_one]
  have hlower := BinaryPermutation.EightOrthogonalActors.two_le_displacement
    (π aH) (heven ⟨aH,rfl⟩) hne ha2
  have hdim := d.imageSpace_codimension_of_index E hEV hUE 1 (by simpa using hindex)
  obtain ⟨w,hw,hm⟩ : ∃ w ∈ d.imageSpace E,
      BinaryPermutation.naturalRepresentation (Fin 8) (π aH) w ≠ w := by
    by_contra! hh
    have hle : d.imageSpace E ≤
        (BinaryPermutation.naturalRepresentation (Fin 8) (π aH) - LinearMap.id).ker := by
      intro w hw
      exact sub_eq_zero.mpr (hh w hw)
    have hd := Submodule.finrank_mono hle
    have hn := (BinaryPermutation.naturalRepresentation (Fin 8) (π aH) -
      LinearMap.id).finrank_range_add_finrank_ker
    omega
  obtain ⟨x,hx,hxw⟩ := (d.mem_imageSpace_iff E w).mp hw
  let c : VH := (⟨(aH:G)*(x:G)*(aH:G)⁻¹,
    (mem_normalizer_iff.mp (d.normalized aH.property) x).mp x.property⟩ : VH) * x⁻¹
  have hc : (c:G) ∈ A1 ⊔ UH := hcomm (commutator_mem_commutator ha hx)
  have hnorm : H ≤ normalizer (UH : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (d.kernel_le.trans d.section_le)).mp
      d.kernel_normal_actor
  have hprod := coe_mul_of_left_le_normalizer_right A1 UH (hAH.trans hnorm)
  change (c:G) ∈ (↑(A1 ⊔ UH) : Set G) at hc
  rw [hprod] at hc
  obtain ⟨b,hb,u,hu,hbu⟩ := hc
  have hbV : b ∈ VH := by
    have he : b = (c:G) * u⁻¹ := by rw [← hbu]; group
    rw [he]
    exact VH.mul_mem c.property (VH.inv_mem (d.kernel_le hu))
  let bV : VH := ⟨b,hbV⟩
  let uV : VH := ⟨u,d.kernel_le hu⟩
  have hcbu : c = bV * uV := Subtype.ext hbu.symm
  have huone : d.coordinates uV = 1 := (d.coordinates_eq_one_iff uV).mpr hu
  have hbimage : (d.coordinates bV).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 8) (π aH) w - w := by
    calc
      (d.coordinates bV).toAdd = (d.coordinates c).toAdd := by
        rw [hcbu,map_mul,huone,mul_one]
      _ = _ := by
        change (d.coordinates (_ * x⁻¹)).toAdd = _
        rw [map_mul,map_inv]
        change (d.coordinates _).toAdd + -(d.coordinates x).toAdd = _
        rw [d.equivariant,hxw]
        simp only [MonoidHom.comp_apply, sub_eq_add_neg]
  exact source_line_le_of_nonzero_image d A1 hA _ (sub_ne_zero.mpr hm)
    ((d.mem_imageSpace_iff A1 _).mpr ⟨bV,hb,hbimage⟩)

open scoped MatrixGroups
open Atlas.Order20160A8.Bivectors (exteriorMap)
open ChapterK.Linear.OrthogonalSix

/-- The exterior marking already used for the tensor span supplies the same
critical indices. The actual exceptional isomorphism intertwines the actions. -/
theorem source_critical_indices_of_exterior_action
    (H VH UH QH Uγ : Subgroup G) [IsElementaryAbelian 2 Uγ]
    (ρ : Representation (ZMod 2) H (Fin 6 → ZMod 2))
    (π : H →* SL(4, ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hact : ∀ h x, ρ h x = exteriorMap (π h).val x)
    (d : BinaryConjugationSection H VH UH ρ)
    (hUH : Uγ ≤ H) (houtside : ¬ Uγ ≤ QH)
    (hcomm : ⁅Uγ,VH⁆ ≤ Uγ ⊓ VH)
    (hVQ : VH ≤ QH) (hU : Nat.card Uγ = 32) (hmeet : Uγ ⊓ UH ≠ ⊥) :
    QH.relIndex Uγ = 2 ∧ 8 ≤ Nat.card (Uγ ⊓ VH : Subgroup G) := by
  let f := sl4EquivAlternating.toMonoidHom.comp π
  let ψ := (alternatingGroup (Fin 8)).subtype.comp f
  let σ := (BinaryPermutation.naturalRepresentation (Fin 8)).comp ψ
  let e : ρ.Equiv σ := {
    __ := exteriorEquivNatural
    isIntertwining' h := by
      apply LinearMap.ext
      intro x
      change exteriorEquivNatural (ρ h x) = σ h (exteriorEquivNatural x)
      rw [hact]
      exact exteriorEquivNatural_intertwines (π h) x }
  have hψ : ψ.ker = QH.subgroupOf H := by
    rw [← hker]
    ext h
    change (sl4EquivAlternating (π h)).val = 1 ↔ π h = 1
    constructor
    · intro hh
      exact sl4EquivAlternating.injective ((Subtype.ext hh).trans sl4EquivAlternating.map_one.symm)
    · intro hh
      rw [hh,map_one]
      rfl
  let p := BinaryConjugationSection.relabel (MonoidHom.id H) d e
  exact source_critical_indices_of_orthogonal_action H VH UH QH Uγ ψ
    (by rintro _ ⟨h,rfl⟩; exact (f h).property) hψ p hUH houtside hcomm hVQ hU hmeet

/-- All three conclusions of 13.8.32 follow from the marked orthogonal quotient,
the critical intersection, and the original hyperplane commutator modulo UH. -/
theorem source_critical_geometry_of_exterior_action
    (H VH UH QH Uγ E A1 : Subgroup G) [IsElementaryAbelian 2 Uγ]
    (ρ : Representation (ZMod 2) H (Fin 6 → ZMod 2))
    (π : H →* SL(4, ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hact : ∀ h x, ρ h x = exteriorMap (π h).val x)
    (d : BinaryConjugationSection H VH UH ρ)
    (hUH : Uγ ≤ H) (houtside : ¬ Uγ ≤ QH)
    (hcomm : ⁅Uγ,VH⁆ ≤ Uγ ⊓ VH)
    (hVQ : VH ≤ QH) (hU : Nat.card Uγ = 32) (hmeet : Uγ ⊓ UH ≠ ⊥)
    (hUE : UH ≤ E) (hEV : E ≤ VH) (hindex : E.relIndex VH = 2)
    (hcommE : ⁅Uγ,E⁆ ≤ A1 ⊔ UH) (hAH : A1 ≤ H) (hA : Nat.card A1 = 2) :
    QH.relIndex Uγ = 2 ∧ 8 ≤ Nat.card (Uγ ⊓ VH : Subgroup G) ∧ A1 ≤ VH := by
  let f := sl4EquivAlternating.toMonoidHom.comp π
  let ψ := (alternatingGroup (Fin 8)).subtype.comp f
  let σ := (BinaryPermutation.naturalRepresentation (Fin 8)).comp ψ
  let e : ρ.Equiv σ := {
    __ := exteriorEquivNatural
    isIntertwining' h := by
      apply LinearMap.ext
      intro x
      change exteriorEquivNatural (ρ h x) = σ h (exteriorEquivNatural x)
      rw [hact]
      exact exteriorEquivNatural_intertwines (π h) x }
  have hψ : ψ.ker = QH.subgroupOf H := by
    rw [← hker]
    ext h
    change (sl4EquivAlternating (π h)).val = 1 ↔ π h = 1
    constructor
    · intro hh
      exact sl4EquivAlternating.injective ((Subtype.ext hh).trans sl4EquivAlternating.map_one.symm)
    · intro hh
      rw [hh,map_one]
      rfl
  let p := BinaryConjugationSection.relabel (MonoidHom.id H) d e
  have heven : ψ.range ≤ alternatingGroup (Fin 8) := by
    rintro _ ⟨h,rfl⟩
    exact (f h).property
  obtain ⟨hi,hj⟩ := source_critical_indices_of_orthogonal_action H VH UH QH Uγ ψ
    heven hψ p hUH houtside hcomm hVQ hU hmeet
  exact ⟨hi,hj,source_line_le_of_orthogonal_hyperplane H VH UH QH Uγ E A1
    ψ heven hψ p hUH houtside hUE hEV hindex hcommE hAH hA⟩

open BinaryLinear.OuterCyclic NoncentralChiefRefinement

/-- The terminal source application derives the critical intersection bounds
and line placement from the actual orthogonal action. The earlier setup, hyperplane geometry,
and chief obstruction remain explicit for this theorem family's final assembly. -/
theorem source_linear_four_exclusion_of_exterior_action
    (H Q QH HC UH V3 V VH R A1 Uγ Gγ K E : Subgroup G)
    [IsElementaryAbelian 2 Uγ]
    (hQH : QH = H.pCoreIn 2) (hVC : VH ≤ HC)
    (hQR : QH ≤ R) (hindex : Q.relIndex R = 4)
    (hcent : Q ⊓ QH ≤ centralizer (V3 : Set G))
    (hdual : (QH ⊓ centralizer (V3 : Set G)).relIndex QH = 4)
    (hHCQH : HC ≤ QH) (hHCV3 : HC ≤ centralizer (V3 : Set G))
    (hHHC : H ≤ normalizer (HC : Set G))
    (hQV : Q ≤ centralizer (V : Set G))
    (hVH : VH = conjugateSpanBy V H)
    (hGγ : Gγ = centralizer (A1 : Set G))
    (hGγUγ : Gγ ≤ normalizer (Uγ : Set G)) (hUγH : Uγ ≤ H)
    (hU : Nat.card Uγ = 32)
    (ρ : Representation (ZMod 2) H (Fin 6 → ZMod 2))
    (π : H →* SL(4, ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hact : ∀ h x, ρ h x = exteriorMap (π h).val x)
    (d : BinaryConjugationSection H VH UH ρ)
    (houtside : ¬ Uγ ≤ QH) (hmeet : Uγ ⊓ UH ≠ ⊥)
    (hcommV : ⁅Uγ,VH⁆ ≤ Uγ ⊓ VH)
    (hUE : UH ≤ E) (hEV : E ≤ VH) (hhyperplane : E.relIndex VH = 2)
    (hcommE : ⁅Uγ,E⁆ ≤ A1 ⊔ UH) (hAH : A1 ≤ H) (hA : Nat.card A1 = 2)
    (hcover : IsSQTK KnownSimple.IsKnownSimple H)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (hKH : K ≤ H) (hK : IsPPerfect 2 K) (hmove : ¬ ⁅HC, K⁆ ≤ VH)
    (hKonto : Function.Surjective
      ((QuotientGroup.mk' (pCore 2 H)).comp (K.subgroupOf H).subtype))
    (hnotfour : ∀ s : ChiefSeries H,
      s.head.val.map H.subtype = VH → s.last.val.map H.subtype = HC →
      (∀ i : Fin s.length, ∀ D : Subgroup (Section (s i.castSucc) (s i.succ)),
        (∀ k : K.subgroupOf H, ∀ x, x ∈ D →
          sectionAction (s i.castSucc) (s i.succ) k x ∈ D) → D = ⊥ ∨ D = ⊤) →
      s.restrictedNoncentralCount (K.subgroupOf H) = 1 → ∀ i : Fin s.length,
        (¬ ∀ k : K.subgroupOf H, ∀ x,
          sectionAction (s i.castSucc) (s i.succ) k x = x) →
          Nat.card (Section (s i.castSucc) (s i.succ)) ≠ 16) : False := by
  obtain ⟨hstar,hintersection,hA1⟩ := source_critical_geometry_of_exterior_action
    H VH UH QH Uγ E A1 ρ π hker hact d hUγH houtside hcommV
    (hVC.trans hHCQH) hU hmeet hUE hEV hhyperplane hcommE hAH hA
  exact source_linear_four_exclusion H Q QH HC V3 V VH R A1 Uγ Gγ K
    hQH hVC hQR hindex hcent hdual hHCQH hHCV3 hHHC hQV hVH hA1 hGγ
    hGγUγ hUγH hU hstar hintersection hcover e hKH hK hmove hKonto hnotfour

end CFSG.Quasithin.Chapter13.Section08.LinearFour
