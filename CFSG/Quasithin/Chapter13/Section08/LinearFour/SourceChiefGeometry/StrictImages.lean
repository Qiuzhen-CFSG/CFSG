module
public import Theory.Representation.BinaryConjugationSection.OrthogonalMovement
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.ReciprocalAxes
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.CommutatorComparison

/-!
# Strict critical images from the literal orthogonal action

If the inverse critical U- and V-images were equal, the natural-action
kernel would force their commutator with U_H into Uγ together with V₁.
Conjugating by the original transporter makes the forward exterior
commutator lie in U_H together with A₁. A nontrivial elementary actor on
the orthogonal six-space cannot have such a one-line image. This proves
the required strict inclusion, without a separate generation premise.

The same natural-action kernel gives [Uγ,V_H ∩ Qγ] ≤ A₁. Both facts feed
the actual CriticalPair geometry and terminal chief-section contradiction,
removing the strict-image and kernel-commutator premises there. All quotient
maps and the source conjugator are retained.

The initial natural/tensor/exterior markings, compatible extra-line movement,
excluded lines, plane-radical placement and 13.8.31 chief obstruction remain
obligations of qt-d-138-linear-four-source. Earlier 13.8.27 setup belongs to
qt-d-138-six-g2-source, and final 13.8.1 assembly to qt-d-1381-source. This
conditional increment does not complete Theorem 13.8.28.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
13.8.11(1), 13.8.32(3) and the terminal argument, printed pp.950,965–966.
-/

public noncomputable section
open Subgroup Representation BinaryParabolicExteriorSquare
open scoped MatrixGroups
open Atlas.Order20160A8.Bivectors (exteriorMap)
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G : Type*} [Group G] [Finite G]

open ChapterK.Linear.OrthogonalSix
/-- The actual exterior marking excludes a one-line commutator image, using
the retained exceptional-isomorphism action equivalence. -/
theorem source_exterior_commutator_not_le_line
    (H VH UH QH B A : Subgroup G) [IsElementaryAbelian 2 B]
    (ρ : Representation (ZMod 2) H (Fin 6 → ZMod 2))
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hact : ∀ h w, ρ h w = exteriorMap (π h).val w)
    (d : BinaryConjugationSection H VH UH ρ)
    (hBH : B ≤ H) (houtside : ¬ B ≤ QH) (hAH : A ≤ H)
    (hA : Nat.card A = 2) : ¬ ⁅B,VH⁆ ≤ UH ⊔ A := by
  let f := sl4EquivAlternating.toMonoidHom.comp π
  let ψ := (alternatingGroup (Fin 8)).subtype.comp f
  let σ := (BinaryPermutation.naturalRepresentation (Fin 8)).comp ψ
  let e : ρ.Equiv σ := {
    __ := exteriorEquivNatural
    isIntertwining' h := by
      apply LinearMap.ext
      intro w
      change exteriorEquivNatural (ρ h w) = σ h (exteriorEquivNatural w)
      rw [hact]
      exact exteriorEquivNatural_intertwines (π h) w }
  have hψ : ψ.ker = QH.subgroupOf H := by
    rw [←hker]
    ext h
    change (sl4EquivAlternating (π h)).val = 1 ↔ π h = 1
    constructor
    · intro hh
      exact sl4EquivAlternating.injective ((Subtype.ext hh).trans sl4EquivAlternating.map_one.symm)
    · intro hh
      rw [hh,map_one]
      rfl
  let p := BinaryConjugationSection.relabel (MonoidHom.id H) d e
  exact BinaryConjugationSection.orthogonal_commutator_not_le_line H VH UH QH B A ψ
    (by rintro _ ⟨h,rfl⟩; exact (f h).property) hψ p hBH houtside hAH hA

omit [Finite G] in
/-- The kernel of the marked natural action centralizes the literal quotient
U_H/V₁, so the original group commutator lies in V₁. -/
theorem source_natural_kernel_commutator
    (H UH V1 QH : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hQH : QH ≤ H) : ⁅QH,UH⁆ ≤ V1 := by
  apply commutator_le.mpr
  intro a ha u hu
  let uU : UH := ⟨u,hu⟩
  let v : UH := ⟨a*u*a⁻¹,(mem_normalizer_iff.mp (d.normalized (hQH ha)) u).mp hu⟩
  apply (d.coordinates_eq_one_iff (v*uU⁻¹)).mp
  apply Multiplicative.toAdd.injective
  change (d.coordinates (v*uU⁻¹)).toAdd = 0
  rw [map_mul,map_inv]
  change (d.coordinates v).toAdd + -(d.coordinates uU).toAdd = 0
  rw [d.equivariant ⟨a,hQH ha⟩ uU,
    (source_natural_action_kernel H QH ρ π hker hnatural ⟨a,hQH ha⟩).mpr ha,
    add_neg_cancel]

omit [Finite G] in
private theorem equal_images_commutator_bound
    (H F U V Z QH : Subgroup G) (π : H →* SL(4,ZMod 2))
    (hker : π.ker = QH.subgroupOf H)
    (hFH : F ≤ H) (hVH : V ≤ H) (hZH : Z ≤ H) (hQH : QH ≤ H)
    (hZN : H ≤ normalizer (Z:Set G))
    (hUV : U ≤ V) (hVF : V ≤ normalizer (F:Set G))
    (hFQ : ⁅F,QH⁆ ≤ Z)
    (he : (U.subgroupOf H).map π = (V.subgroupOf H).map π) :
    ⁅F,V⁆ ≤ ⁅F,U⁆ ⊔ Z := by
  let : (Z.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hZN
  let : (QH.subgroupOf H).Normal := hker ▸ inferInstance
  have hN : V.subgroupOf H ≤ normalizer (F.subgroupOf H : Set H) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    apply map_le_iff_le_comap.mp
    rw [map_commutator,map_subgroupOf_eq_of_le hFH,map_subgroupOf_eq_of_le hVH]
    exact le_normalizer_iff_commutator_le_left.mp hVF
  have hQ : ⁅F.subgroupOf H,QH.subgroupOf H⁆ ≤ Z.subgroupOf H := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,map_subgroupOf_eq_of_le hFH,map_subgroupOf_eq_of_le hQH]
    exact hFQ
  have he' : (U.subgroupOf H).map (QuotientGroup.mk' (QH.subgroupOf H)) =
      (V.subgroupOf H).map (QuotientGroup.mk' (QH.subgroupOf H)) := by
    apply map_eq_map_iff.mpr
    simpa only [QuotientGroup.ker_mk',hker] using (map_eq_map_iff.mp he)
  have hc := CriticalGeometry.commutator_bound_of_same_core_image
    (F.subgroupOf H) (U.subgroupOf H) (V.subgroupOf H)
    (QH.subgroupOf H) (Z.subgroupOf H) (subgroupOf_mono H hUV) hN hQ he'
  have hm := map_mono (f := H.subtype) hc
  rwa [map_commutator,Subgroup.map_sup,map_commutator,
    map_subgroupOf_eq_of_le hFH,map_subgroupOf_eq_of_le (hUV.trans hVH),
    map_subgroupOf_eq_of_le hVH,map_subgroupOf_eq_of_le hZH] at hm

/-- The inverse critical images are strictly nested. Equality would confine
forward exterior displacement to the conjugate of V₁, contradicting the
plane displacement bound. The same transporter is used at both endpoints. -/
theorem source_inverse_critical_images_strict
    (H UH V1 QH VH : Subgroup G) [IsElementaryAbelian 2 UH]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (ξ : Representation (ZMod 2) H (Fin 6 → ZMod 2))
    (dx : BinaryConjugationSection H VH UH ξ)
    (hexterior : ∀ h w, ξ h w = exteriorMap (π h).val w)
    (hV1 : Nat.card V1 = 2) (hQH : QH ≤ H)
    (y : G) (hforward : UH.conjBy y ≤ H) (hback : VH.conjBy y⁻¹ ≤ H)
    (houtside : ¬ UH.conjBy y ≤ QH) :
    ((UH.conjBy y⁻¹).subgroupOf H).map π <
      ((VH.conjBy y⁻¹).subgroupOf H).map π := by
  let : IsElementaryAbelian 2 (UH.conjBy y) := IsElementaryAbelian.map _
  have hnZ : H ≤ normalizer (V1:Set G) :=
    (normal_subgroupOf_iff_le_normalizer (d.kernel_le.trans d.section_le)).mp d.kernel_normal_actor
  have hUV : UH.conjBy y⁻¹ ≤ VH.conjBy y⁻¹ := map_mono dx.kernel_le
  refine lt_of_le_of_ne (map_mono (subgroupOf_mono H hUV)) ?_
  intro he
  have hc := equal_images_commutator_bound H UH (UH.conjBy y⁻¹)
    (VH.conjBy y⁻¹) V1 QH π hker d.section_le hback
    (d.kernel_le.trans d.section_le) hQH hnZ hUV (hback.trans d.normalized)
    (by rw [commutator_comm]; exact source_natural_kernel_commutator H UH V1 QH ρ d π hker hnatural hQH) he
  have hn : UH ≤ normalizer (UH.conjBy y⁻¹ : Set G) := by
    have hh := (map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) (hforward.trans d.normalized)).trans
      (UH.le_normalizer_map (MulAut.conj y⁻¹).toMonoidHom)
    change (UH.conjBy y).conjBy y⁻¹ ≤ _ at hh
    rwa [conjBy_inv] at hh
  have hb := hc.trans (sup_le_sup (le_normalizer_iff_commutator_le_right.mp hn) le_rfl)
  have hm := map_mono (f := (MulAut.conj y).toMonoidHom) hb
  rw [map_commutator,Subgroup.map_sup] at hm
  change ⁅UH.conjBy y,(VH.conjBy y⁻¹).conjBy y⁆ ≤
    (UH.conjBy y⁻¹).conjBy y ⊔ V1.conjBy y at hm
  rw [conjBy_inv',conjBy_inv'] at hm
  have hA : Nat.card (V1.conjBy y) = 2 :=
    (card_map_of_injective (MulAut.conj y).injective).trans hV1
  exact source_exterior_commutator_not_le_line H VH UH QH (UH.conjBy y) (V1.conjBy y)
    ξ π hker hexterior dx hforward houtside ((map_mono d.kernel_le).trans hforward) hA hm

omit [Finite G] in
/-- The natural kernel commutator, conjugated by the original transporter,
gives the bound on the actual intersection V_H ∩ Qγ. -/
theorem source_critical_kernel_commutator
    (H UH V1 QH VH : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hQH : QH ≤ H) (y : G) :
    ⁅UH.conjBy y,VH ⊓ QH.conjBy y⁆ ≤ V1.conjBy y := by
  have hc := source_natural_kernel_commutator H UH V1 QH ρ d π hker hnatural hQH
  rw [commutator_comm] at hc
  have hm := map_mono (f := (MulAut.conj y).toMonoidHom) hc
  rw [map_commutator] at hm
  exact (commutator_mono le_rfl inf_le_right).trans hm

open CriticalGeometry NoncentralChiefRefinement BinaryLinear.OuterCyclic

/-- The marked actions prove strictness and the kernel commutator for the
actual critical pair, then give all three conclusions of 13.8.32 from the
remaining parabolic and excluded-line inputs. -/
theorem source_critical_pair_geometry_of_parabolic_markings
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
    (g : SL(4,ZMod 2))
    (hradical : (((Source.VH H V).conjBy (c.gb:G)⁻¹).subgroupOf H).map π ≤
      PlaneRadical.radical.conjBy g)
    :
    (Source.QH H).relIndex (c.Ugamma V3) = 2 ∧
      8 ≤ Nat.card (c.Ugamma V3 ⊓ Source.VH H V : Subgroup G) ∧
      c.Aone V1 ≤ Source.VH H V := by
  have hb : (Source.VH H V).conjBy (c.gb:G)⁻¹ ≤ H := by
    rw [c.vertexGroup_gamma] at hendpoint
    have hh := map_mono (f := (MulAut.conj (c.gb:G)⁻¹).toMonoidHom) hendpoint
    change (Source.VH H V).conjBy (c.gb:G)⁻¹ ≤ (H.conjBy (c.gb:G)).conjBy (c.gb:G)⁻¹ at hh
    rwa [conjBy_inv] at hh
  have hQH : Source.QH H ≤ H := pCoreIn_le 2 H
  have hstrict := source_inverse_critical_images_strict H (Source.UH H V3) V1
    (Source.QH H) (Source.VH H V) ρ d π hker hnatural ξ dx hexterior hV1 hQH
    (c.gb:G) ((map_mono dx.kernel_le).trans hforward) hb houtside
  have hcommE := source_critical_kernel_commutator H (Source.UH H V3) V1
    (Source.QH H) (Source.VH H V) ρ d π hker hnatural hQH (c.gb:G)
  exact source_critical_geometry_of_mutual_markings H (Source.UH H V3) V1 V3 V
    (Source.QH H) (Source.VH H V) ρ d π hker hnatural ξ dx hexterior hV1 hVQ
    rfl rfl hseed (c.gb:G) hforward hb houtside hline hbackline hstrict g hradical hcommE


/-- Apply the constructed strict critical images and kernel commutator to
the terminal exclusion. The remaining markings, parabolic placement and
chief obstruction must still be discharged by this source family. -/
theorem source_linear_four_exclusion_of_parabolic_markings
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
    (g : SL(4,ZMod 2))
    (hradical : (((Source.VH H V).conjBy (c.gb:G)⁻¹).subgroupOf H).map π ≤
      PlaneRadical.radical.conjBy g)
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
  have hb : (Source.VH H V).conjBy (c.gb:G)⁻¹ ≤ H := by
    rw [c.vertexGroup_gamma] at hendpoint
    have hh := map_mono (f := (MulAut.conj (c.gb:G)⁻¹).toMonoidHom) hendpoint
    change (Source.VH H V).conjBy (c.gb:G)⁻¹ ≤ (H.conjBy (c.gb:G)).conjBy (c.gb:G)⁻¹ at hh
    rwa [conjBy_inv] at hh
  have hQH : Source.QH H ≤ H := pCoreIn_le 2 H
  have hstrict := source_inverse_critical_images_strict H (Source.UH H V3) V1
    (Source.QH H) (Source.VH H V) ρ d π hker hnatural ξ dx hexterior hV1 hQH
    (c.gb:G) ((map_mono dx.kernel_le).trans hforward) hb houtside
  have hcommE := source_critical_kernel_commutator H (Source.UH H V3) V1
    (Source.QH H) (Source.VH H V) ρ d π hker hnatural hQH (c.gb:G)
  exact source_linear_four_exclusion_of_critical_pair_markings L T H Q V V1 V3 R K c
    ρ d π hker hnatural ξ dx hexterior hH hV1 hseed hforward hendpoint houtside
    hline hbackline hstrict g hradical hcommE hQR hindex hcent hdual hQV hcover e
    hKH hK hmove hKonto hnotfour

end CFSG.Quasithin.Chapter13.Section08.LinearFour
