module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.SevenExclusion
public import CFSG.Quasithin.Chapter10.SourceNonnormalFixedResidual
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.Alternatives
public import Theory.Representation.BinaryAlternatingFivePointStabilizer
public import Theory.GroupTheory.PCoreCoverEquiv

/-!
# The ordinary A₇ obstruction in source point-centralizer control

For the literal deleted A₅ moved module, every vector has a cubic
stabilizer in the original component L. The opposite component K=Lᵗ
commutes with L modulo its two-core. Odd centralizer covering gives an
order-five element of K commuting with that cubic. If a normal containing
C-component of C_G(v) had A₇ two-core quotient, cubic containment and the
centralizer of a five-cycle would give a contradiction.

The source module alternatives therefore leave only the natural SL₂(4)
quotient in this containing-A₇ situation. Irreducibility is retained for
the chosen source setup; it is not inferred for an arbitrary initial FSU.
This removes the ordinary A₇-block branch of 10.2.9. The other containing
component classifications and earlier10.2.6 normalizer bounds remain
necessary for the full assertion C_G(v)≤M.

Source: Aschbacher–Smith,10.2.9, printed pp.750–753, especially the final
ordinary A₇-block contradiction on p.753 (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- An original component centralizes its distinct Sylow conjugate's
intrinsic two-core quotient. No block structure is assumed. -/
theorem source_conjugate_sectionCentralizer
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    L ≤ sectionCentralizer (L.map (MulAut.conj t).toMonoidHom) := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let tH : H := ⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩
  let B := A.map (MulAut.conj tH).toMonoidHom
  let K := L.map (MulAut.conj t).toMonoidHom
  have hmapA : A.map H.subtype = L := map_subgroupOf_eq_of_le le_sup_left
  have hmapB : B.map H.subtype = K := by
    rw [show B = A.map (MulAut.conj tH).toMonoidHom from rfl,map_map]
    rw [show H.subtype.comp (MulAut.conj tH).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp H.subtype from rfl,←map_map,hmapA]
  have hB : B.IsCComponent := D.maximal.1.1.map_equiv (MulAut.conj tH)
  have hc : ⁅A,B⁆ ≤ pCore 2 H := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [map_commutator,hmapA,hmapB]
    exact source_conjugate_commutator_le_core D.simpleQTKE D.maximal.1 ht htn
  obtain ⟨hn,hc⟩ := section_kernel_controls_cComponent hB hc
  apply (le_sectionCentralizer_iff L K).mpr
  constructor
  · rw [←hmapA,←hmapB]
    exact (map_mono hn).trans (B.le_normalizer_map H.subtype)
  · have hm := map_mono (f := H.subtype) hc
    rw [map_commutator,hmapA,hmapB,map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
      hmapB] at hm
    exact hm

private theorem five_centralizes_section_cubic
    (K : Subgroup G) [Group.IsPerfect K]
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (x : G) (hx : orderOf x = 3) (hxc : x ∈ sectionCentralizer K) :
    ∃ y : G, y ∈ K ∧ orderOf y = 5 ∧ Commute x y := by
  let B := zpowers x
  let A := (solvableResidual (K ⊓ centralizer (B : Set G) : Subgroup G)).map
    (K ⊓ centralizer (B : Set G)).subtype
  have hAL : A ≤ K := (map_subtype_le _).trans inf_le_left
  have hb : Odd (Nat.card B) := by rw [Nat.card_zpowers,hx]; decide
  have hcover := Chapter4.Section04.perfect_centralizer_cover K B (zpowers_le.mpr hxc) hb
  obtain ⟨eA,_⟩ := exists_pCoreQuotientEquiv_of_cover hAL hcover.subset
  have hd : 5 ∣ Nat.card A := by
    apply dvd_trans ?_ (card_quotient_dvd_card (pCore 2 A))
    rw [Nat.card_congr (eA.trans e).toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' (G := A) 5 hd
  refine ⟨y,hAL y.property,(orderOf_coe y).trans hy,?_⟩
  have hc : (y : G) ∈ centralizer (B : Set G) :=
    ((map_subtype_le _).trans inf_le_right) y.property
  exact hc x (mem_zpowers x)

/-- Every nonzero vector of the actual deleted moved module excludes a
normal A₇-quotient C-component containing the opposite original component. -/
theorem source_a5_deleted_point_component_not_seven
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (c : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin 5)).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    {t v : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hv : v ∈ ⁅D.fullModule,L⁆) (hvne : v ≠ 1)
    (I : Subgroup G) (hKI : L.map (MulAut.conj t).toMonoidHom ≤ I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G)) :
    ¬ Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨eI⟩
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨x,hxL,hx3,hxv⟩ := c.exists_cubic_point_centralizer q
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hk v hv
  let K := L.map (MulAut.conj t).toMonoidHom
  let d := (MulAut.conj t).subgroupMap L
  let eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ d.symm (pCore_map_iso 2 d.symm)).trans e
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect K := Group.IsPerfect.map (MulAut.conj t).toMonoidHom
  obtain ⟨y,hyK,hy5,hxy⟩ := five_centralizes_section_cubic K eK x hx3
    (source_conjugate_sectionCentralizer D ht htn hxL)
  have hv2 : orderOf v = 2 := by
    let := source_original_full_moved_elementary D
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian v hv) hvne
  let X := centralizer ({v} : Set G)
  let J := I.subgroupOf X
  let dI : J ≃* I := subgroupOfEquivOfLe hIX
  let eJ : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.congr _ _ dI (pCore_map_iso 2 dI)).trans eI
  let : J.Normal := (normal_subgroupOf_iff_le_normalizer hIX).mpr hNI
  let xX : X := ⟨x,hxv⟩
  let yX : X := ⟨y,hIX (hKI hyK)⟩
  apply FixedCenterOvercomponent.seven_component_not_commute_three_five J hI eJ
    ((D.simpleQTKE.involution_centralizer_sqtk hv2).stronglyQuasithin 3
      (by decide) (by decide)) xX yX
  · exact (orderOf_coe xX).symm.trans hx3
  · exact (orderOf_coe yX).symm.trans hy5
  · exact hKI hyK
  · rw [normalizer_eq_top]
    trivial
  · exact Subtype.ext hxy.eq

local instance pointControlMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance pointControlFieldFourAlgebra :
    Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

/-- The actual source marking alternatives remove the deleted branch
whenever the point centralizer has the indicated A₇ component. The source
choice establishing quotient irreducibility is retained explicitly. -/
theorem source_a5_point_seven_forces_natural
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    {t v : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hv : v ∈ ⁅D.fullModule,L⁆) (hvne : v ≠ 1)
    (I : Subgroup G) (hKI : L.map (MulAut.conj t).toMonoidHom ≤ I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (eI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) :
    ∃ f : alternatingGroup (Fin 5) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty (Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
        (sourceMovedFixed D)
        (Representation.SL2.BinarySmall.natural.comp
          (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) := by
  rcases source_a5_original_module_alternatives_of_irreducible D e hi with h | ⟨_,f,⟨c⟩⟩
  · exact h
  · exact (source_a5_deleted_point_component_not_seven D (e.trans f) c ht htn
      hv hvne I hKI hIX hI hNI ⟨eI⟩).elim
end CFSG.Quasithin.Chapter10
