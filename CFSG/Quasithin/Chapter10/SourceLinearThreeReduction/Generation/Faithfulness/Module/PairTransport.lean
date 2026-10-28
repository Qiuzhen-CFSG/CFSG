module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.PairImage
public import Theory.GroupAction.EquivariantCommutant

/-!
# Transporting the original first moved commutant to its Sylow partner

Conjugation by M acts on the original full central quotient and carries each
moved-factor image to the conjugate image. Restricting both actors and spaces
gives an equivariant isomorphism and hence identifies their full commutants.
The original Sylow pair therefore needs just one commutant-order bound; its
product-image bound uses twice the exponent. The final application fixes the
literal odd Hall kernel on the original full module.

Source: Aschbacher--Smith, 10.1.1 and 10.2.3(2), printed pp.741,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Original M-conjugation carries each moved image onto the conjugate moved image. -/
theorem source_moved_quotient_conjugate (m : D.maximalLocal) (K : Subgroup G) :
    (sourceMovedQuotient D K).map (sourceFullModuleQuotientAction D m).toMonoidHom =
      sourceMovedQuotient D (K.map (MulAut.conj (m : G)).toMonoidHom) := by
  have hv : D.fullModule.map (MulAut.conj (m : G)).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule m.property)
  have hw : (⁅D.fullModule,K⁆).map (MulAut.conj (m : G)).toMonoidHom =
      ⁅D.fullModule,K.map (MulAut.conj (m : G)).toMonoidHom⁆ := by
    rw [map_commutator,hv]
  simp only [sourceMovedQuotient_eq]
  apply le_antisymm
  · rintro y ⟨x,⟨v,hv',rfl⟩,rfl⟩
    change sourceFullModuleQuotientAction D m (QuotientGroup.mk' D.fullCentralizer v) ∈ _
    rw [sourceFullModuleQuotientAction_apply]
    apply mem_map_of_mem
    change (m : G) * (v : G) * (m : G)⁻¹ ∈ ⁅D.fullModule,K.map _⁆
    rw [←hw]
    exact mem_map_of_mem (MulAut.conj (m : G)).toMonoidHom hv'
  · rintro y ⟨v,hv',rfl⟩
    change (v : G) ∈ ⁅D.fullModule,K.map _⁆ at hv'
    rw [←hw] at hv'
    obtain ⟨w,hw',he⟩ := hv'
    have hwV : w ∈ D.fullModule := by
      have h : (MulAut.conj (m : G)) w ∈ D.fullModule := he.symm ▸ v.property
      exact (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule m.property) w).mpr h
    refine ⟨QuotientGroup.mk' D.fullCentralizer ⟨w,hwV⟩,
      mem_map_of_mem _ hw',?_⟩
    change sourceFullModuleQuotientAction D m
      (QuotientGroup.mk' D.fullCentralizer ⟨w,hwV⟩) = _
    rw [sourceFullModuleQuotientAction_apply]
    exact congrArg (QuotientGroup.mk' D.fullCentralizer) (Subtype.ext he)

/-- The actual quotient action restricts to an equivalence of moved factors. -/
noncomputable def sourceMovedQuotientConj (m : D.maximalLocal) (K : Subgroup G) :
    sourceMovedQuotient D K ≃* sourceMovedQuotient D
      (K.map (MulAut.conj (m : G)).toMonoidHom) :=
  ((sourceFullModuleQuotientAction D m).subgroupMap _).trans
    (MulEquiv.subgroupCongr (source_moved_quotient_conjugate D m K))

/-- The moved-factor equivalence retains the literal full quotient action. -/
theorem sourceMovedQuotientConj_apply (m : D.maximalLocal) (K : Subgroup G)
    (v : sourceMovedQuotient D K) :
    (sourceMovedQuotientConj D m K v : D.fullCentralQuotient) =
      sourceFullModuleQuotientAction D m v := by rfl

private theorem actor_map (m : D.maximalLocal) (K : Subgroup G) :
    (K.subgroupOf D.maximalLocal).map (MulAut.conj m).toMonoidHom =
      (K.map (MulAut.conj (m : G)).toMonoidHom).subgroupOf D.maximalLocal := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact mem_map_of_mem (MulAut.conj (m : G)).toMonoidHom hy
  · intro hx
    obtain ⟨y,hy,he⟩ := hx
    change (m : G) * y * (m : G)⁻¹ = (x : G) at he
    have hyM : y ∈ D.maximalLocal := by
      apply (mem_normalizer_iff.mp (D.maximalLocal.le_normalizer m.property) y).mpr
      rw [he]
      exact x.property
    exact ⟨⟨y,hyM⟩,hy,Subtype.ext he⟩

private noncomputable def movedActorConj (m : D.maximalLocal) (K : Subgroup G) :
    K.subgroupOf D.maximalLocal ≃*
      (K.map (MulAut.conj (m : G)).toMonoidHom).subgroupOf D.maximalLocal :=
  ((MulAut.conj m).subgroupMap _).trans (MulEquiv.subgroupCongr (actor_map D m K))

private theorem moved_quotient_conj_equivariant (m : D.maximalLocal) (K : Subgroup G)
    (k : K.subgroupOf D.maximalLocal) (v : sourceMovedQuotient D K) :
    sourceMovedQuotientConj D m K (sourceMovedQuotientAction D K K K.le_normalizer k v) =
      sourceMovedQuotientAction D _ _ (K.map (MulAut.conj (m : G)).toMonoidHom).le_normalizer
        (movedActorConj D m K k) (sourceMovedQuotientConj D m K v) := by
  apply Subtype.ext
  change sourceFullModuleQuotientAction D m
      (sourceMovedQuotientAction D K K K.le_normalizer k v : D.fullCentralQuotient) = _
  simp only [sourceMovedQuotientAction_apply]
  change sourceFullModuleQuotientAction D m (sourceFullModuleQuotientAction D k.val v) =
    sourceFullModuleQuotientAction D (m * k.val * m⁻¹)
      (sourceFullModuleQuotientAction D m v)
  rw [map_mul,map_mul,map_inv]
  simp only [MulAut.mul_apply,MulAut.inv_apply_self]

/-- The paired commutants are isomorphic under the original conjugation. -/
noncomputable def sourceMovedQuotientCommutantConj (m : D.maximalLocal) (K : Subgroup G) :
    centralizer ((sourceMovedQuotientAction D K K K.le_normalizer).range :
      Set (MulAut (sourceMovedQuotient D K))) ≃*
    centralizer ((sourceMovedQuotientAction D
      (K.map (MulAut.conj (m : G)).toMonoidHom)
      (K.map (MulAut.conj (m : G)).toMonoidHom)
      (K.map (MulAut.conj (m : G)).toMonoidHom).le_normalizer).range :
        Set (MulAut (sourceMovedQuotient D (K.map (MulAut.conj (m : G)).toMonoidHom)))) :=
  actionCommutantEquiv _ _ (movedActorConj D m K) (sourceMovedQuotientConj D m K)
    (moved_quotient_conj_equivariant D m K)

/-- One marked commutant bound suffices: Sylow conjugation supplies the second,
and the product-image bound adds the two exponents. -/
theorem source_hall_kernel_fixes_of_first_moved_commutant
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (Y : Subgroup H) (hYM : Y ≤ D.maximalLocal.subgroupOf H)
    (hY : IsHallSubgroup oddPrimes (Y.subgroupOf (D.maximalLocal.subgroupOf H)))
    (n : ℕ)
    (hfirst : Nat.card (centralizer
      ((sourceMovedQuotientAction D L L L.le_normalizer).range :
        Set (MulAut (sourceMovedQuotient D L)))) ∣ Nat.card (L ⧸ pCore 2 L) ^ n) :
    Y.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (D.fullModule : Set G) := by
  obtain ⟨t,ht,_,hpair⟩ := source_nonnormal_moved_quotient_pair D hn
  apply source_hall_kernel_fixes_of_moved_commutants D hn Y hYM hY t ht hpair n n hfirst
  rw [← Nat.card_congr (sourceMovedQuotientCommutantConj D
    ⟨t,le_normalizer_componentOrbit L T ht⟩ L).toEquiv]
  exact hfirst

end CFSG.Quasithin.Chapter10
