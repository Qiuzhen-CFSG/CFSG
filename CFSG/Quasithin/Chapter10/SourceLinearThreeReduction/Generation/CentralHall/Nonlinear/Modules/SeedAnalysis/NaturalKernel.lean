module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalDegree
public import Theory.SpecificGroups.FFLinearPrimeCore

/-!
# The kernel of the original natural component action

Let N = N_M(L) act on the unchanged moved subgroup W. Its faithful image
has trivial two-core by original minimality. The opposite component fixes W,
so the image of L₀ is exactly the image of L. The latter meets the kernel of
the marked SL₂ automorphism action trivially: inner automorphisms are faithful
and the original component two-core fixes W. Thus the kernel order divides
[M:L₀], which is prime to every odd prime dividing the component order.

The literal source application combines these conclusions with the natural
degree argument: a starred cubic actor contains a nonidentity involution in
this three-free kernel. This isolates the remaining component-centralizer
branch of D.3.9; separation and that branch's exclusion are still owned by
qt-d-10-nona5-central-hall-orders. No source classification is asserted here.
Source: Aschbacher--Smith D.3.9(2), D.3.21(3), and 10.1.3,
printed pp.200--201,205--206,742.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
private theorem component_le_stabilizer : L ≤ D.maximalLocal ⊓ normalizer (L : Set G) :=
  le_inf ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) L.le_normalizer

/-- Original full-module minimality kills the two-core of the full stabilizer image. -/
theorem movedStabilizerImage_twoCore_eq_bot
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) :
    pCore 2 (actionImage (movedStabilizerAction D)) = ⊥ := by
  let ρ := movedStabilizerAction D
  let σ := imageRepresentation ρ
  let : ρ.IsIrreducible := movedStabilizerAction_irreducible D c ht htn hsep
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective σ).mp
      (inferInstance : ρ.IsIrreducible)
  have hk := normal_p_subgroup_le_ker σ (pCore 2 (actionImage ρ)) pCore_isPGroup
  exact bot_unique (hk.trans (σ.ker_eq_bot_iff.mpr (imageRepresentation_injective ρ)).le)

/-- The kernel on the marked component quotient also has trivial two-core. -/
theorem naturalImageQuotientAction_ker_twoCore_eq_bot
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v)) :
    pCore 2 (movedNaturalImageQuotientAction D e I E hE).ker = ⊥ := by
  let K := (movedNaturalImageQuotientAction D e I E hE).ker
  have hm : (pCore 2 K).map K.subtype ≤ pCore 2 (actionImage (movedStabilizerAction D)) :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map K.subtype⟩
  rw [movedStabilizerImage_twoCore_eq_bot D c ht htn hsep] at hm
  exact ((pCore 2 K).map_eq_bot_iff_of_injective K.subtype_injective).mp (bot_unique hm)

omit [Finite F] [CharP F 2] in
private theorem quotientAction_component
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (l : L) :
    movedNaturalQuotientAction D e ⟨l,component_le_stabilizer D l.property⟩ =
      MulAut.conj (e (QuotientGroup.mk' (pCore 2 L) l)) := by
  apply DFunLike.ext
  intro x
  obtain ⟨k,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) x
  change e (normalizerPCoreQuotientAction L _ (e.symm (e _))) = _
  rw [e.symm_apply_apply]
  change e (quotientAut (pCore 2 L) _ _) = _
  rw [quotientAut_apply_mk]
  change e (QuotientGroup.mk' (pCore 2 L) (l*k*l⁻¹)) = _
  simp only [map_mul,map_inv,MulAut.conj_apply,Function.comp_apply]

/-- The actual quotient-action kernel inherits the original odd-rank index
restriction, without a two-group assumption on the normalizer quotient. -/
theorem naturalImageQuotientAction_ker_card_coprime
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) :
    Nat.Coprime p (Nat.card (movedNaturalImageQuotientAction D e I E hE).ker) := by
  let N := D.maximalLocal ⊓ normalizer (L : Set G)
  let R := (localOrbit T L).subgroupOf N
  let ρ := movedStabilizerAction D
  let f := actionHom ρ
  let α := movedNaturalImageQuotientAction D e I E hE
  let S := (L.subgroupOf N).map f
  have hLN : L ≤ N := component_le_stabilizer D
  have hRN : localOrbit T L ≤ N := le_inf (localOrbit T L).le_normalizer
    (source_nonnormal_orbit_le_normalizer D c.nonnormal)
  let : (L.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hLN).mpr inf_le_right
  let : S.Normal := Normal.map inferInstance f ρ.asGroupHom.rangeRestrict_surjective
  have hpair : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 c.nonnormal)
      inf_le_right ht htn
  have hLtN : L.map (MulAut.conj t).toMonoidHom ≤ N :=
    (le_sup_right.trans hpair.symm.le).trans hRN
  have hkill : (L.map (MulAut.conj t).toMonoidHom).subgroupOf N ≤ f.ker := by
    intro l hl
    apply (actionHom_eq_one_iff ρ l).mpr
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G) * (w.toMul : G) * (l : G)⁻¹ = (w.toMul : G)
    have hc := mem_centralizer_iff.mp
      (full_moved_centralizes_opposite_of_seed_separated D ht htn hsep w.toMul.property) l hl
    rw [hc,mul_assoc,mul_inv_cancel,mul_one]
  have hRS : R.map f = S := by
    change ((localOrbit T L).subgroupOf N).map f = _
    rw [hpair,subgroupOf_sup hLN hLtN,Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff (f := f) _).mpr hkill,sup_bot_eq]
  have hdis : S ⊓ α.ker = ⊥ := by
    apply bot_unique
    rintro a ⟨⟨l,hl,rfl⟩,ha⟩
    let lL : L := ⟨l,hl⟩
    have hb : movedNaturalQuotientAction D e l = 1 := by
      rw [←movedNaturalImageQuotientAction_apply D e I E hE]
      exact ha
    have hb' : MulAut.conj (e (QuotientGroup.mk' (pCore 2 L) lL)) = 1 := by
      rw [←quotientAction_component D e lL]
      exact hb
    have hz : e (QuotientGroup.mk' (pCore 2 L) lL) = 1 :=
      (MulAut.conj_injective_of_center_eq_bot (Theory.PSL2.sl2_center_eq_bot F))
        (hb'.trans (map_one (MulAut.conj : SL(2,F) →* MulAut (SL(2,F)))).symm)
    have hlcore : lL ∈ pCore 2 L := (QuotientGroup.eq_one_iff _).mp (e.map_eq_one_iff.mp hz)
    apply (actionHom_eq_one_iff ρ l).mpr
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G) * (w.toMul : G) * (l : G)⁻¹ = (w.toMul : G)
    have hc := mem_centralizer_iff.mp (source_component_core_centralizes_fullModule D
      (mem_map_of_mem L.subtype hlcore)) w.toMul (moved_le_fullModule D w.toMul.property)
    change (w.toMul : G) * (l : G) = (l : G) * (w.toMul : G) at hc
    rw [←hc,mul_inv_cancel_right]
  have hc : Nat.card α.ker ∣ S.index := by
    have hh := S.relIndex_dvd_index_of_normal α.ker
    rwa [←inf_relIndex_right,hdis,relIndex_bot_left] at hh
  have hindex : R.index ∣ ((localOrbit T L).subgroupOf D.maximalLocal).index := by
    change (localOrbit T L).relIndex N ∣ _
    rw [←relIndex_subgroupOf (H := localOrbit T L) (L := D.maximalLocal) inf_le_left]
    exact relIndex_dvd_index_of_le (subgroupOf_mono D.maximalLocal hRN)
  have hS : S.index ∣ ((localOrbit T L).subgroupOf D.maximalLocal).index := by
    rw [←hRS]
    exact (R.index_map_dvd ρ.asGroupHom.rangeRestrict_surjective).trans hindex
  exact (HallGeometry.hall_component_orbit_index_coprime D c.nonnormal e p hp hd).of_dvd_right
    (hc.trans hS)

local instance (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2

omit [Field F] [Finite F] [CharP F 2] in
/-- The original separated natural branch supplies a starred actor whose
component kernel contains an involution, has trivial two-core and is three-free.
These are inputs to the remaining D.3.9 component-centralizer analysis. -/
theorem source_natural_starred_actor_kernel
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → GaloisField 2 n) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v)) :
    let α := movedNaturalImageQuotientAction D e I E hE
    pCore 2 α.ker = ⊥ ∧ Nat.Coprime 3 (Nat.card α.ker) ∧
      ∃ A : Subgroup (actionImage (movedStabilizerAction D)),
        A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)) ∧
        ∃ a : actionImage (movedStabilizerAction D), a ∈ A ∧ a ≠ 1 ∧ a ^ 2 = 1 ∧ α a = 1 := by
  dsimp only
  refine ⟨naturalImageQuotientAction_ker_twoCore_eq_bot D c ht htn hsep e I E hE,
    naturalImageQuotientAction_ker_card_coprime D c ht htn hsep e I E hE 3 (by decide) ?_,?_⟩
  · rw [Nat.card_congr e.toEquiv]
    exact Theory.SpecificGroups.three_dvd_card_sl_two _
  · have hc := movedStabilizerAction_cubic_bound D c ht htn hsep
    obtain ⟨A,hA⟩ := (ChapterD.QhatStar_nonempty_iff _).mpr hc
    refine ⟨A,hA,natural_budget_actor_has_quotient_kernel_involution
      D c ht htn hsep n hn e I hI E hE A hA.1.2.1 ?_⟩
    exact (actionRatio_le_nat_iff _ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hc)

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
