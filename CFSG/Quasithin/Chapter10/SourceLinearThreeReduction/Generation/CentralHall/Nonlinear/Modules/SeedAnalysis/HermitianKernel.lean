module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.HermitianMultiplicity
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalPrime
public import Theory.Representation.MarkedImageCentralizer

/-!
# Removing the Hermitian actor-kernel alternative

The original orbit index is prime to both three and five in the Hermitian
row. The literal component-action kernel is therefore solvable and three-free.
If a starred cubic actor met it nontrivially, D.3.9's component-centralizer
argument would produce a nontrivial three-subgroup or a nonsolvable component
inside it. Both alternatives are impossible. Thus a starred actor is faithful
on the original quotient, and the two-section budget proves moved minimality.
The final theorems reconstruct both separated seed orientations and apply to
the literal central Hall subgroup. Separation and constituent construction
remain with qt-d-10-nona5-central-hall-orders, as does final source assembly.
Source: Aschbacher--Smith D.3.9, D.3.21 and10.1.3, pp.199--207,742.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 Representation.BinaryOffender
open Representation.OrthogonalFourMinus.FiniteModel
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
private theorem component_le_stabilizer : L ≤ D.maximalLocal ⊓ normalizer (L : Set G) :=
  le_inf ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) L.le_normalizer
local instance : (movedStabilizerComponent D).Normal :=
  (normal_subgroupOf_iff_le_normalizer (component_le_stabilizer D)).mpr inf_le_right
variable (s : ℕ) [NeZero s]
local instance : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- The Hermitian constituent marks the actual component image and its exact centralizer. -/
theorem movedHermitianImage_component_and_centralizer
    (e : (L ⧸ pCore 2 L) ≃* SL(2,Field s))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (SL2.BinarySmall.hermitian s (movedNaturalComponentProjection D e l) v) =
        I.toRepresentation l (E v)) :
    Nonempty ((L ⧸ pCore 2 L) ≃* movedStabilizerComponentImage D) ∧
      (movedHermitianImageQuotientAction D s e I E hE).ker =
        centralizer (movedStabilizerComponentImage D : Set (actionImage (movedStabilizerAction D))) := by
  have hk : (movedNaturalComponentProjection D e).ker ≤
      ((actionHom (movedStabilizerAction D)).comp (movedStabilizerComponent D).subtype).ker := by
    intro l hl
    have hlcore : (⟨l.val.val,l.property⟩ : L) ∈ pCore 2 L := by
      apply (QuotientGroup.eq_one_iff _).mp
      apply e.map_eq_one_iff.mp
      exact hl
    apply (actionHom_eq_one_iff (movedStabilizerAction D) l).mpr
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l.val : G) * (w.toMul : G) * (l.val : G)⁻¹ = (w.toMul : G)
    have hc := mem_centralizer_iff.mp (source_component_core_centralizes_fullModule D
      (mem_map_of_mem L.subtype hlcore)) w.toMul (moved_le_fullModule D w.toMul.property)
    change (w.toMul : G) * (l.val : G) = (l.val : G) * (w.toMul : G) at hc
    rw [←hc,mul_inv_cancel_right]
  have hker := SL2Hermitian.hermitian_constituent_detects_component_kernel s
    (movedStabilizerAction D) (movedStabilizerComponent D)
    (movedNaturalComponentProjection D e) I E hE
  obtain ⟨⟨eS⟩,hc⟩ := marked_image_component_and_centralizer
    (movedStabilizerAction D) (movedStabilizerComponent D)
    (movedNaturalComponentProjection D e) (movedNaturalComponentProjection_surjective D e)
    (movedHermitianImageQuotientAction D s e I E hE)
    (fun g k => by
      rw [movedHermitianImageQuotientAction_apply]
      exact movedNaturalComponentProjection_conj D e g k)
    (le_antisymm hker hk)
  exact ⟨⟨e.trans eS.symm⟩,hc⟩

/-- The original odd-rank restriction applies to the literal Hermitian quotient kernel. -/
theorem hermitianImageQuotientAction_ker_card_coprime
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,Field s))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (SL2.BinarySmall.hermitian s (movedNaturalComponentProjection D e l) v) =
        I.toRepresentation l (E v))
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) :
    Nat.Coprime p (Nat.card (movedHermitianImageQuotientAction D s e I E hE).ker) := by
  let N := D.maximalLocal ⊓ normalizer (L : Set G)
  let R := (localOrbit T L).subgroupOf N
  let ρ := movedStabilizerAction D
  let f := actionHom ρ
  let α := movedHermitianImageQuotientAction D s e I E hE
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
      rw [←movedHermitianImageQuotientAction_apply D s e I E hE]
      exact ha
    have hb' : MulAut.conj (e (QuotientGroup.mk' (pCore 2 L) lL)) = 1 := by
      apply DFunLike.ext
      intro x
      obtain ⟨k,rfl⟩ := movedNaturalComponentProjection_surjective D e x
      have he := movedNaturalComponentProjection_conj D e l k
      rw [hb] at he
      let lK : movedStabilizerComponent D := ⟨l,hl⟩
      change movedNaturalComponentProjection D e (lK*k*lK⁻¹) =
        movedNaturalComponentProjection D e k at he
      change movedNaturalComponentProjection D e lK * movedNaturalComponentProjection D e k *
        (movedNaturalComponentProjection D e lK)⁻¹ = movedNaturalComponentProjection D e k
      simpa only [map_mul,map_inv] using he
    have hz : e (QuotientGroup.mk' (pCore 2 L) lL) = 1 :=
      (MulAut.conj_injective_of_center_eq_bot (Theory.PSL2.sl2_center_eq_bot (Field s)))
        (hb'.trans (map_one (MulAut.conj : SL(2,Field s) →* MulAut (SL(2,Field s)))).symm)
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
/-- Both forbidden odd primes divide the original Hermitian component, so its
literal quotient-action kernel is three-free and solvable. -/
theorem hermitianImageQuotientAction_kernel_solvable
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,Field s))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (SL2.BinarySmall.hermitian s (movedNaturalComponentProjection D e l) v) =
        I.toRepresentation l (E v)) :
    Nat.Coprime 3 (Nat.card (movedHermitianImageQuotientAction D s e I E hE).ker) ∧
      Group.IsSolvable (movedHermitianImageQuotientAction D s e I E hE).ker := by
  let α := movedHermitianImageQuotientAction D s e I E hE
  have h3 : Nat.Coprime 3 (Nat.card α.ker) := by
    apply hermitianImageQuotientAction_ker_card_coprime D s c ht htn hsep e I E hE 3 (by decide)
    rw [Nat.card_congr e.toEquiv]
    exact Theory.SpecificGroups.three_dvd_card_sl_two _
  have h5 : Nat.Coprime 5 (Nat.card α.ker) := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    apply hermitianImageQuotientAction_ker_card_coprime D s c ht htn hsep e I E hE 5 (by decide)
    rw [Nat.card_congr e.toEquiv,Atlas.card_sl_two]
    change 5 ∣ Nat.card (GaloisField 2 (2*s)) * (Nat.card (GaloisField 2 (2*s)) ^ 2 - 1)
    rw [GaloisField.card 2 (2*s) (by have := NeZero.ne s; omega)]
    apply dvd_mul_of_dvd_right
    have hpow : (2 ^ (2*s)) ^ 2 = 16 ^ s := by
      rw [←pow_mul,show (2*s)*2 = 4*s by omega,pow_mul]
      rfl
    rw [hpow]
    exact dvd_trans (by decide : 5 ∣ 16 - 1)
      (by simpa using Nat.sub_dvd_pow_sub_pow 16 1 s)
  exact ⟨h3,KnownSimple.isSolvable_of_coprime_three_five _
    ((movedStabilizerImage_isKGroup D).subgroup α.ker) h3 h5⟩

/-- Every original starred cubic actor is faithful on the Hermitian component
quotient; its possible kernel has now been excluded by the ambient odd-rank bound. -/
theorem hermitian_starred_actor_faithful
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,Field s))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (SL2.BinarySmall.hermitian s (movedNaturalComponentProjection D e l) v) =
        I.toRepresentation l (E v))
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D))) :
    Function.Injective ((movedHermitianImageQuotientAction D s e I E hE).comp A.subtype) := by
  classical
  let ρ := movedStabilizerAction D
  let σ := imageRepresentation ρ
  let α := movedHermitianImageQuotientAction D s e I E hE
  let S := movedStabilizerComponentImage D
  let : FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) :=
    Module.Finite.of_finite
  obtain ⟨⟨eS⟩,hC⟩ := movedHermitianImage_component_and_centralizer D s e I E hE
  let := D.quasisimple
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv eS
  let : ρ.IsIrreducible := movedStabilizerAction_irreducible D c ht htn hsep
  have hi : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective σ).mp
      (inferInstance : ρ.IsIrreducible)
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_simple D c.nonnormal
  let : Nontrivial S := eS.injective.nontrivial
  have hSn : S ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot S).mp inferInstance
  have hfull := subspaceCommutator_top_eq_top_of_normal_faithful_irreducible σ
    (imageRepresentation_injective ρ) hi S hSn
  have hcore := movedStabilizerImage_twoCore_eq_bot D c ht htn hsep
  obtain ⟨h3,hsol⟩ := hermitianImageQuotientAction_kernel_solvable D s c ht htn hsep e I E hE
  let := hsol
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  apply Subtype.ext
  by_contra hne
  have hAn : A ⊓ centralizer (S : Set (actionImage ρ)) ≠ ⊥ := by
    intro hz
    have hm : a.val ∈ A ⊓ centralizer (S : Set (actionImage ρ)) := ⟨a.property,hC ▸ ha⟩
    exact hne (mem_bot.mp (hz ▸ hm))
  obtain ⟨X,hXC,_,hXn,_,hcase⟩ :=
    ChosenSource325.exists_starred_moved_subgroup_in_component_centralizer σ
      (imageRepresentation_injective ρ) S hcore hfull hA hAn
  rcases hcase with ⟨_,hXp⟩ | ⟨J,hJ,hJC,_⟩
  · have hXK : X ≤ α.ker := hXC.trans hC.symm.le
    have hcX : Nat.Coprime 3 (Nat.card X) := h3.of_dvd_right (card_dvd_of_le hXK)
    obtain ⟨k,hk⟩ := hXp.exists_card_eq
    apply hXn
    apply Subgroup.card_eq_one.mp
    rw [hk] at hcX ⊢
    exact Nat.eq_one_of_dvd_coprimes (hcX.pow_left k) dvd_rfl dvd_rfl
  · have hJK : J ≤ α.ker := hJC.trans hC.symm.le
    exact hJ.isCComponent.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective (f := inclusion hJK) (inclusion_injective hJK))

/-- A Hermitian constituent makes the original moved module minimal, with no
actor-faithfulness or multiplicity premise. -/
theorem movedMinimal_of_hermitian_constituent
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (hs : 1 < s)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,Field s))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (SL2.BinarySmall.hermitian s (movedNaturalComponentProjection D e l) v) =
        I.toRepresentation l (E v)) : MovedMinimal D := by
  have hc := movedStabilizerAction_cubic_bound D c ht htn hsep
  obtain ⟨A,hA⟩ := (ChapterD.QhatStar_nonempty_iff _).mpr hc
  exact movedMinimal_of_hermitian_faithful_image_actor D s c ht htn hsep hs e I hI E hE
    A hA.1.2.1 (hermitian_starred_actor_faithful D s c ht htn hsep e I E hE A hA)
    ((actionRatio_le_nat_iff _ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hc))

/-- Reconstruct all original seed clauses in either separated Hermitian orientation. -/
theorem separatedSeed_of_hermitian_constituent
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (hs : 1 < s)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,Field s))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (SL2.BinarySmall.hermitian s (movedNaturalComponentProjection D e l) v) =
        I.toRepresentation l (E v)) : SeparatedSeed D t :=
  separatedSeed_of_separated_and_movedMinimal D
    (movedMinimal_of_hermitian_constituent D s c ht htn hsep hs e I hI E hE)
    ht htn hsep

/-- The actual Hall exponent follows from the original separated Hermitian
constituent. All actor-kernel and multiplicity obligations are discharged. -/
theorem hall_exponent_of_hermitian_constituent
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    (hs : 1 < s)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,Field s))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (SL2.BinarySmall.hermitian s (movedNaturalComponentProjection D e l) v) =
        I.toRepresentation l (E v)) : ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2 ^ n + 1 :=
  hall_exponent_of_moved_minimal_and_crossed T D c hnot ht htn
    (movedMinimal_of_hermitian_constituent D s c ht htn hsep hs e I hI E hE)
    (full_moved_centralizes_opposite_of_seed_separated D ht htn hsep)

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
