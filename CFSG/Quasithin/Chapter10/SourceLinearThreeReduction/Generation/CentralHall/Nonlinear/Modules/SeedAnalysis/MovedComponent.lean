module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.HermitianKernel
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.FullSemisimple

/-!
# The original moved component before constituent selection

The literal component action on W = [V_M,L] has kernel O2(L), by the
already faithful action on its central quotient. Thus both the component
marking and its normalizer action descend to the faithful full stabilizer
image without a chosen natural or Hermitian constituent. The marking keeps
its exact formula on the original component projection.

In either separated seed orientation, the kernel is the component
centralizer and its order is prime to every odd component prime. If five
divides the binary component order, the kernel is solvable and three-free.
D.3.9 therefore makes every starred cubic actor faithful on the component.
The constituent construction and literal Hall application are in
EvenConstituent. Source: Aschbacher--Smith D.3.9, D.3.21 and10.1.3,
printed pp.199--207,742.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
private theorem component_le_stabilizer : L ≤ D.maximalLocal ⊓ normalizer (L : Set G) :=
  le_inf ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) L.le_normalizer
local instance : (movedStabilizerComponent D).Normal :=
  (normal_subgroupOf_iff_le_normalizer (component_le_stabilizer D)).mpr inf_le_right
variable {F : Type*} [Field F]

/-- The original component action has exactly the marked two-core kernel. -/
theorem movedStabilizerComponent_kernel
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    ((actionHom (movedStabilizerAction D)).comp (movedStabilizerComponent D).subtype).ker =
      (movedNaturalComponentProjection D e).ker := by
  ext l
  constructor
  · intro hl
    let lL : L := ⟨l.val.val,l.property⟩
    have hfix := (actionHom_eq_one_iff (movedStabilizerAction D) l.val).mp hl
    have htriv : movedQuotientAction D hn (QuotientGroup.mk' (pCore 2 L) lL) = 1 := by
      apply LinearMap.ext
      intro v
      obtain ⟨w,hw⟩ := (movedQuotientSection D hn).onto (Multiplicative.ofAdd v)
      have he := (movedQuotientSection D hn).equivariant lL w
      have hh : (⟨(lL:G) * (w:G) * (lL:G)⁻¹,
          (mem_normalizer_iff.mp ((movedQuotientSection D hn).normalized lL.property) w).mp w.property⟩ :
          (⁅D.fullModule,L⁆ : Subgroup G)) = w := by
        exact congrArg Additive.toMul (hfix (Additive.ofMul w))
      rw [hh,hw] at he
      exact he.symm
    change e (QuotientGroup.mk' (pCore 2 L) lL) = 1
    rw [show QuotientGroup.mk' (pCore 2 L) lL = 1 from
      movedQuotientAction_faithful D hn (htriv.trans (movedQuotientAction D hn).map_one.symm),map_one]
  · intro hl
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

/-- The whole-module kernel acts trivially on the original component quotient. -/
theorem movedStabilizer_automorphism_kernel
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    (actionHom (movedStabilizerAction D)).ker ≤ (movedNaturalQuotientAction D e).ker := by
  let ρ := movedStabilizerAction D
  let K := movedStabilizerComponent D
  let q := movedNaturalComponentProjection D e
  intro a ha
  have hk := (movedStabilizerComponent_kernel D hn e).le
  have hc (k : K) : q (MulAut.conjNormal a k) = q k := by
    have hmem : (MulAut.conjNormal a k) * k⁻¹ ∈ ((actionHom ρ).comp K.subtype).ker := by
      change actionHom ρ (a * (k : _) * a⁻¹ * (k : _)⁻¹) = 1
      simp only [map_mul,Subgroup.coe_inv,map_inv,show actionHom ρ a = 1 from ha,inv_one,one_mul,mul_one,mul_inv_cancel]
    have hh : q ((MulAut.conjNormal a k) * k⁻¹) = 1 := hk hmem
    simpa only [map_mul,map_inv,mul_inv_eq_one] using hh
  apply DFunLike.ext
  intro g
  obtain ⟨k,rfl⟩ := movedNaturalComponentProjection_surjective D e g
  exact (movedNaturalComponentProjection_conj D e a k).symm.trans (hc k)

/-- Conjugation on the marked component quotient through the faithful moved image. -/
@[expose] def movedImageQuotientAction
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    actionImage (movedStabilizerAction D) →* MulAut (SL(2,F)) :=
  (actionHom (movedStabilizerAction D)).liftOfSurjective
    (movedStabilizerAction D).asGroupHom.rangeRestrict_surjective
    ⟨movedNaturalQuotientAction D e,movedStabilizer_automorphism_kernel D hn e⟩

/-- The descended action agrees with original normalizer conjugation. -/
theorem movedImageQuotientAction_apply
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (g : ↥(D.maximalLocal ⊓ normalizer (L : Set G))) :
    movedImageQuotientAction D hn e (actionHom (movedStabilizerAction D) g) =
      movedNaturalQuotientAction D e g :=
  (actionHom (movedStabilizerAction D)).liftOfRightInverse_comp_apply _ _ _ g

/-- The original component quotient identifies its image and its exact centralizer. -/
theorem movedImage_component_and_centralizer
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    Nonempty ((L ⧸ pCore 2 L) ≃* movedStabilizerComponentImage D) ∧
      (movedImageQuotientAction D hn e).ker =
        centralizer (movedStabilizerComponentImage D : Set (actionImage (movedStabilizerAction D))) := by
  obtain ⟨⟨eS⟩,hc⟩ := marked_image_component_and_centralizer
    (movedStabilizerAction D) (movedStabilizerComponent D)
    (movedNaturalComponentProjection D e) (movedNaturalComponentProjection_surjective D e)
    (movedImageQuotientAction D hn e)
    (fun g k => by rw [movedImageQuotientAction_apply]; exact movedNaturalComponentProjection_conj D e g k)
    (movedStabilizerComponent_kernel D hn e)
  exact ⟨⟨e.trans eS.symm⟩,hc⟩


/-- The component image marking before any constituent is selected. -/
@[expose] def movedImageComponentProjection
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    movedStabilizerComponentImage D →* SL(2,F) :=
  let f := ((actionHom (movedStabilizerAction D)).comp
    (movedStabilizerComponent D).subtype).rangeRestrict
  f.liftOfSurjective (MonoidHom.rangeRestrict_surjective _) ⟨movedNaturalComponentProjection D e,by
    intro k hk
    apply (movedStabilizerComponent_kernel D hn e).le
    exact congrArg (fun x : movedStabilizerComponentImage D => (x : actionImage (movedStabilizerAction D))) hk⟩

/-- The component marking retains the literal original projection. -/
theorem movedImageComponentProjection_apply
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (k : movedStabilizerComponent D) :
    movedImageComponentProjection D hn e
      (((actionHom (movedStabilizerAction D)).comp (movedStabilizerComponent D).subtype).rangeRestrict k) =
      movedNaturalComponentProjection D e k :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k

/-- The component projection on the faithful image is an isomorphism. -/
theorem movedImageComponentProjection_bijective
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    Function.Bijective (movedImageComponentProjection D hn e) := by
  let f := ((actionHom (movedStabilizerAction D)).comp
    (movedStabilizerComponent D).subtype).rangeRestrict
  constructor
  · apply (injective_iff_map_eq_one _).mpr
    intro b hb
    obtain ⟨k,rfl⟩ := MonoidHom.rangeRestrict_surjective _ b
    apply Subtype.ext
    exact (movedStabilizerComponent_kernel D hn e).ge
      ((movedImageComponentProjection_apply D hn e k).symm.trans hb)
  · intro g
    obtain ⟨k,rfl⟩ := movedNaturalComponentProjection_surjective D e g
    exact ⟨f k,movedImageComponentProjection_apply D hn e k⟩

/-- The exact marked component isomorphism, before constituent selection. -/
@[expose] def movedImageComponentEquiv
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) : movedStabilizerComponentImage D ≃* SL(2,F) :=
  MulEquiv.ofBijective (movedImageComponentProjection D hn e)
    (movedImageComponentProjection_bijective D hn e)

variable [Finite F] [CharP F 2]

/-- Original odd-rank bounds exclude each odd component prime from the kernel. -/
theorem movedImageQuotientAction_ker_card_coprime
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) :
    Nat.Coprime p (Nat.card (movedImageQuotientAction D c.nonnormal e).ker) := by
  let N := D.maximalLocal ⊓ normalizer (L : Set G)
  let R := (localOrbit T L).subgroupOf N
  let ρ := movedStabilizerAction D
  let f := actionHom ρ
  let α := movedImageQuotientAction D c.nonnormal e
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
      rw [←movedImageQuotientAction_apply D c.nonnormal e]
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

/-- A five-divisible even-linear component has no starred actor kernel; no constituent is assumed. -/
theorem even_starred_actor_faithful
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (h5 : 5 ∣ Nat.card (L ⧸ pCore 2 L))
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D))) :
    Function.Injective ((movedImageQuotientAction D c.nonnormal e).comp A.subtype) := by
  classical
  let ρ := movedStabilizerAction D
  let σ := imageRepresentation ρ
  let α := movedImageQuotientAction D c.nonnormal e
  let S := movedStabilizerComponentImage D
  let : FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) :=
    Module.Finite.of_finite
  obtain ⟨⟨eS⟩,hC⟩ := movedImage_component_and_centralizer D c.nonnormal e
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
  have h3 : Nat.Coprime 3 (Nat.card α.ker) := by
    apply movedImageQuotientAction_ker_card_coprime D c ht htn hsep e 3 (by decide)
    rw [Nat.card_congr e.toEquiv]
    exact Theory.SpecificGroups.three_dvd_card_sl_two _
  have hc5 : Nat.Coprime 5 (Nat.card α.ker) := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact movedImageQuotientAction_ker_card_coprime D c ht htn hsep e 5 (by decide) h5
  have hsol := KnownSimple.isSolvable_of_coprime_three_five _
    ((movedStabilizerImage_isKGroup D).subgroup α.ker) h3 hc5
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

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
