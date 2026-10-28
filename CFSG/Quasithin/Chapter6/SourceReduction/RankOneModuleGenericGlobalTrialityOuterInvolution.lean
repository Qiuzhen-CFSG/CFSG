module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCompletionFusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityOuterTorus
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2OuterCentralizer
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2OuterInvolution
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2OuterCentralizer

/-!
# The original triality outer involution and its centralizer extension factor

The genuine triality torus pulls back to an odd Hall subgroup D of the
whole source Borel. Hall conjugacy gives T = S N_T(D). The explicit
root-coordinate calculation makes S intersect N_T(D) trivial, and the
actual cubic-field quotient action embeds N_T(D) into a cyclic field
automorphism group. Thus S<T constructs an involution t outside S
normalizing this same marked D, with field coefficient of order two.

For every t in this complement, C_T(t) = C_S(t) N_T(D), and its order is
|C_S(t)| [T:S]. The already proved quotient-action kernel gives [T:S]
dividing the original exponent n, hence less than 2^n. The selected outer
involution fixes a subfield of square-root order in the actual cubic field.
The Chapter 12 companion supplies the literal chosen-module application.

These are the splitting and centralizer-extension steps in F.4.37–38.
The root fixed-point bound, ambient Sylow placement and S=T remain to be
proved. Original uniqueness, exhaustive compatible comparison and ambient
recognition remain obligations of the generic-global assembly. No full-model
automorphism extension or odd-degree assumption is used here.

Source: Aschbacher–Smith F.4.29(2), F.4.37–38, pp.289,293–294,
and 5.3.3, p.659 (`refs/quasithin.pdf`). The internal imports reuse general
Hall/centralizer transport proofs from the same source family while retaining
their existing public boundaries.
-/

public noncomputable section
open Subgroup Subgroup.OddHall Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem model_torus_hall (P : Parameters) (hp : P.prime=2) :
    IsHallSubgroup oddPrimes ((torus P).subgroupOf (borel P)) := by
  apply OddHall.oddHall_of_normalized_sup (unipotent_isPGroup_binary P hp)
    (Nat.coprime_two_left.mpr (by
      rw [TorusCoordinates.card_torus P hp]
      exact TorusCoordinates.odd_torus_order P hp))
    ((torus_le_borel P).trans (borel_le_normalizer_unipotent P hp))
  apply SetLike.coe_injective
  rw [coe_mul_of_right_le_normalizer_left (unipotent P) (torus P)
    ((torus_le_borel P).trans (borel_le_normalizer_unipotent P hp))]
  exact (borel_eq_mul P hp).symm

/-- A compatible triality comparison supplies a Hall torus whose Sylow normalizer
complements the original source core. The comparison's whole overlap is retained. -/
theorem Preparation.triality_source_sylow_torus_split
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
    ∃ D : Subgroup G, D ≤ C ∧ IsHallSubgroup oddPrimes (D.subgroupOf C) ∧
      (∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ torus (binaryParameters m hm)) ∧
      Disjoint (sourceS L H) (normalizer (D : Set G)) ∧
      IsCyclic ((T : Subgroup G) ⊓ normalizer (D : Set G) : Subgroup G) ∧
      (T : Set G) = (sourceS L H : Set G) *
        ((T : Subgroup G) ⊓ normalizer (D : Set G) : Set G) := by
  let Q := binaryParameters m hm
  let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
  let hf := d.hypothesisF11 h hTH
  have hSC : sourceS L H ≤ C := le_sup_right
  let a : C ≃* borel Q :=
    (MulEquiv.subgroupCongr (ChapterF.Source.lemma_F_1_3_6 hf)).symm.trans e.middle
  obtain ⟨P,hP⟩ := hf.sylow_commonBorel
  have hPS : (P : Subgroup C) = (sourceS L H).subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hSC]
  let R := (unipotentSylow Q rfl).subtype
    (show unipotent Q ≤ borel Q from unipotent_le_borel Q)
  let : (R : Subgroup (borel Q)).Normal := unipotent_normal_in_borel Q rfl
  let := Sylow.unique_of_normal R (inferInstance : R.Normal)
  have hSR : ((sourceS L H).subgroupOf C).map a.toMonoidHom = ((unipotent Q).subgroupOf (borel Q)) := by
    rw [←hPS]
    exact congrArg Sylow.toSubgroup (Subsingleton.elim (P.mapSurjective a.surjective) R)
  let D₀ := ((torus Q).subgroupOf (borel Q)).map a.symm.toMonoidHom
  let D := D₀.map C.subtype
  have hDC : D ≤ C := map_subtype_le _
  have hD₀ : D.subgroupOf C = D₀ := comap_map_eq_self_of_injective C.subtype_injective _
  have hDa : (D.subgroupOf C).map a.toMonoidHom = ((torus Q).subgroupOf (borel Q)) := by
    rw [hD₀]
    have heq : a.toMonoidHom.comp a.symm.toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext a.apply_symm_apply
    rw [map_map,heq,map_id]
  have hHall : IsHallSubgroup oddPrimes (D.subgroupOf C) := by
    rw [hD₀]
    constructor
    · intro p hp
      apply (model_torus_hall Q rfl).p_in_pi_of_p_dvd_card p
      rwa [card_map_of_injective a.symm.injective] at hp
    · intro p hp
      apply (model_torus_hall Q rfl).p_in_pi_of_p_dvd_index p
      change p.val ∣ (((torus Q).subgroupOf (borel Q)).map a.symm.toMonoidHom).index at hp
      have hi : (((torus Q).subgroupOf (borel Q)).map a.symm.toMonoidHom).index =
          (((torus Q).subgroupOf (borel Q))).index :=
        index_map_equiv (H := ((torus Q).subgroupOf (borel Q))) a.symm
      exact hi ▸ hp
  have hm2 := d.triality_parameter_gt_one h hp m hm e
  have hdis : Disjoint (sourceS L H) (normalizer (D : Set G)) := by
    apply disjoint_def.mpr
    intro x hx hn
    let y : C := ⟨x,hSC hx⟩
    have hy : a y ∈ ((unipotent Q).subgroupOf (borel Q)) := hSR ▸ mem_map_of_mem a.toMonoidHom hx
    have hyn : y ∈ normalizer (D.subgroupOf C : Set C) := by
      rw [mem_normalizer_iff]
      intro z
      exact (mem_normalizer_iff.mp hn z.val)
    have han := (D.subgroupOf C).le_normalizer_map a.toMonoidHom
      (mem_map_of_mem a.toMonoidHom hyn)
    rw [hDa] at han
    have han' := (((torus Q).subgroupOf (borel Q))).le_normalizer_map
      (borel Q).subtype (mem_map_of_mem _ han)
    rw [map_subgroupOf_eq_of_le (show torus Q ≤ borel Q from torus_le_borel Q)] at han'
    have he : (a y).val=1 := TrialityOuterTorus.unipotent_torus_normalizer_trivial m hm hm2 _ hy han'
    have hey : y=1 := a.injective ((Subtype.ext he).trans a.map_one.symm)
    exact congrArg Subtype.val hey
  refine ⟨D,hDC,hHall,?_,hdis,?_,?_⟩
  · intro b
    let c : C := ⟨b.val,(ChapterF.Source.lemma_F_1_3_6 hf).le b.property⟩
    have hh : a c ∈ ((torus Q).subgroupOf (borel Q)) ↔ c ∈ D.subgroupOf C := by
      rw [←hDa]
      exact mem_map_iff_mem a.injective
    exact hh.symm
  · have hs := d.triality_local_structure h hTH hp m hm e
    exact d.cyclic_of_disjoint_sourceS h hTH (d.triality_sourceS_le_factors h hTH hp m hm (Or.inr ⟨e⟩)) hs.2.2.2.2.1
      inf_le_left (hdis.mono_right inf_le_right)
  · exact OddHall.normal_sylow_frattini C (sourceS L H) (T : Subgroup G) D
      hf.commonBorel_solvable (sourceS_le_sylow h.sylow_normalizes hTH)
      (source_common_borel_normalized h.sylow_normalizes hTH) P hP hDC hHall


/-- If the original source core is proper in T, the pulled-back Hall torus
constructs an actual involution of T outside S. -/
theorem Preparation.triality_exists_outer_involution
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hne : sourceS L H ≠ (T : Subgroup G)) :
    let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
    ∃ D : Subgroup G, D ≤ C ∧ IsHallSubgroup oddPrimes (D.subgroupOf C) ∧
      (∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ torus (binaryParameters m hm)) ∧
      ∃ eR : (residual H ⧸ pCore 2 (residual H)) ≃* Theory.PSL2.Group (ExtensionField (binaryParameters m hm)),
      ∃ t : T, orderOf t=2 ∧ t.val ∉ sourceS L H ∧
        t.val ∈ normalizer (D : Set G) ∧ orderOf (residualSylowFieldAction hTH eR t)=2 := by
  obtain ⟨D,hDC,hHall,hmark,hdis,_,hsplit⟩ := d.triality_source_sylow_torus_split h hTH hp m hm e
  let U := (T : Subgroup G) ⊓ normalizer (D : Set G)
  have hU : U ≠ ⊥ := by
    intro hu
    apply hne
    apply le_antisymm (sourceS_le_sylow h.sylow_normalizes hTH)
    intro t ht
    change t ∈ (T : Set G) at ht
    rw [hsplit] at ht
    obtain ⟨s,hs,u,hu',rfl⟩ := ht
    have hu1 : u=1 := mem_bot.mp (hu ▸ (show u ∈ U from hu'))
    change s ∈ sourceS L H at hs
    change s*u ∈ sourceS L H
    rw [hu1,mul_one]
    exact hs
  let : Nontrivial U := U.nontrivial_iff_ne_bot.mpr hU
  obtain ⟨k,hk⟩ := (T.isPGroup'.to_le (show U ≤ T from inf_le_left)).exists_card_eq
  have hkpos : 0<k := by
    have hh := Finite.one_lt_card (α := U)
    rw [hk] at hh
    by_contra hn
    have hz : k=0 := by omega
    simp [hz] at hh
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := U) 2
    (hk ▸ dvd_pow_self 2 (by omega))
  let t : T := ⟨u.val,u.property.1⟩
  have ht : orderOf t=2 := by
    exact ((Subgroup.orderOf_coe t).symm.trans (Subgroup.orderOf_coe u)).trans hu
  have htS : t.val ∉ sourceS L H := by
    intro htS
    have hu1 : u.val=1 := disjoint_def.mp hdis htS u.property.2
    have ho := hu
    rw [show u=1 from Subtype.ext hu1,orderOf_one] at ho
    omega
  have hs := d.triality_local_structure h hTH hp m hm e
  obtain ⟨b⟩ := hs.2.2.2.1
  let eR : (residual H ⧸ pCore 2 (residual H)) ≃* Theory.PSL2.Group (ExtensionField (binaryParameters m hm)) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans (localFactorArmsQuotientEquivPSL2 (binaryParameters m hm) rfl)
  refine ⟨D,hDC,hHall,hmark,eR,t,ht,htS,u.property.2,?_⟩
  apply orderOf_eq_prime
  · have ht2 : t^2=1 := (orderOf_eq_prime_iff.mp ht).1
    rw [←map_pow,ht2,map_one]
  · intro he
    apply htS
    have hh : t ∈ (residualSylowFieldAction hTH eR).ker := he
    rw [d.residual_sylow_field_kernel h hTH (d.triality_sourceS_le_factors h hTH hp m hm (Or.inr ⟨e⟩)) eR] at hh
    exact hh

private theorem triality_marked_torus_unique
    {T : Sylow 2 G} {L W H A B D E : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hE : E ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmarkD : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ torus (binaryParameters m hm))
    (hmarkE : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ E ↔ (e.middle b).val ∈ torus (binaryParameters m hm)) : D=E := by
  have hC := (ChapterF.Source.lemma_F_1_3_6 (d.hypothesisF11 h hTH)).ge
  apply le_antisymm
  · intro x hx
    exact (hmarkE ⟨x,hC (hD hx)⟩).mpr ((hmarkD ⟨x,hC (hD hx)⟩).mp hx)
  · intro x hx
    exact (hmarkD ⟨x,hC (hE hx)⟩).mpr ((hmarkE ⟨x,hC (hE hx)⟩).mp hx)

/-- The same marked torus gives the exact centralizer decomposition. Its cyclic
complement has order [T:S], dividing n and smaller than the base-field order. -/
theorem Preparation.triality_outer_torus_centralizer
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ torus (binaryParameters m hm))
    (t : T) (ht : t.val ∈ normalizer (D : Set G)) :
    let U := (T : Subgroup G) ⊓ normalizer (D : Set G)
    U ≤ centralizer ({t.val} : Set G) ∧
      ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Set G) =
        ((sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) : Set G) * (U : Set G) ∧
      Nat.card U = (sourceS L H).relIndex (T : Subgroup G) ∧
      Nat.card U ∣ n ∧ Nat.card U < 2^n ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) =
        Nat.card (sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) *
          (sourceS L H).relIndex (T : Subgroup G) := by
  obtain ⟨E,hE,_,hmarkE,hd,hcyc,hs⟩ := d.triality_source_sylow_torus_split h hTH hp m hm e
  have hDE : D=E := triality_marked_torus_unique d h hTH m hm e hD hE hmark hmarkE
  subst E
  have hST := sourceS_le_sylow h.sylow_normalizes hTH
  have hd' := hd.mono_right (show (T : Subgroup G) ⊓ normalizer (D : Set G) ≤
    normalizer (D : Set G) from inf_le_right)
  have hi := split_index hST inf_le_left hd' hs
  have hc := cyclic_centralizer hcyc t.val ⟨t.property,ht⟩
  have hn := d.triality_source_sylow_index_dvd h hTH hp m hm (Or.inr ⟨e⟩)
  refine ⟨hc,centralizer_split hST inf_le_left hs t.val hc,hi,hi ▸ hn,?_,
    split_centralizer_card hST inf_le_left hd' hs hcyc t.val ⟨t.property,ht⟩⟩
  rw [hi]
  exact (Nat.le_of_dvd (by have := h.exponent; omega : 0<n) hn).trans_lt Nat.lt_two_pow_self

/-- The actual outer involution retains its quotient field coefficient and
marked Hall torus. Its fixed field has square-root order, and its centralizer
in T has the exact extension factor [T:S], at most n. -/
theorem Preparation.triality_exists_outer_involution_centralizer
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hne : sourceS L H ≠ (T : Subgroup G)) :
    let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
    ∃ D : Subgroup G, D ≤ C ∧ IsHallSubgroup oddPrimes (D.subgroupOf C) ∧
      (∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ torus (binaryParameters m hm)) ∧
      ∃ eR : (residual H ⧸ pCore 2 (residual H)) ≃* Theory.PSL2.Group (ExtensionField (binaryParameters m hm)),
      ∃ t : T, orderOf t=2 ∧ t.val ∉ sourceS L H ∧
        t.val ∈ normalizer (D : Set G) ∧ orderOf (residualSylowFieldAction hTH eR t)=2 ∧
        Nat.card (FixedBy.subfield (ExtensionField (binaryParameters m hm)) (residualSylowFieldAction hTH eR t))^2=Nat.card (ExtensionField (binaryParameters m hm)) ∧
        Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) =
          Nat.card (sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) *
            (sourceS L H).relIndex (T : Subgroup G) ∧
        Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) ≤
          Nat.card (sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) * n := by
  obtain ⟨D,hD,hHall,hmark,eR,t,ht,htS,htD,hσ⟩ :=
    d.triality_exists_outer_involution h hTH hp m hm e hne
  have hc := d.triality_outer_torus_centralizer h hTH hp m hm e hD hmark t htD
  have hσ2 := (orderOf_eq_prime_iff.mp hσ).1
  have hσne := (orderOf_eq_prime_iff.mp hσ).2
  have hfixed : Nat.card (FixedBy.subfield (ExtensionField (binaryParameters m hm)) (residualSylowFieldAction hTH eR t))^2 =
      Nat.card (ExtensionField (binaryParameters m hm)) := FiniteField.card_involution_fixed_sq _ (fun x => by
        have he := congrArg (fun σ : ExtensionField (binaryParameters m hm) ≃+* ExtensionField (binaryParameters m hm) => σ x) hσ2
        exact he) hσne
  refine ⟨D,hD,hHall,hmark,eR,t,ht,htS,htD,hσ,hfixed,hc.2.2.2.2.2,?_⟩
  rw [hc.2.2.2.2.2]
  apply Nat.mul_le_mul_left
  rw [←hc.2.2.1]
  exact Nat.le_of_dvd (by have := h.exponent; omega : 0<n) hc.2.2.2.1

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
