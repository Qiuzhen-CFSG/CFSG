module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialFieldAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Maximal
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction
public import Theory.AtlasPort.LinearGroups.G2.EvenBorelTorus

/-!
# Splitting the original G₂ Sylow extension and constructing an outer involution

The whole-overlap comparison pulls the concrete split torus back to an odd
Hall subgroup D of the original common Borel C. The original T normalizes C.
Hall conjugacy therefore gives T = S N_T(D). In the model, a unipotent
normalizer of the split torus centralizes it; the six root characters then
force all six coordinates to vanish. Transport through the same middle map
gives S intersect N_T(D) = 1, including at field order four.

The actual right-quotient field action has kernel S. Its restriction embeds
N_T(D) into the cyclic field-automorphism group, proving that this is a
cyclic complement. If S<T, Cauchy's theorem now constructs an actual
involution t outside S, normalizing the same marked D. The original
right-factor quotient supplies an actual PSL₂(F) equivalence, and t's
field coefficient has order two, since the field-action kernel is S.

These results discharge the splitting and outer-involution existence steps
of F.4.29(2) and F.4.38 without assuming an extension of local automorphisms
to a full model automorphism. The outer centralizer's order and its Sylow
placement remain required for S=T. Original uniqueness, exhaustive amalgam
comparison, completion recognition and full GlobalExit remain with the
assembly owner. The companion applies these constructions in Chapter 12.

Source: Aschbacher–Smith F.4.29(2), F.4.37–38, printed pp.289,293–294,
and 5.3.3, p.659 (`refs/quasithin.pdf`). The imported root formulas retain
the ATLAS attribution in LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Subgroup.OddHall Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Atlas.G2 Atlas.G2.LieParabolicSetup
variable {G : Type*} [Group G] [Finite G]

private theorem unipotent_torus_normalizer_trivial
    {F : Type} [Field F] [Finite F] [CharP F 2] (hq : 2 < Nat.card F)
    (u : Model F) (hu : u ∈ unipotent)
    (hn : u ∈ normalizer (splitTorus (K := F) : Set (Model F))) : u=1 := by
  have hc (t : Model F) (ht : t ∈ splitTorus) : t*u=u*t := by
    have hxD : u*t*u⁻¹*t⁻¹ ∈ splitTorus := splitTorus.mul_mem
      ((mem_normalizer_iff.mp hn t).mp ht) (splitTorus.inv_mem ht)
    have hxU : u*t*u⁻¹*t⁻¹ ∈ unipotent := by
      have hh := unipotent.mul_mem hu (torus_normalizes_unipotent ht (unipotent.inv_mem hu))
      simpa only [mul_assoc] using hh
    have hx := disjoint_def.mp unipotent_disjoint_torus hxU hxD
    have he : u*t=t*u := mul_inv_eq_one.mp (by
      simpa only [mul_inv_rev,mul_assoc] using hx)
    exact he.symm
  rw [unipotent_eq_range] at hu
  obtain ⟨v,rfl⟩ := hu
  have he (l m : Fˣ) : torusUnipotentParameters l m v=v := by
    apply unipotentProduct_injective
    rw [←torus_unipotentProduct]
    have hh := hc (torus l m) (show torus l m ∈ splitTorus from ⟨(l,m),rfl⟩)
    rw [hh,mul_inv_cancel_right]
  have hu : 1 < Nat.card Fˣ := by
    rw [Nat.card_units]
    omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hu
  obtain ⟨a,ha⟩ := exists_ne (1:Fˣ)
  have ha' : (a:F) ≠ 1 := fun hh => ha (Units.ext hh)
  have h₁ := he a 1
  have h₂ := he 1 a
  have hv : v=0 := by
    funext i
    have h1 := congrFun h₁ i
    have h2 := congrFun h₂ i
    fin_cases i <;> simp [torusUnipotentParameters] at h1 h2 ⊢ <;>
      first | exact eq_zero_of_mul_eq_self_left ha' h1
            | exact eq_zero_of_mul_eq_self_left ha' h2
            | exact eq_zero_of_mul_eq_self_left (inv_ne_one.mpr ha') h1
            | exact eq_zero_of_mul_eq_self_left (inv_ne_one.mpr ha') h2
  rw [hv,unipotentProduct_zero]

omit [Finite G] in
private theorem source_common_borel_normalized
    {T : Sylow 2 G} {L H : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) :
    (T : Subgroup G) ≤ normalizer
      (ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) : Set G) := by
  have hTS := sylow_normalizes_sourceS hTL hTH
  have hb (K : Subgroup G) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
      (T : Subgroup G) ≤ normalizer (ChapterF.Source.borel K (sourceS L H) : Set G) := by
    have hi := (le_inf hTS hTK).trans inf_normalizer_le_normalizer_inf
    exact (le_inf hTK (hi.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact (le_inf
    ((le_inf (hb L hTL) (hb (residual H) (hTH.trans (le_normalizer_residual H)))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)) hTS).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

private theorem model_torus_hall
    {F : Type} [Field F] [Finite F] [CharP F 2] :
    IsHallSubgroup oddPrimes (EvenBorelTorus.complement (F := F)) := by
  exact OddHall.oddHall_of_normalized_sup unipotent_isTwoGroup
    (Nat.coprime_two_left.mpr EvenBorelTorus.card_torus_odd)
    EvenBorelTorus.torus_le_normalizer rfl

private theorem Preparation.cyclic_of_disjoint_sourceS
    {T : Sylow 2 G} {L W H A B U : Subgroup G} {n r : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (hS : ∀ i : Fin 2, sourceS L H ≤ ![L,residual H] i)
    (he : ClassicalGroup.IsPSL (residual H ⧸ pCore 2 (residual H)) 2 (2^r))
    (hUT : U ≤ (T : Subgroup G)) (hdis : Disjoint (sourceS L H) U) : IsCyclic U := by
  obtain ⟨E,_,_,hE,⟨e⟩⟩ := he
  let := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hE)
  let : IsCyclic (E ≃+* E) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  let f := (residualSylowFieldAction hTH e).comp (inclusion hUT)
  apply isCyclic_of_injective f
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro u hu
  have hs : u.val ∈ sourceS L H := by
    have hk : inclusion hUT u ∈ (residualSylowFieldAction hTH e).ker := hu
    rw [d.residual_sylow_field_kernel h hTH hS e] at hk
    exact hk
  exact Subtype.ext (disjoint_def.mp hdis hs u.property)

/-- A compatible G₂ comparison supplies a Hall torus whose Sylow normalizer
complements the original source core. The comparison's whole overlap is retained. -/
theorem Preparation.g2_source_sylow_torus_split
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) :
    let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
    ∃ D : Subgroup G, D ≤ C ∧ IsHallSubgroup oddPrimes (D.subgroupOf C) ∧
      (∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ splitTorus) ∧
      Disjoint (sourceS L H) (normalizer (D : Set G)) ∧
      IsCyclic ((T : Subgroup G) ⊓ normalizer (D : Set G) : Subgroup G) ∧
      (T : Set G) = (sourceS L H : Set G) *
        ((T : Subgroup G) ⊓ normalizer (D : Set G) : Set G) := by
  let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
  let hf := d.hypothesisF11 h hTH
  have hSC : sourceS L H ≤ C := le_sup_right
  let a : C ≃* Atlas.G2.borel (K := F) :=
    ((MulEquiv.subgroupCongr (ChapterF.Source.lemma_F_1_3_6 hf)).symm.trans e.middle).trans
      (MulEquiv.subgroupCongr ChapterF.GreenBook.LieModels.G2.overlap_eq_borel)
  obtain ⟨P,hP⟩ := hf.sylow_commonBorel
  have hPS : (P : Subgroup C) = (sourceS L H).subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hSC]
  let R := (Atlas.G2.LieParabolicSetup.sylow (F := F)).subtype
    (show unipotent ≤ Atlas.G2.borel from le_sup_left)
  let : (R : Subgroup (Atlas.G2.borel (K := F))).Normal := EvenBorelTorus.radical_normal
  let := Sylow.unique_of_normal R (inferInstance : R.Normal)
  have hSR : ((sourceS L H).subgroupOf C).map a.toMonoidHom = EvenBorelTorus.radical := by
    rw [←hPS]
    exact congrArg Sylow.toSubgroup (Subsingleton.elim (P.mapSurjective a.surjective) R)
  let D₀ := EvenBorelTorus.complement.map a.symm.toMonoidHom
  let D := D₀.map C.subtype
  have hDC : D ≤ C := map_subtype_le _
  have hD₀ : D.subgroupOf C = D₀ := comap_map_eq_self_of_injective C.subtype_injective _
  have hDa : (D.subgroupOf C).map a.toMonoidHom = EvenBorelTorus.complement := by
    rw [hD₀]
    have heq : a.toMonoidHom.comp a.symm.toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext a.apply_symm_apply
    rw [map_map,heq,map_id]
  have hHall : IsHallSubgroup oddPrimes (D.subgroupOf C) := by
    rw [hD₀]
    constructor
    · intro p hp
      apply (model_torus_hall (F := F)).p_in_pi_of_p_dvd_card p
      rwa [card_map_of_injective a.symm.injective] at hp
    · intro p hp
      apply (model_torus_hall (F := F)).p_in_pi_of_p_dvd_index p
      change p.val ∣ (EvenBorelTorus.complement.map a.symm.toMonoidHom).index at hp
      have hi : (EvenBorelTorus.complement.map a.symm.toMonoidHom).index =
          (EvenBorelTorus.complement (F := F)).index :=
        index_map_equiv (H := EvenBorelTorus.complement (F := F)) a.symm
      exact hi ▸ hp
  have hF := (d.g2_local_structure h hTH hp F (Or.inr ⟨e⟩)).1
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) h.exponent)
  have hdis : Disjoint (sourceS L H) (normalizer (D : Set G)) := by
    apply disjoint_def.mpr
    intro x hx hn
    let y : C := ⟨x,hSC hx⟩
    have hy : a y ∈ EvenBorelTorus.radical := hSR ▸ mem_map_of_mem a.toMonoidHom hx
    have hyn : y ∈ normalizer (D.subgroupOf C : Set C) := by
      rw [mem_normalizer_iff]
      intro z
      exact (mem_normalizer_iff.mp hn z.val)
    have han := (D.subgroupOf C).le_normalizer_map a.toMonoidHom
      (mem_map_of_mem a.toMonoidHom hyn)
    rw [hDa] at han
    have han' := (EvenBorelTorus.complement (F := F)).le_normalizer_map
      (Atlas.G2.borel (K := F)).subtype (mem_map_of_mem _ han)
    rw [map_subgroupOf_eq_of_le (show splitTorus (K := F) ≤ Atlas.G2.borel from le_sup_right)] at han'
    have he : (a y).val=1 := unipotent_torus_normalizer_trivial hq _ hy han'
    have hey : y=1 := a.injective ((Subtype.ext he).trans a.map_one.symm)
    exact congrArg Subtype.val hey
  refine ⟨D,hDC,hHall,?_,hdis,?_,?_⟩
  · intro b
    let c : C := ⟨b.val,(ChapterF.Source.lemma_F_1_3_6 hf).le b.property⟩
    have hh : a c ∈ EvenBorelTorus.complement ↔ c ∈ D.subgroupOf C := by
      rw [←hDa]
      exact mem_map_iff_mem a.injective
    exact hh.symm
  · have hs := d.g2_local_structure h hTH hp F (Or.inr ⟨e⟩)
    exact d.cyclic_of_disjoint_sourceS h hTH hs.2.2.2.2 hs.2.2.2.1
      inf_le_left (hdis.mono_right inf_le_right)
  · exact OddHall.normal_sylow_frattini C (sourceS L H) (T : Subgroup G) D
      hf.commonBorel_solvable (sourceS_le_sylow h.sylow_normalizes hTH)
      (source_common_borel_normalized h.sylow_normalizes hTH) P hP hDC hHall


/-- If the original source core is proper in T, the pulled-back Hall torus
constructs an actual involution of T outside S. -/
theorem Preparation.g2_exists_outer_involution
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hne : sourceS L H ≠ (T : Subgroup G)) :
    let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
    ∃ D : Subgroup G, D ≤ C ∧ IsHallSubgroup oddPrimes (D.subgroupOf C) ∧
      (∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ splitTorus) ∧
      ∃ eR : (residual H ⧸ pCore 2 (residual H)) ≃* Theory.PSL2.Group F,
      ∃ t : T, orderOf t=2 ∧ t.val ∉ sourceS L H ∧
        t.val ∈ normalizer (D : Set G) ∧ orderOf (residualSylowFieldAction hTH eR t)=2 := by
  obtain ⟨D,hDC,hHall,hmark,hdis,_,hsplit⟩ := d.g2_source_sylow_torus_split h hTH hp F e
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
  have hs := d.g2_local_structure h hTH hp F (Or.inr ⟨e⟩)
  obtain ⟨b⟩ := hs.2.2.1
  let eR : (residual H ⧸ pCore 2 (residual H)) ≃* Theory.PSL2.Group F :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans local₁CoreQuotientEquivPSL
  refine ⟨D,hDC,hHall,hmark,eR,t,ht,htS,u.property.2,?_⟩
  apply orderOf_eq_prime
  · have ht2 : t^2=1 := (orderOf_eq_prime_iff.mp ht).1
    rw [←map_pow,ht2,map_one]
  · intro he
    apply htS
    have hh : t ∈ (residualSylowFieldAction hTH eR).ker := he
    rw [d.residual_sylow_field_kernel h hTH hs.2.2.2.2 eR] at hh
    exact hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
