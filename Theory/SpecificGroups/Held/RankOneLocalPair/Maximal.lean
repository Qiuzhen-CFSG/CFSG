module

public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.CoreQuotient
public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.ConcreteMaximality
public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.MatrixQuotient
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoB
public import Theory.SpecificGroups.Held.TwoLocalCandidates.SelfNormalizing
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer
public import Theory.GroupTheory.NormalizerOuterPGroup

/-!
# Held's maximal local through all permitted outer extensions

The literal max5 subgroup is self-normalizing and contains a Held Sylow.
Its central involution generates the center of that Sylow, so every Sylow
stabilizer preserves max5. Extending this Sylow to an arbitrary inner
overgroup in Aut(He), then applying Sylow conjugacy, gives the local at any
specified Sylow. Maximality transfers from max5 using the intersection with
the inner group and the source supplement condition.

The proved outer-index bound gives the two possible orders. The local inner
subgroup is actually equivalent to max5, and its intrinsic core quotient
embeds normally in the larger local core quotient. The imported concrete
calculations prove IsCoatom max5 and construct the matrix equivalence
max5/O₂(max5) ≃ PSL₃(2). The final theorem discharges these two inputs,
retaining only full automorphism realization. It supplies MaximalOvergroups
to exists_of_automorphism_overgroups; the local-pair assembly owns realization
and the independent solvable overgroup construction. No simplicity or
E-generation premise is needed for this maximal-local construction.

Source: Aschbacher–Smith E.1.14(4), refs/quasithin.pdf, printed p.214;
ATLAS HeG1-max5W1 and Hed2G1-max4W1. All words use the inversion convention
in Held/Model/Source/README.md. No maximal-two-local catalogue is substituted
for maximality among all subgroups.
-/

@[expose] public section

namespace Held.RankOneLocalPair
open Subgroup TwoLocalCandidates LocalPairs LocalPairs.SylowGeometry.Calculations
open scoped Pointwise

/-- The checked Held Sylow normalizer and containment calculations make max5 self-normalizing. -/
theorem max5_self_normalizing : normalizer (max5 : Set He) = max5 :=
  normalizer_eq_of_representative representative_isPGroup InnerNormalizer.normalizer_eq 2

/-- Full realization transfers the proved permutation-normalizer bound to the actual outer quotient. -/
theorem inner_index_le_two_of_realization
    (hreal : Function.Surjective permutationGroup.normalizerMonoidHom) :
    (MulAut.innerSubgroup He).index ≤ 2 :=
  (Nat.card_le_card_of_surjective _
    (normalizerOuterAction_surjective permutationGroup hreal)).trans
    permutationNormalizerQuotient_card_le_two

/-- Within the automorphism normalizer, the inner actors are precisely conjugations by max5. -/
theorem local_inner_eq (U : Subgroup (MulAut He))
    (hU : U ≤ automorphismNormalizer max5) :
    (max5.map MulAut.conj).subgroupOf U = (MulAut.innerSubgroup He).subgroupOf U := by
  ext x
  constructor
  · rintro ⟨g, _, hg⟩
    exact ⟨g, hg⟩
  · rintro ⟨g, hg⟩
    have hm : g ∈ normalizer (max5 : Set He) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      change MulAut.conj g ∈ automorphismNormalizer max5
      rw [hg]
      exact hU x.property
    exact ⟨g, max5_self_normalizing ▸ hm, hg⟩

/-- The local inner subgroup is genuinely equivalent to max5, using Held centerlessness. -/
noncomputable def localInnerEquiv (U : Subgroup (MulAut He))
    (hU : U ≤ automorphismNormalizer max5) (h5 : max5.map MulAut.conj ≤ U) :
    max5 ≃* (MulAut.innerSubgroup He).subgroupOf U :=
  ((max5.equivMapOfInjective MulAut.conj
    (Theory.GroupTheory.conj_injective_of_center_eq_bot LocalPairs.center_eq_bot)).trans
      (subgroupOfEquivOfLe h5).symm).trans
    (MulEquiv.subgroupCongr (local_inner_eq U hU))

/-- Restriction to any automorphism subgroup preserves the index bound on its inner intersection. -/
theorem local_inner_index_le_two (U : Subgroup (MulAut He))
    (hreal : Function.Surjective permutationGroup.normalizerMonoidHom) :
    ((MulAut.innerSubgroup He).subgroupOf U).index ≤ 2 :=
  (Nat.le_of_dvd (Nat.pos_of_ne_zero (MulAut.innerSubgroup He).index_ne_zero_of_finite)
    ((MulAut.innerSubgroup He).relIndex_dvd_index_of_normal U)).trans
      (inner_index_le_two_of_realization hreal)

/-- The quotient by the relative inner subgroup is a two-group. -/
theorem local_inner_quotient_isPGroup (U : Subgroup (MulAut He))
    (hreal : Function.Surjective permutationGroup.normalizerMonoidHom) :
    IsPGroup 2 (U ⧸ (MulAut.innerSubgroup He).subgroupOf U) := by
  have hle := local_inner_index_le_two U hreal
  have hpos := ((MulAut.innerSubgroup He).subgroupOf U).index_ne_zero_of_finite
  have hc : Nat.card (U ⧸ (MulAut.innerSubgroup He).subgroupOf U) = 1 ∨
      Nat.card (U ⧸ (MulAut.innerSubgroup He).subgroupOf U) = 2 := by
    change Nat.card (U ⧸ (MulAut.innerSubgroup He).subgroupOf U) ≤ 2 at hle
    change Nat.card (U ⧸ (MulAut.innerSubgroup He).subgroupOf U) ≠ 0 at hpos
    omega
  rcases hc with hc | hc
  · exact IsPGroup.of_card (n := 0) hc
  · exact IsPGroup.of_card (n := 1) hc

/-- Every intermediate local between inner max5 and its automorphism normalizer has one of the two required orders. -/
theorem local_card (U : Subgroup (MulAut He))
    (hU : U ≤ automorphismNormalizer max5) (h5 : max5.map MulAut.conj ≤ U)
    (hreal : Function.Surjective permutationGroup.normalizerMonoidHom) :
    Nat.card U = 21504 ∨ Nat.card U = 43008 := by
  let I := (MulAut.innerSubgroup He).subgroupOf U
  have hI : Nat.card I = 21504 :=
    (Nat.card_congr (localInnerEquiv U hU h5).toEquiv).symm.trans
      InvolutionFixedData.TwoB.max5_card
  have hi : I.index = 1 ∨ I.index = 2 := by
    have hle : I.index ≤ 2 := local_inner_index_le_two U hreal
    have hpos : I.index ≠ 0 := I.index_ne_zero_of_finite
    omega
  have hc := I.card_mul_index
  rw [hI] at hc
  rcases hi with hi | hi
  · left; omega
  · right; omega

/-- The literal max5 subgroup contains an actual Sylow two-subgroup of Held. -/
theorem exists_sylow_le_max5 : ∃ R : Sylow 2 He, (R : Subgroup He) ≤ max5 := by
  obtain ⟨R, hR⟩ := exists_representative_sylow representative_isPGroup
    InnerNormalizer.normalizer_eq
  obtain ⟨g, hg⟩ := SylowContainment.exists_conjugate_representative_le 2
  refine ⟨R.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective, ?_⟩
  change (R : Subgroup He).map (MulAut.conj g).toMonoidHom ≤ max5
  rw [hR]
  exact hg

/-- Sylow conjugacy supplies every inner local overgroup from the two concrete max5 inputs. -/
theorem inner_overgroups_of_max5
    (hmax : IsCoatom max5)
    (e : max5 ⧸ pCore 2 max5 ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (S : Sylow 2 He) :
    ∃ P : Subgroup He, IsCoatom P ∧ Nat.card P = 21504 ∧
      (S : Subgroup He) ≤ P ∧ HasPSL3TwoCoreQuotient P := by
  obtain ⟨R, hR⟩ := exists_sylow_le_max5
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq He R S
  let d := MulAut.conj g
  refine ⟨max5.map d.toMonoidHom, (d.mapSubgroup.isCoatom_iff _).mpr hmax, ?_, ?_, ?_⟩
  · exact (card_map_of_injective d.injective).trans InvolutionFixedData.TwoB.max5_card
  · rw [← hg]
    exact map_mono hR
  · exact (hasPSL3TwoCoreQuotient_of_equiv e).of_equiv (d.subgroupMap max5)

/-- The matrix quotient of max5 supplies the actual normal PSL₃(2) section in every permitted local extension. -/
theorem local_hasPSL3TwoCoreQuotient (U : Subgroup (MulAut He))
    (hU : U ≤ automorphismNormalizer max5) (h5 : max5.map MulAut.conj ≤ U)
    (hreal : Function.Surjective permutationGroup.normalizerMonoidHom)
    (e : max5 ⧸ pCore 2 max5 ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :
    HasPSL3TwoCoreQuotient U := by
  let I := (MulAut.innerSubgroup He).subgroupOf U
  let d : I ≃* max5 := (localInnerEquiv U hU h5).symm
  apply hasPSL3TwoCoreQuotient_of_normal I
    ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans e)
  exact local_inner_quotient_isPGroup U hreal

/-- Apply the order and quotient transfers to the literal intersection with an inner overgroup. -/
theorem automorphism_normalizer_local (A : Subgroup (MulAut He))
    (hA : MulAut.innerSubgroup He ≤ A)
    (hreal : Function.Surjective permutationGroup.normalizerMonoidHom)
    (e : max5 ⧸ pCore 2 max5 ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :
    let U := A ⊓ automorphismNormalizer max5
    (Nat.card U = 21504 ∨ Nat.card U = 43008) ∧ HasPSL3TwoCoreQuotient U := by
  dsimp only
  have h5 : max5.map MulAut.conj ≤ A ⊓ automorphismNormalizer max5 := by
    apply le_inf
    · exact (map_le_range _ _).trans hA
    · rintro _ ⟨g, hg, rfl⟩
      exact mem_normalizer_iff_map_conj_eq.mp (max5.le_normalizer hg)
  exact ⟨local_card _ inf_le_right h5 hreal,
    local_hasPSL3TwoCoreQuotient _ inf_le_right h5 hreal e⟩

private theorem inner_preimage_stable (U : Subgroup (MulAut He)) :
    U ≤ automorphismNormalizer (U.comap MulAut.conj) := by
  have hm (a : MulAut He) (ha : a ∈ U) (y : He) (hy : MulAut.conj y ∈ U) :
      MulAut.conj (a y) ∈ U := by
    have he : MulAut.conj (a y) = a * MulAut.conj y * a⁻¹ := by
      ext x
      simp
    rw [he]
    exact U.mul_mem (U.mul_mem ha hy) (U.inv_mem ha)
  intro a ha
  change (U.comap MulAut.conj).map a.toMonoidHom = U.comap MulAut.conj
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact hm a ha y hy
  · intro x hx
    refine ⟨a.symm x, hm a⁻¹ (U.inv_mem ha) x hx, a.apply_symm_apply x⟩

/-- A maximal self-normalizing inner local stays maximal in an automorphism overgroup that it supplements. -/
theorem automorphism_normalizer_isCoatom
    (hmax : IsCoatom max5) (A : Subgroup (MulAut He))
    (hA : MulAut.innerSubgroup He ≤ A)
    (hgen : (MulAut.innerSubgroup He).subgroupOf A ⊔
      (automorphismNormalizer max5).subgroupOf A = ⊤) :
    IsCoatom ((automorphismNormalizer max5).subgroupOf A) := by
  let P := (automorphismNormalizer max5).subgroupOf A
  apply SetLike.isCoatom_iff.mpr
  refine ⟨?_, ?_⟩
  · intro htop
    apply hmax.ne_top
    apply top_unique
    intro g _
    have hg : (⟨MulAut.conj g, hA ⟨g, rfl⟩⟩ : A) ∈ P := by
      change (⟨MulAut.conj g, hA ⟨g, rfl⟩⟩ : A) ∈
        (automorphismNormalizer max5).subgroupOf A
      rw [htop]
      exact mem_top _
    exact max5_self_normalizing ▸ mem_normalizer_iff_map_conj_eq.mpr hg
  · intro V a hPV haP haV
    let U := V.map A.subtype
    let K := U.comap MulAut.conj
    have hMK : max5 ≤ K := by
      intro g hg
      have hgp : (⟨MulAut.conj g, hA ⟨g, rfl⟩⟩ : A) ∈ P :=
        mem_normalizer_iff_map_conj_eq.mp (max5.le_normalizer hg)
      exact mem_map_of_mem A.subtype (hPV hgp)
    rcases hmax.le_iff.mp hMK with hK | hK
    · have hi : (MulAut.innerSubgroup He).subgroupOf A ≤ V := by
        rintro b ⟨g, hg⟩
        have hgm : MulAut.conj g ∈ U := show g ∈ K from hK ▸ mem_top g
        obtain ⟨v, hv, he⟩ := hgm
        have hev : v = b := Subtype.ext (he.trans hg)
        exact hev ▸ hv
      apply top_unique
      rw [← hgen]
      exact sup_le hi hPV
    · exfalso
      apply haP
      have hs := inner_preimage_stable U (mem_map_of_mem A.subtype haV)
      change (a : MulAut He) ∈ automorphismNormalizer K at hs
      rw [hK] at hs
      exact hs

/-- Identify the relative automorphism normalizer with its literal ambient intersection. -/
def normalizerInEquiv (A : Subgroup (MulAut He)) :
    (automorphismNormalizer max5).subgroupOf A ≃* ↥(A ⊓ automorphismNormalizer max5) where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Construct the exact requested local when the specified Sylow already normalizes max5. -/
theorem maximalOvergroup_of_sylow_normalizes
    (hmax : IsCoatom max5)
    (e : max5 ⧸ pCore 2 max5 ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (hreal : Function.Surjective permutationGroup.normalizerMonoidHom)
    (A : Subgroup (MulAut He)) (hA : MulAut.innerSubgroup He ≤ A)
    (S : Sylow 2 A)
    (hgen : (MulAut.innerSubgroup He).subgroupOf A ⊔ (S : Subgroup A) = ⊤)
    (hS : (S : Subgroup A) ≤ (automorphismNormalizer max5).subgroupOf A) :
    ∃ P : Subgroup A, IsCoatom P ∧ (Nat.card P = 21504 ∨ Nat.card P = 43008) ∧
      (S : Subgroup A) ≤ P ∧ HasPSL3TwoCoreQuotient P := by
  let P := (automorphismNormalizer max5).subgroupOf A
  have hgenP : (MulAut.innerSubgroup He).subgroupOf A ⊔ P = ⊤ :=
    top_unique (hgen ▸ sup_le_sup_left hS _)
  obtain ⟨hc, hq⟩ := automorphism_normalizer_local A hA hreal e
  have hd := Nat.card_congr (normalizerInEquiv A).toEquiv
  refine ⟨P, automorphism_normalizer_isCoatom hmax A hA hgenP, ?_, hS, ?_⟩
  · exact hd ▸ hc
  · exact hq.of_equiv (normalizerInEquiv A).symm

private theorem fixed_of_center_two {G : Type*} [Group G] (R : Subgroup G)
    (hc : Nat.card (center R) = 2) (a : MulAut G)
    (ha : R.map a.toMonoidHom = R) (z : R) (hz : z ∈ center R) :
    a (z : G) = z := by
  let r : R ≃* R := (a.subgroupMap R).trans (MulEquiv.subgroupCongr ha)
  let c := Subgroup.centerCongr r
  let v : center R := ⟨z, hz⟩
  have hfix : c v = v := by
    by_cases hv : v = 1
    · rw [hv, c.map_one]
    obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : center R)).mp hc
    exact (hw (c v) (by
      intro he
      exact hv (c.injective (he.trans c.map_one.symm)))).trans (hw v hv).symm
  exact congrArg (fun w : center R => (w.val : G)) hfix

/-- A Sylow stabilizer fixes the central involution and hence preserves its exact centralizer max5. -/
theorem sylow_stabilizer_le_max5_stabilizer (R : Sylow 2 He)
    (hR : (R : Subgroup He) ≤ max5) :
    automorphismNormalizer R ≤ automorphismNormalizer max5 := by
  let z : He := max5First ^ 4
  have hzC : z ∈ centralizer (R : Set He) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp (CentralInvolutionBounds.max5_le_centralizer (hR hx))
  have hzR : z ∈ R := by
    have := centralizer_le_normalizer (R : Set He) hzC
    rwa [inner_self_normalizing R] at this
  let zR : R := ⟨z, hzR⟩
  have hzZ : zR ∈ center R := mem_center_iff.mpr (fun x => Subtype.ext (hzC x x.property))
  intro a ha
  have haR : (R : Subgroup He).map a.toMonoidHom = R := ha
  have haz : a z = z := fixed_of_center_two (R : Subgroup He) (inner_center_card R)
    a haR zR hzZ
  change max5.map a.toMonoidHom = max5
  apply eq_of_le_of_card_ge
  · rw [← InvolutionFixedData.TwoB.centralizer_eq_max5]
    have hm := map_centralizer_le_centralizer_image ({z} : Set He) a.toMonoidHom
    rw [Set.image_singleton] at hm
    change (centralizer ({z} : Set He)).map a.toMonoidHom ≤
      centralizer ({a z} : Set He) at hm
    rwa [haz] at hm
  · exact (card_map_of_injective a.injective).ge

/-- Extend an inner Sylow to the given automorphism overgroup while preserving max5. -/
theorem exists_sylow_normalizes_max5 (A : Subgroup (MulAut He))
    (hA : MulAut.innerSubgroup He ≤ A) :
    ∃ S : Sylow 2 A, (S : Subgroup A) ≤ (automorphismNormalizer max5).subgroupOf A := by
  obtain ⟨R, hR⟩ := exists_sylow_le_max5
  let f : He →* A := MulAut.conj.codRestrict A (fun g => hA ⟨g, rfl⟩)
  have hf : Function.Injective f := by
    intro x y he
    exact Theory.GroupTheory.conj_injective_of_center_eq_bot LocalPairs.center_eq_bot
      (congrArg Subtype.val he)
  obtain ⟨S, hS⟩ := R.exists_comap_eq_of_injective hf
  have hi : ((S : Subgroup A).map A.subtype).comap MulAut.conj = (R : Subgroup He) := by
    change (((S : Subgroup A).map A.subtype).comap A.subtype).comap f = _
    rw [comap_map_eq_self_of_injective A.subtype_injective, hS]
  have hs := inner_preimage_stable ((S : Subgroup A).map A.subtype)
  rw [hi] at hs
  refine ⟨S, ?_⟩
  intro a ha
  exact sylow_stabilizer_le_max5_stabilizer R hR
    (hs (mem_map_of_mem A.subtype ha))

/-- Conditional final assembly, including all outer extensions and arbitrary specified Sylows.
Only the actual maximality and matrix-quotient calculations for max5 remain
in addition to automorphism realization. -/
theorem maximalOvergroups_of_realization_and_max5
    (hmax : IsCoatom max5)
    (e : max5 ⧸ pCore 2 max5 ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (hreal : Function.Surjective permutationGroup.normalizerMonoidHom) :
    MaximalOvergroups := by
  intro A hA S hgen
  obtain ⟨S₀, hS₀⟩ := exists_sylow_normalizes_max5 A hA
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A S₀ S
  let d := MulAut.conj a
  have hSmap : (S₀ : Subgroup A).map d.toMonoidHom = (S : Subgroup A) :=
    congrArg (fun T : Sylow 2 A => (T : Subgroup A)) ha
  have hi : ((MulAut.innerSubgroup He).subgroupOf A).map d.toMonoidHom =
      (MulAut.innerSubgroup He).subgroupOf A := by
    apply mem_normalizer_iff_map_conj_eq.mp
    rw [Subgroup.normalizer_eq_top]
    exact mem_top _
  have hgen₀ : (MulAut.innerSubgroup He).subgroupOf A ⊔ (S₀ : Subgroup A) = ⊤ := by
    apply map_injective (f := d.toMonoidHom) d.injective
    rw [Subgroup.map_sup, hi, hSmap, map_top_of_surjective d.toMonoidHom d.surjective]
    exact hgen
  obtain ⟨P, hP, hc, hSP, hq⟩ := maximalOvergroup_of_sylow_normalizes
    hmax e hreal A hA S₀ hgen₀ hS₀
  refine ⟨P.map d.toMonoidHom, (d.mapSubgroup.isCoatom_iff _).mpr hP, ?_, ?_, ?_⟩
  · have hd := card_map_of_injective (K := P) (f := d.toMonoidHom) d.injective
    exact hd ▸ hc
  · rw [← hSmap]
    exact map_mono hSP
  · exact hq.of_equiv (d.subgroupMap P)

/-- The maximal-local contract for every inner overgroup and specified Sylow.
The concrete maximality and matrix-quotient proofs discharge both max5 inputs;
only full automorphism realization remains with the local-pair assembly owner. -/
theorem maximalOvergroups_of_realization
    (hreal : Function.Surjective permutationGroup.normalizerMonoidHom) :
    MaximalOvergroups :=
  maximalOvergroups_of_realization_and_max5
    ConcreteMaximality.max5_isCoatom MatrixQuotient.equiv hreal

end Held.RankOneLocalPair
