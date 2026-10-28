module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Alternatives
public import CFSG.Quasithin.Chapter15.Section01.CaseI.OrdinarySource.InnerPlacement
public import Theory.SpecificGroups.Tits.SylowCenterMaximal
public import Theory.SpecificGroups.Triality.SylowCenterMaximal
public import Theory.SpecificGroups.G2Even.BinarySylowCenterMaximal
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.BinarySylowFixers
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup

/-!
# The initial binary rank-two rows

For an ordinary component in the original pre-exclusion configuration, a
central involution induces an involutory automorphism fixing a Sylow subgroup
pointwise. Innerness on the actual model therefore places the centralizer of
the full Sylow center inside M_L. The maximality of that centralizer and
properness of M_L give equality, including the literal centralizer clause of
15.1.20(3c). The three model applications discharge both model-theoretic premises.

These are branches of the initial catalogue. Exhaustiveness and the later
15.1.22 parabolic refinements remain with the ordinary catalogue assembly.
Source: Aschbacher--Smith 15.1.20(3c), printed pp.1095--1096.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Innerness of involutory Sylow fixers on an actual model gives the original centralizer placement. -/
theorem PreExclusionSource.centralizer_le_of_sylow_fixers
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {X : Type*} [Group X] (e : d.L ≃* X)
    (hinner : ∀ (P : Sylow 2 X) (a : MulAut X),
      a ^ 2 = 1 → (∀ x ∈ P, a x = x) → ∃ t : X, a = MulAut.conj t) :
    d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G) ≤ d.ML := by
  obtain ⟨z,hz,hzne⟩ := (bot_or_exists_ne_one (centralInvolutions T)).resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  obtain ⟨α,ha,_⟩ := ((s.ordinary hL).actions z hz hzne).2
  apply d.ordinary_inner_centralizer_le hG hu h s.centralizer_sylow s.odd_core hL hz hzne α ha
  let K := d.L.subgroupOf d.G1
  let a : K ≃* X := (subgroupOfEquivOfLe d.L_component.1).trans e
  obtain ⟨P,_,h115⟩ := d.ordinary_involution_inputs hG hu h s.centralizer_sylow
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_subnormal K hL.1
  have hfix (x : K) (hx : x ∈ Q) : α x = x := by
    apply Subtype.ext
    apply Subtype.ext
    rw [ha]
    have hxP : (x : d.G1) ∈ P := by
      change x ∈ (Q : Subgroup K) at hx
      rw [hQ] at hx
      exact hx
    exact mul_inv_eq_iff_eq_mul.mpr
      ((h115 z hz hzne).central x (mem_map_of_mem d.G1.subtype hxP)).symm
  let R := Q.mapSurjective (f := a.toMonoidHom) a.surjective
  have hα2 : α ^ 2 = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change ((α (α x) : d.G1) : G) = x
    rw [ha,ha]
    have hz2 : z*z=1 := by
      simpa only [(h115 z hz hzne).involution,pow_two] using pow_orderOf_eq_one z
    calc
      z * (z * (x : G) * z⁻¹) * z⁻¹ = (z*z) * x * (z*z)⁻¹ := by group
      _ = x := by rw [hz2]; simp
  have hβ2 : (MulAut.congr a α) ^ 2 = 1 := by
    rw [← map_pow, hα2, map_one]
  obtain ⟨t,ht⟩ := hinner R (MulAut.congr a α) hβ2 (by
    rintro _ ⟨x,hx,rfl⟩
    change a (α (a.symm (a x))) = a x
    rw [a.symm_apply_apply,hfix x hx])
  obtain ⟨u,hu⟩ := (MulAut.congr_inner_iff a α).mp ⟨t,ht⟩
  exact ⟨u,hu.symm⟩

/-- A maximal Sylow-center centralizer forces equality with the original M_L. -/
theorem PreExclusionSource.centralizer_eq_of_sylow_fixers
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {X : Type*} [Group X] (e : d.L ≃* X)
    (hinner : ∀ (P : Sylow 2 X) (a : MulAut X),
      a ^ 2 = 1 → (∀ x ∈ P, a x = x) → ∃ t : X, a = MulAut.conj t)
    (hmax : ∀ P : Sylow 2 d.L,
      IsCoatom (centralizer ((center P).map (P : Subgroup d.L).subtype : Set d.L))) :
    d.ML = d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G) := by
  have hle := s.centralizer_le_of_sylow_fixers (h := h) hG hM hu hL e hinner
  obtain ⟨P,hP⟩ := s.component_sylow
  let Z := (center P).map (P : Subgroup d.L).subtype
  let C := d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G)
  have hZ : Z.map d.L.subtype = (center d.SL).map d.SL.subtype := by
    change ((center P).map (P : Subgroup d.L).subtype).map d.L.subtype = _
    rw [map_map, ← map_center_image_of_injective (P : Subgroup d.L)
      d.L.subtype d.L.subtype_injective, hP]
  have hC : C.subgroupOf d.L = centralizer (Z : Set d.L) := by
    ext x
    constructor
    · intro hx z hz
      apply Subtype.ext
      exact hx.2 z (hZ ▸ mem_map_of_mem d.L.subtype hz)
    · intro hx
      refine ⟨x.property, ?_⟩
      intro z hz
      obtain ⟨w,hw,rfl⟩ := hZ.symm ▸ hz
      exact congrArg Subtype.val (hx w hw)
  have hne : d.ML.subgroupOf d.L ≠ ⊤ := by
    intro he
    exact (not_le_of_gt (s.ordinary hL).local_proper) (subgroupOf_eq_top.mp he)
  have hm : IsCoatom (C.subgroupOf d.L) := hC.symm ▸ hmax P
  have he := (hm.le_iff_eq hne).mp (comap_mono hle)
  have hh := congrArg (Subgroup.map d.L.subtype) he
  simpa only [map_subgroupOf_eq_of_le (s.ordinary hL).local_proper.le,
    map_subgroupOf_eq_of_le (show C ≤ d.L from inf_le_left)] using hh

/-- The actual Tits model supplies the entire initial row, including its centralizer clause. -/
theorem PreExclusionSource.ordinary20_of_tits
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Tits.ParrottGroup) : d.Ordinary20Alternatives := by
  apply Ordinary20Alternatives.binaryRankTwo (.inr (.inl ⟨e⟩))
  apply s.centralizer_eq_of_sylow_fixers (h := h) hG hM hu hL e
  · intro P a _ ha
    obtain ⟨t,_,ht⟩ := Tits.SylowPointwiseInner.parrott_fixing_sylow_inner P a ha
    exact ⟨t,ht⟩
  · exact Tits.SylowCenterMaximal.centralizer_isCoatom e

/-- The genuine binary triality carrier supplies the entire initial rank-two row. -/
theorem PreExclusionSource.ordinary20_of_triality
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) :
    d.Ordinary20Alternatives := by
  apply Ordinary20Alternatives.binaryRankTwo (.inr (.inr ⟨e⟩))
  apply s.centralizer_eq_of_sylow_fixers (h := h) hG hM hu hL e
  · intro _ a ha _
    have hp : IsPGroup 2 (zpowers a) := by
      apply IsPGroup.of_card_dvd_pow (n := 1)
      simpa only [Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one ha
    obtain ⟨t,ht⟩ := Triality.Standard.ParabolicOuterTwo.twoSubgroup_le_inner_at_two
      (zpowers a) hp (mem_zpowers a)
    exact ⟨t,ht.symm⟩
  · exact Triality.Standard.SylowCenterMaximal.centralizer_isCoatom e

/-- The actual binary derived G₂ supplies the full initial row, including its centralizer clause. -/
theorem PreExclusionSource.ordinary20_of_binaryG2Derived
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* commutator (Atlas.G2.Model (ZMod 2))) : d.Ordinary20Alternatives := by
  apply Ordinary20Alternatives.binaryRankTwo (.inl ⟨e⟩)
  apply s.centralizer_eq_of_sylow_fixers (h := h) hG hM hu hL e
  · intro P a _ ha
    obtain ⟨t,_,ht⟩ := Atlas.G2.EvenInvolutionGeometry.binary_fixing_sylow_inner
      Atlas.G2.LieAutomorphismExtensions.binaryConjugation_bijective P a ha
    exact ⟨t,ht⟩
  · exact Atlas.G2.BinarySylowCenterMaximal.centralizer_isCoatom e

/-- Every actual binary rank-two model has the literal centralizer geometry of
15.1.20(3c) in the original pre-exclusion configuration. -/
theorem PreExclusionSource.ordinary20_of_binaryRankTwo
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : OrdinaryBinaryRankTwo d.L) : d.Ordinary20Alternatives := by
  rcases hm with hg | ht | hd
  · exact s.ordinary20_of_binaryG2Derived (h := h) hG hM hu hL (Classical.choice hg)
  · exact s.ordinary20_of_tits (h := h) hG hM hu hL (Classical.choice ht)
  · exact s.ordinary20_of_triality (h := h) hG hM hu hL (Classical.choice hd)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
