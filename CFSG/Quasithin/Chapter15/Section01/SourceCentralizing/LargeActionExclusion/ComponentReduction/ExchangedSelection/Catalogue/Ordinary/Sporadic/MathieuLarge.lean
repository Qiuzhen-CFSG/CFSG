module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.MaximalCentralizers
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.Components
public import Theory.Mathieu.M22.OrdinarySource
public import Theory.Mathieu.M22.Properties.ElementarySylowFixers

/-!
# The initial M₂₂ row through its actual central cover

The original central involution acts as a nontrivial inner Sylow fixer.
Its fixed subgroup is the full preimage of the quotient involution
centralizer and is also the centralizer of the original Sylow center.
The empty faithful-local-family hypothesis puts the solvable residual of
M_c in C_G(Z). Therefore the literal model image of M_L has residual in
that involution centralizer. Native M₂₂ solvable-overgroup geometry forces
equality, without claiming maximality of the involution centralizer.

All central two-covers and the original quotient map are retained. The
generic residual-control interface also records precisely what is needed
for the larger Mathieu rows, whose centralizers need not be solvable.
Source: Aschbacher--Smith 14.1.6 and 15.1.20(3d), printed pp.977,1097.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Residual control in the original M_c replaces a false maximality
premise for the larger Mathieu centralizers. The model image is obtained
from the actual L/O₂(L) equivalence. -/
theorem PreExclusionSource.centralizer_eq_of_quotient_residual_control
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {X : Type*} [Group X] [Finite X] (e : (d.L ⧸ pCore 2 d.L) ≃* X)
    (hX : center X = ⊥)
    (hinner : ∀ (Q : Sylow 2 X) (a : MulAut X),
      (∀ x ∈ Q, a x = x) → ∃ t : X, a = MulAut.conj t)
    (hcard : ∀ Q : Sylow 2 X, Nat.card (center Q) ≤ 2)
    (hcontrol : ∀ (U : Subgroup X) (t : X), orderOf t = 2 →
      DoubleCoverCentralizer.TwoCentral t → centralizer ({t} : Set X) ≤ U →
      (solvableResidual U).map U.subtype ≤ centralizer ({t} : Set X) →
      U = centralizer ({t} : Set X)) :
    d.ML = d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G) := by
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  let ec := (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).trans e
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center d.L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact (s.ordinary hL).center_eq.symm
  have hinnerL (P : Sylow 2 d.L) (a : MulAut d.L) (hfix : ∀ x ∈ P, a x = x) :
      ∃ t : d.L, a = MulAut.conj t := by
    apply (MulAut.centralQuotientAction_inner_iff ec a).mp
    obtain ⟨Q,hQ⟩ := MulAut.centralQuotientAction_exists_fixed_sylow ec a P hfix
    exact hinner Q _ hQ
  let C := d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G)
  have hCML : C ≤ d.ML := s.centralizer_le_of_sylow_fixers (h := h) hG hM hu hL
    (MulEquiv.refl d.L) (fun P a _ ha => hinnerL P a ha)
  obtain ⟨z,hz,hzne⟩ := (bot_or_exists_ne_one (centralInvolutions T)).resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  obtain ⟨α,ha,_⟩ := s.ordinary_marked_model (h := h) hL hz hzne
  obtain ⟨P,hP⟩ := s.component_sylow
  have hfix : ∀ x ∈ P, α x = x := by
    intro x hx
    apply Subtype.ext
    rw [ha]
    exact mul_inv_eq_iff_eq_mul.mpr
      (centralInvolutions_le_centralizer_sylow T hz x
        (d.SL_le_S.trans d.S_le_T (hP ▸ mem_map_of_mem d.L.subtype hx))).symm
  have hz2 : z*z=1 := by
    have hh := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz
    simpa only [pow_two] using hh.2.1
  have hα2 : α^2=1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (α (α x) : G) = x
    rw [ha,ha]
    calc
      z*(z*(x:G)*z⁻¹)*z⁻¹ = (z*z)*x*(z*z)⁻¹ := by group
      _ = x := by rw [hz2]; simp
  have hαne : α ≠ 1 := by
    intro he
    have hc : z ∈ centralizer (d.L : Set G) := by
      intro x hx
      have hh := ha (⟨x,hx⟩ : d.L)
      rw [he] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    exact hzne (mem_bot.mp ((s.ordinary hL).central_faithful ▸ ⟨hz,hc⟩))
  obtain ⟨a,hi⟩ := hinnerL P α hfix
  have hi' : α ∈ (MulAut.conj (G := d.L)).range := ⟨a,hi.symm⟩
  obtain ⟨t,ht,htc,heq⟩ := MulAut.exists_twoCentral_model_of_central_cover
    f hf hk.le hX α hi' (orderOf_eq_prime hα2 hαne) P hfix
  have hcardEq : ∀ Q : Sylow 2 X, Nat.card (center Q) = 2 := by
    obtain ⟨Q,htQ,hct⟩ := htc
    let tQ : center Q := ⟨⟨t,htQ⟩,hct⟩
    have hne : tQ ≠ 1 := by
      intro he
      have ht1 : t=1 := congrArg (fun x : center Q => ((x : Q) : X)) he
      rw [ht1,orderOf_one] at ht
      omega
    let : Nontrivial (center Q) := ⟨⟨tQ,1,hne⟩⟩
    have hq := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial (center Q))
    intro R
    have he := Nat.card_congr (centerCongr (R.equiv Q)).toEquiv
    have hr := hcard R
    omega
  have hfixed := SylowCenterCover.fixed_eq_center_centralizer ec (s.ordinary hL).center_two
    P α hα2 hαne hi' hfix hcardEq
  let Z := (center P).map (P : Subgroup d.L).subtype
  have hZ : Z.map d.L.subtype = (center d.SL).map d.SL.subtype := by
    change ((center P).map (P : Subgroup d.L).subtype).map d.L.subtype = _
    rw [map_map,←map_center_image_of_injective (P : Subgroup d.L)
      d.L.subtype d.L.subtype_injective,hP]
  have hC : C.subgroupOf d.L = centralizer (Z : Set d.L) := by
    ext x
    constructor
    · intro hx v hv
      exact Subtype.ext (hx.2 v (hZ ▸ mem_map_of_mem d.L.subtype hv))
    · intro hx
      refine ⟨x.property,?_⟩
      intro v hv
      obtain ⟨w,hw,rfl⟩ := hZ.symm ▸ hv
      exact congrArg Subtype.val (hx w hw)
  have hfixedC : α.fixedSubgroup = C.subgroupOf d.L := hfixed.trans hC.symm
  have him : α.fixedSubgroup.map f = centralizer ({t} : Set X) := by
    rw [← MulAut.fixedSubgroup_conj]
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      rw [MulAut.mem_fixedSubgroup,←heq,(MulAut.mem_fixedSubgroup _ _).mp hx]
    · intro y hy
      obtain ⟨x,hx⟩ := MulAut.fixedSubgroupMap_surjective_of_sylow_fixed
        α (MulAut.conj t) f hf hk.le heq hα2 P hfix ⟨y,hy⟩
      exact ⟨x,x.property,congrArg Subtype.val hx⟩
  have hker : f.ker ≤ α.fixedSubgroup := by
    intro x hx
    rw [MulAut.mem_fixedSubgroup,hi]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp (hk ▸ hx) a)
  have hpre : α.fixedSubgroup = (centralizer ({t} : Set X)).comap f := by
    rw [←him,comap_map_eq_self hker]
  let U := d.ML.subgroupOf d.L
  let I := U.map f
  have hCI : centralizer ({t} : Set X) ≤ I := by
    rw [←him,hfixedC]
    exact map_mono (comap_mono hCML)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro x hx
    exact hMc.2 (fun w hw => (centralInvolutions_le_centralizer_sylow T hw x hx).symm)
  have hres := residual_le_centralizer_Z
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    hG T hempty ⟨Chapter1.mem_H_of_isTwoLocal hMc.1.1,hTMc⟩
  let j : U →* Mc := {
    toFun x := ⟨x.val.val,x.property.1.2⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hRF : (solvableResidual U).map U.subtype ≤ α.fixedSubgroup := by
    rintro _ ⟨x,hx,rfl⟩
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    rw [ha]
    have hc := hres (mem_map_of_mem Mc.subtype
      (map_solvableResidual_le j (mem_map_of_mem j hx))) z hz
    exact mul_inv_eq_iff_eq_mul.mpr hc
  have hRI : (solvableResidual I).map I.subtype ≤ centralizer ({t} : Set X) := by
    have he : (solvableResidual I).map I.subtype =
        ((solvableResidual U).map U.subtype).map f := by
      rw [←map_solvableResidual_eq (f.subgroupMap U) (f.subgroupMap_surjective U),map_map,map_map]
      rfl
    rw [he]
    exact (map_mono hRF).trans_eq him
  have hI := hcontrol I t ht htc hCI hRI
  have hUC : U ≤ C.subgroupOf d.L := by
    rw [←hfixedC,hpre]
    intro x hx
    exact hI ▸ mem_map_of_mem f hx
  have hle : d.ML ≤ C := by
    intro x hx
    exact hUC (show (⟨x,(s.ordinary hL).local_proper.le hx⟩ : d.L) ∈ U from hx)
  exact le_antisymm hle hCML

/-- The complete original M₂₂ constructor, retaining central two-covers.
The genuinely required empty-family hypothesis discharges residual control. -/
theorem PreExclusionSource.ordinary20_of_mathieuTwentyTwo_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.Mathieu.M22) : d.Ordinary20Alternatives := by
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  let : IsSimpleGroup (d.L ⧸ center d.L) := IsQuasisimple.simple
  let ec := (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).trans e
  let : IsSimpleGroup Sporadic.Mathieu.M22 := ec.symm.isSimpleGroup
  apply Ordinary20Alternatives.sporadic .m22 (by intro he; cases he) (by intro he; cases he) ⟨e⟩
  apply s.centralizer_eq_of_quotient_residual_control (h := h) hG hempty hM hu hL e
  · exact Sporadic.Mathieu.m22_center_eq_bot
  · intro Q a ha
    exact Sporadic.Mathieu.M22SylowPointwise.automorphism_inner_of_fixes_sylow a Q ha
  · exact Sporadic.Mathieu.m22_sylow_center_card_le_two
  · exact Sporadic.Mathieu.OrdinaryTwentyTwo.centralizer_eq_of_residual_le

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
