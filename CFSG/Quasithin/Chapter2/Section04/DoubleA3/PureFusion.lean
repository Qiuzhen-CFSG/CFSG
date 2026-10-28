module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.SourceSetup
public import Theory.GroupTheory.DihedralPairPureFusion

/-!
# Pure fusion in the original paired-cubic source

The source component K is the actual A₆ in C_G(z₂), and the second factor
is the actual right conjugate of R ∩ K. Their involutions fuse to z₂ using
the marked z₁ and the source exchange element. A six-point class bound on
actual elementary sixteens then excludes mixed involutions by the dihedral
pair counting theorem. This fills the pure-fusion field of the frozen
source-factor record from the other raw source 2.4.36 fields.

The remaining hypothesis is stated at the original elementary subgroups,
not as pure-factor containment: each has at most six elements in z₂'s
ambient class. The book obtains this by repeating 2.4.29(2) in N_G(A₁).
The current family-action theorem alone does not provide that fusion
calculation; this module does not assert the earlier normalizer rerun.

Source: Aschbacher–Smith, 2.4.37, printed p.550, combined manuscript
of 1 March 2004.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter2.DoubleA3
open Subgroup Stellmacher AlternatingSix.ShadowLocal
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The precise earlier fusion conclusion needed in 2.4.37: every actual
rank-four elementary subgroup in R contains at most six conjugates of z₂.
The source proves it by applying 2.4.29(2) at N_G(A₁). -/
def SourceElementarySixteenFusion {d : MinimalBlockSetup M} (c : SourceComponentGeometry d) : Prop :=
  ∀ A : Subgroup G, A ≤ sourceR d → IsElementaryAbelian 2 A → Nat.card A=16 →
    Nat.card {a : A // IsConj c.z (a:G)} ≤ 6

omit [Finite G] in
/-- The original maximum-elementary family supplies the local contract
once its six-point fusion calculation and an order-sixteen member are known. -/
theorem SourceComponentGeometry.elementarySixteenFusion_of_maximum_family
    {d : MinimalBlockSetup M} (c : SourceComponentGeometry d)
    (T Q : Subgroup G) (hRT : sourceR d ≤ T)
    (hQ : Q ∈ elementaryAbelianMaxSubgroups T) (hQcard : Nat.card Q=16)
    (hfamily : ∀ A ∈ elementaryAbelianMaxSubgroups T,
      Nat.card {a : A // IsConj c.z (a:G)} ≤6) : SourceElementarySixteenFusion c := by
  intro A hAR hAe hAcard
  apply hfamily A
  refine ⟨hAR.trans hRT,hAe,?_⟩
  intro B hBT hBe
  simpa only [hAcard,hQcard] using hQ.2.2 B hBT hBe

/-- Source 2.4.37's pure-factor containment, with both factors' involution
fusion deduced from the actual A₆ and the original right conjugator. -/
theorem SourceComponentGeometry.pure_fusion_of_elementary_sixteen_fusion
    {d : MinimalBlockSetup M} (c : SourceComponentGeometry d)
    (P : Sylow 2 c.K)
    (hP : (P : Subgroup c.K).map c.K.subtype =
      (sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K)
    (E : Subgroup (involutionCentralizer c.z))
    (hE : E.map (involutionCentralizer c.z).subtype =
      (((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K).map
        (involutionCentralizer c.z).subtype).map (MulAut.conj c.s⁻¹).toMonoidHom)
    (hgen : ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K) ⊔ E =
      (sourceR d).subgroupOf (involutionCentralizer c.z))
    (hd : Disjoint ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K) E)
    (hc : ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K) ≤
      centralizer (E : Set (involutionCentralizer c.z)))
    (hlocal : SourceElementarySixteenFusion c) :
    ∀ a : involutionCentralizer c.z, IsConj c.z (a:G) →
      a ∈ (sourceR d).subgroupOf (involutionCentralizer c.z) → a ∈ c.K ∨ a ∈ E := by
  let H := involutionCentralizer c.z
  let R := (sourceR d).subgroupOf H
  let D := R ⊓ c.K
  obtain ⟨eP⟩ := exists_component_sylow_coordinates c.K c.componentEquiv P
  let eD : D ≃* DihedralGroup 4 := (MulEquiv.subgroupCongr hP.symm).trans eP
  obtain ⟨eE⟩ := exists_right_conjugate_factor_coordinates H D E c.s hE eD
  obtain ⟨e₀,hDmark,hEmark⟩ := Theory.GroupTheory.exists_marked_internalProductEquiv R D E hgen hd hc
  let eR : sourceR d ≃* R := (subgroupOfEquivOfLe c.thompson_le).symm
  let e := eR.trans (e₀.trans (eD.prodCongr eE))
  have hfirst (a : sourceR d) (ha : (e a).1=1) : ((eR a : R) : H) ∈ E := by
    have he : (e₀ (eR a)).1=1 := eD.injective (ha.trans eD.map_one.symm)
    have hh : e₀ (eR a) ∈ (E.subgroupOf R).map e₀.toMonoidHom := by
      rw [hEmark]
      exact ⟨he,trivial⟩
    change eR a ∈ E.subgroupOf R
    simpa only [mem_map_equiv, MulEquiv.symm_apply_apply] using hh
  have hsecond (a : sourceR d) (ha : (e a).2=1) : ((eR a : R) : H) ∈ D := by
    have he : (e₀ (eR a)).2=1 := eE.injective (ha.trans eE.map_one.symm)
    have hh : e₀ (eR a) ∈ (D.subgroupOf R).map e₀.toMonoidHom := by
      rw [hDmark]
      exact ⟨trivial,he⟩
    change eR a ∈ D.subgroupOf R
    simpa only [mem_map_equiv, MulEquiv.symm_apply_apply] using hh
  have hzz₁ : IsConj c.z (c.z₁:G) := by
    apply IsConj.symm
    apply isConj_iff.mpr
    exact ⟨c.s⁻¹,by simpa only [inv_inv] using c.exchange⟩
  let J := c.K.map H.subtype
  let eJ : J ≃* A6 := (c.K.equivMapOfInjective H.subtype H.subtype_injective).symm.trans c.componentEquiv
  let J' := J.map (MulAut.conj c.s⁻¹).toMonoidHom
  let eJ' : J' ≃* A6 := ((MulAut.conj c.s⁻¹).subgroupMap J).symm.trans eJ
  have hz₁J : (c.z₁:G) ∈ J := mem_map_of_mem H.subtype c.first_in_component
  have hzJ' : c.z ∈ J' := by
    refine mem_map.mpr ⟨c.z₁,hz₁J,?_⟩
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] using c.exchange
  have hEJ' : E.map H.subtype ≤ J' := by
    rw [hE]
    exact map_mono (map_mono inf_le_right)
  have haxes (a : sourceR d) (ha : a^2=1) (ha1 : a≠1)
      (hpure : (e a).1=1 ∨ (e a).2=1) : IsConj c.z (a:G) := by
    have haG : (a:G)^2=1 := congrArg Subtype.val ha
    have haG1 : (a:G)≠1 := fun hh => ha1 (Subtype.ext hh)
    rcases hpure with h | h
    · exact involution_fusion_of_alternating_six J' eJ' c.z hzJ' c.involution c.nonidentity
        a (hEJ' (mem_map_of_mem H.subtype (hfirst a h))) haG haG1
    · apply hzz₁.trans
      exact involution_fusion_of_alternating_six J eJ c.z₁ hz₁J
        (isConj_one_right.mp (c.involution ▸ hzz₁.pow 2))
        (fun hh => c.nonidentity (isConj_one_left.mp (hh ▸ hzz₁)))
        a (mem_map_of_mem H.subtype (hsecond a h).2) haG haG1
  intro a ha haR
  let b : sourceR d := ⟨a,haR⟩
  rcases Theory.GroupTheory.DihedralPairPureFusion.pure_of_elementary_sixteen_bound
    c.z c.involution (sourceR d) e haxes hlocal b ha with h | h
  · exact Or.inr (hfirst b h)
  · exact Or.inl (hsecond b h).2

/-- Fill the frozen source-factor record from source 2.4.36 and the preceding
six-point elementary fusion calculation, removing its pure-fusion premise. -/
def SourceComponentGeometry.sourceFactors_of_elementary_sixteen_fusion
    {d : MinimalBlockSetup M} (c : SourceComponentGeometry d)
    (hcentralizer : centralizer (c.K : Set (involutionCentralizer c.z)) ≤
      (sourceR d).subgroupOf (involutionCentralizer c.z))
    (eB : centralizer (c.K : Set (involutionCentralizer c.z)) ≃* Multiplicative (ZMod 4))
    (P : Sylow 2 c.K)
    (hP : (P : Subgroup c.K).map c.K.subtype =
      (sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K)
    (E : Subgroup (involutionCentralizer c.z))
    (hE : E.map (involutionCentralizer c.z).subtype =
      (((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K).map
        (involutionCentralizer c.z).subtype).map (MulAut.conj c.s⁻¹).toMonoidHom)
    (hgen : ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K) ⊔ E =
      (sourceR d).subgroupOf (involutionCentralizer c.z))
    (hd : Disjoint ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K) E)
    (hc : ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K) ≤
      centralizer (E : Set (involutionCentralizer c.z)))
    (hlocal : SourceElementarySixteenFusion c) : SourceFactorGeometry c where
  centralizer_le := hcentralizer
  centralizerEquiv := eB
  P := P
  component_sylow := hP
  E := E
  second_factor := hE
  generate := hgen
  disjoint := hd
  commute := hc
  pure_fusion := c.pure_fusion_of_elementary_sixteen_fusion P hP E hE hgen hd hc hlocal

end CFSG.Quasithin.Chapter2.DoubleA3
