module
public import Theory.GroupTheory.PGroup.SecondCenterSquares
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.SecondCenterSections
public import Theory.Representation.SL3.NaturalDualElementaryLift

/-!
# Quadratic upper sections at the whole-center marking

Coordinates on the whole elementary center transport the intrinsic squares
and commutators of Z₂(Q)/Z(Q) to the same marked representation. The square
map is equivariant and its polarization is the original commutator. The
literal Φ(Z₂(Q)), embedded in the original group, lies in Z(Q) and is
normalized by every normalizer of Q.

A dual-natural subsection over the whole center has an elementary full
preimage when that center is natural or doubled natural at the same SL₃
marking. A nonzero covector stabilizer fixes no natural vector; it therefore
fixes no vector in either summand of a doubled center. It fixes the square
of any lift, so that square vanishes. This calculation retains the complete
central kernel and does not require the subsection to exhaust Q/Z(Q).

NonblockSecondCenterSquares discharges the center-model premise in the
original field-four nonabelian configuration. Existence and exhaustion of
upper dual sections, exclusion of the nonabelian doubled-center branch, and
the arbitrary-degree fixed-factor row remain part of C.1.34 reconstruction.
Source: Aschbacher–Smith C.1.34–35, printed pp.136–138, and original
4.3.8–10, pp.616–617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.SecondCenterSquares
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {K Q A : Subgroup G}
local notation "Z" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q
local notation "T₂" => Subgroup.upperCentralSeries Q 2
local notation "C₂" => Subgroup.subgroupOf (center Q) (Subgroup.upperCentralSeries Q 2)
local notation "V₂" => (T₂ ⧸ C₂)

/-- Actual square and alternating commutator coordinates on the second central
quotient. Neither nondegeneracy nor a model of the whole upper quotient is assumed. -/
@[expose] def HasSquareCoordinates {F W X : Type*} [Field F] [AddCommGroup W] [Module F W]
    [Group X] (K Q₀ : Subgroup G) (a : K →* X) (ρ : Representation F X W) : Prop :=
  let Upper := Subgroup.upperCentralSeries Q₀ 2
  let Central := (center Q₀).subgroupOf Upper
  let UpperQuotient := Upper ⧸ Central
  ∃ c : center Q₀ ≃* Multiplicative W, ∃ s : UpperQuotient → W,
    ∃ b : UpperQuotient →* (UpperQuotient →* Multiplicative W),
      (∀ (k : K) (z z' : center Q₀), ((z':Q₀):G)=(k:G)*((z:Q₀):G)*(k:G)⁻¹ →
        (c z').toAdd=ρ (a k) (c z).toAdd) ∧
      (∀ x : Upper, (c.symm (Multiplicative.ofAdd (s (QuotientGroup.mk' Central x))):Q₀)=(x:Q₀)^2) ∧
      (∀ x y : Upper, (c.symm (b (QuotientGroup.mk' Central x) (QuotientGroup.mk' Central y)):Q₀)=
        ⁅(x:Q₀),(y:Q₀)⁆) ∧
      (∀ u v, s (u*v)=s u+s v+(b u v).toAdd) ∧
      (∀ u, b u u=1) ∧
      (∀ (k : K) (x x' : Upper), (x'.val:G)=(k:G)*(x.val:G)*(k:G)⁻¹ →
        s (QuotientGroup.mk' Central x')=ρ (a k) (s (QuotientGroup.mk' Central x)))

/-- A whole elementary center model coordinates the actual upper squares and
commutators at that same marking. -/
theorem exists_marked_squares {F W X : Type*} [Field F] [AddCommGroup W] [Module F W]
    [Group X] [CharP F 2]
    (a : K →* X) (ρ : Representation F X W)
    (hm : HasSectionModel K Z ⊥ a ρ) :
    IsElementaryAbelian 2 (center Q) ∧ HasSquareCoordinates K Q a ρ := by
  let : IsElementaryAbelian 2 (Multiplicative W) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro v
      rw [pow_two]
      apply Multiplicative.toAdd.injective
      change v.toAdd+v.toAdd=0
      rw [←two_smul F,CharTwo.two_eq_zero,zero_smul]) }
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hi₀,c₀,hc₀⟩ := hm
  let := hi₀
  let j : center Q ≃* Z := (center Q).equivMapOfInjective Q.subtype Q.subtype_injective
  let c : center Q ≃* Multiplicative W := j.trans (QuotientGroup.quotientBot.symm.trans c₀)
  have hi : IsElementaryAbelian 2 (center Q) :=
    IsElementaryAbelian.of_injective c.toMonoidHom c.injective
  let := hi
  have hc (k : K) (z z' : center Q)
      (hz : ((z':Q):G)=(k:G)*((z:Q):G)*(k:G)⁻¹) :
      (c z').toAdd=ρ (a k) (c z).toAdd := hc₀ k (j z) (j z') hz
  let s := fun u : V₂ => (c (SecondCenterFrattini.upperSquare u)).toAdd
  let b := (SecondCenterFrattini.upperPolar (P := Q)).compr₂ c.toMonoidHom
  refine ⟨hi,c,s,b,hc,?_,?_,?_,?_,?_⟩
  · intro x
    change (c.symm (c (SecondCenterFrattini.upperSquare _)):Q)=_
    rw [c.symm_apply_apply,SecondCenterFrattini.upperSquare_apply]
  · intro x y
    change (c.symm (c (SecondCenterFrattini.upperPolar _ _)):Q)=_
    rw [c.symm_apply_apply,SecondCenterFrattini.upperPolar_apply]
  · intro u v
    dsimp [s,b]
    rw [SecondCenterFrattini.upperSquare_mul,c.map_mul,c.map_mul]
    rfl
  · intro u
    change c (SecondCenterFrattini.upperPolar u u)=1
    rw [SecondCenterFrattini.upperPolar_self,map_one]
  · intro k x x' hxx
    apply hc
    simp only [SecondCenterFrattini.upperSquare_apply,Subgroup.coe_pow,hxx]
    exact (map_pow (MulAut.conj (k:G)) (x.val:G) 2).symm

/-- The original second-center Frattini subgroup is central and inherits
normalization from every normalizer of Q. -/
theorem upper_frattini_structure (hQ : IsPGroup 2 Q) [IsElementaryAbelian 2 (center Q)] :
    let B := ((frattini T₂).map (T₂).subtype).map Q.subtype
    B ≤ Z ∧ normalizer (Q : Set G) ≤ normalizer (B : Set G) := by
  refine ⟨map_mono (SecondCenterFrattini.upper_frattini_le_center hQ),?_⟩
  rw [map_map]
  exact (normalizer_le_normalizer_characteristic_image Q T₂).trans
    (by
      have h := normalizer_le_normalizer_characteristic_image
        ((T₂).map Q.subtype) (frattini ((T₂).map Q.subtype))
      let e := (T₂).equivMapOfInjective Q.subtype Q.subtype_injective
      have he : (frattini T₂).map e.toMonoidHom=frattini ((T₂).map Q.subtype) :=
        frattini_map_equiv e
      have hf : ((T₂).map Q.subtype).subtype.comp e.toMonoidHom=
          Q.subtype.comp (T₂).subtype := by ext x; rfl
      rw [←he,map_map,hf] at h
      exact h)

variable {F : Type} [Field F] [CharP F 2]

omit [Finite G] in
private theorem dual_lift_elementary {W : Type*} [AddCommGroup W] [Module F W]
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (ρ : Representation F SL(3,F) W)
    (hAZ : HasSectionModel K A Z (linearThreeActor e) (specialLinearNatural 3).dual)
    (hAQ : A ≤ Q)
    (hm : HasSectionModel K Z ⊥ (linearThreeActor e) ρ)
    (hfix : ∀ f : Module.Dual F (Fin 3 → F), f ≠ 0 → ∀ v : W,
      (∀ g : SL(3,F), (specialLinearNatural 3).dual g f=f → ρ g v=v) → v=0) :
    IsElementaryAbelian 2 A := by
  obtain ⟨hZA,hKA,_,hi,d,hd⟩ := hAZ
  let := hi
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hi₀,c₀,hc⟩ := hm
  let := hi₀
  let c : Z ≃* Multiplicative W := QuotientGroup.quotientBot.symm.trans c₀
  let p : A →* Multiplicative (Module.Dual F (Fin 3 → F)) :=
    d.toMonoidHom.comp (QuotientGroup.mk' ((Z).subgroupOf A))
  have hker (x : A) : p x=1 ↔ (x:G)∈Z := by
    change d (QuotientGroup.mk' _ x)=1 ↔ _
    rw [d.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff (N := (Z).subgroupOf A) x
  have hZexp (z : G) (hz : z∈Z) : z^2=1 := by
    have hh : c ((⟨z,hz⟩:Z)^2)=1 := by
      rw [map_pow,pow_two]
      apply Multiplicative.toAdd.injective
      change (c ⟨z,hz⟩).toAdd+(c ⟨z,hz⟩).toAdd=0
      rw [←two_smul F,CharTwo.two_eq_zero,zero_smul]
    exact congrArg Subtype.val (c.map_eq_one_iff.mp hh)
  have hsquare (x : A) : (x:G)^2∈Z := by
    have hh : p (x^2)=1 := by
      rw [map_pow,pow_two]
      apply Multiplicative.toAdd.injective
      change (p x).toAdd+(p x).toAdd=0
      rw [←two_smul F,CharTwo.two_eq_zero,zero_smul]
    simpa only [Subgroup.coe_pow] using (hker (x^2)).mp hh
  have hs (x : A) : x^2=1 := by
    apply Subtype.ext
    change (x:G)^2=1
    by_cases hf : (p x).toAdd=0
    · exact hZexp x ((hker x).mp (Multiplicative.toAdd.injective hf))
    let z : Z := ⟨(x:G)^2,hsquare x⟩
    have hz : (c z).toAdd=0 := by
      apply hfix (p x).toAdd hf
      intro g hg
      obtain ⟨k,hk⟩ := e.surjective.comp (QuotientGroup.mk'_surjective _) g
      let y : A := A.normalizerMonoidHom ⟨k,hKA k.property⟩ x
      have hpy : p y=p x := by
        apply Multiplicative.toAdd.injective
        have hh := hd k x y rfl
        change (p y).toAdd=(specialLinearNatural 3).dual (linearThreeActor e k) (p x).toAdd at hh
        rw [show linearThreeActor e k=g from hk] at hh
        exact hh.trans hg
      have hyx : (y:G)/(x:G)∈Z := by
        have hh : y/x ∈ p.ker := p.div_mem_ker_iff.mpr hpy
        exact (hker (y/x)).mp hh
      have hcomm : Commute ((y:G)/(x:G)) (x:G) := by
        obtain ⟨t,ht,he⟩ := hyx
        rw [←he]
        exact congrArg Q.subtype (mem_center_iff.mp ht (⟨x,hAQ x.property⟩:Q)).symm
      have hysq : (y:G)^2=(x:G)^2 := by
        calc
          (y:G)^2=(((y:G)/(x:G))*(x:G))^2 := by rw [div_mul_cancel]
          _ = ((y:G)/(x:G))^2*(x:G)^2 := hcomm.mul_pow 2
          _ = (x:G)^2 := by rw [hZexp _ hyx,one_mul]
      have hzfix : (z:G)=(k:G)*(z:G)*(k:G)⁻¹ := by
        change (x:G)^2=(k:G)*(x:G)^2*(k:G)⁻¹
        calc
          (x:G)^2=(y:G)^2 := hysq.symm
          _ = (k:G)*(x:G)^2*(k:G)⁻¹ := by
            have hy : (y:G)=(k:G)*(x:G)*(k:G)⁻¹ := rfl
            rw [hy]
            exact (map_pow (MulAut.conj (k:G)) (x:G) 2).symm
      have hh := hc k z z hzfix
      change (c z).toAdd=ρ (linearThreeActor e k) (c z).toAdd at hh
      rw [show linearThreeActor e k=g from hk] at hh
      exact hh.symm
    exact congrArg Subtype.val (c.map_eq_one_iff.mp (Multiplicative.toAdd.injective hz))
  have hinv (x : A) : x⁻¹=x := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hs x)
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  intro x y
  calc x*y=(x*y)⁻¹ := (hinv _).symm
       _=y*x := by rw [mul_inv_rev,hinv,hinv]

omit [Finite G] in
/-- Every dual-natural subsection over the whole natural or doubled center
has an elementary full preimage. The actor marking is common to both sections. -/
theorem dual_section_elementary
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (hAQ : A ≤ Q)
    (hm : HasSectionModel K Z ⊥ (linearThreeActor e) (specialLinearNatural 3) ∨
      HasSectionModel K Z ⊥ (linearThreeActor e)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)))
    (hA : HasSectionModel K A Z (linearThreeActor e) (specialLinearNatural 3).dual) :
    IsElementaryAbelian 2 A := by
  rcases hm with hm|hm
  · exact dual_lift_elementary e _ hA hAQ hm SL3ParabolicNatural.dual_stabilizer_fixed_zero
  · apply dual_lift_elementary e _ hA hAQ hm
    intro f hf v hv
    exact Prod.ext
      (SL3ParabolicNatural.dual_stabilizer_fixed_zero f hf v.1 (fun g hg => congrArg Prod.fst (hv g hg)))
      (SL3ParabolicNatural.dual_stabilizer_fixed_zero f hf v.2 (fun g hg => congrArg Prod.snd (hv g hg)))

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.SecondCenterSquares
