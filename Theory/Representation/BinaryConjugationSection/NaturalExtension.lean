module
public import Theory.Representation.BinaryConjugationSection.Projection
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.BinaryConjugationSection.FixedImage
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.SL2FourNaturalExtensions.Quadratic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Theory.Representation.BinaryConjugationSection.Canonical
/-!
# Natural factors of a literal binary group section

Marked group sections V/Z and Q/V construct both natural factors of the
actual middle module Q/Z. The given coordinate maps produce an equivariant
injection and projection, so the submodule is exactly the image of V.
An original centralizing subgroup supplies its full image dimension in the
fixed space. Conversely quadraticity bounds the original triple commutator.

These are the group-to-module bridges for the terminal characteristic-two
case of Niles, “Pushing-up in finite groups”, printed p.58. The natural
extension result is Lemma 3.4, printed pp.37–39; the marked group factors
come from the earlier Proposition 5.5.
-/

public section
noncomputable section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G J W N : Type*} [Group G] [Group J]
  [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup N] [Module (ZMod 2) N]

/-- Two marked group factors construct the invariant submodule and its literal quotient. -/
theorem exists_natural_submodule
    (H Q V Z : Subgroup G) (hVQ : V≤Q) (hZV : Z≤V)
    (q : H→*J) (hq : Function.Surjective q)
    (ρ : Representation (ZMod 2) J W) (τ : Representation (ZMod 2) J N)
    (c : BinaryConjugationSection H Q Z (ρ.comp q))
    (cV : BinaryConjugationSection H V Z (τ.comp q))
    (cQ : BinaryConjugationSection H Q V (τ.comp q)) :
    ∃ (X : Subrepresentation ρ) (eX : X.toSubmodule≃ₗ[ZMod 2]N)
      (eQ : (W⧸X.toSubmodule)≃ₗ[ZMod 2]N),
      (∀g x,eX (X.toRepresentation g x)=τ g (eX x)) ∧
      (∀g x,eQ (X.quotientRepresentation g x)=τ g (eQ x)) ∧
      X.toSubmodule=c.imageSpace V := by
  let cv : V→*Multiplicative W := c.coordinates.comp (inclusion hVQ)
  have hk : cV.coordinates.ker≤cv.ker := by
    intro v hv
    apply (c.coordinates_eq_one_iff _).mpr
    exact (cV.coordinates_eq_one_iff v).mp hv
  let f₀ := cV.coordinates.liftOfSurjective cV.onto ⟨cv,hk⟩
  have hf₀ (v:V) : f₀ (cV.coordinates v)=cv v :=
    cV.coordinates.liftOfRightInverse_comp_apply _ _ _ v
  let fl : N→ₗ[ZMod 2]W := (AddMonoidHom.toMultiplicative.symm f₀).toZModLinearMap 2
  have hfl (v:V) : fl (cV.coordinates v).toAdd=(c.coordinates (inclusion hVQ v)).toAdd := hf₀ v
  have hfe (g:J) (v:N) : fl (τ g v)=ρ g (fl v) := by
    obtain ⟨h,rfl⟩ := hq g
    obtain ⟨a,ha⟩ := cV.onto (Multiplicative.ofAdd v)
    have ha' : (cV.coordinates a).toAdd=v := congrArg Multiplicative.toAdd ha
    rw [←ha']
    change fl ((τ.comp q) h _)=_
    rw [←cV.equivariant,hfl,hfl]
    exact c.equivariant h (inclusion hVQ a)
  let f : τ.IntertwiningMap ρ := fl.intertwiningMap_of_isIntertwiningMap τ ρ hfe
  have hfi : Function.Injective fl := by
    apply (LinearMap.ker_eq_bot).mp
    apply bot_unique
    intro v hv
    obtain ⟨a,ha⟩ := cV.onto (Multiplicative.ofAdd v)
    have ha' : (cV.coordinates a).toAdd=v := congrArg Multiplicative.toAdd ha
    have hzero : (c.coordinates (inclusion hVQ a)).toAdd=0 := (hfl a).symm.trans (ha' ▸ hv)
    have hz : (a:G)∈Z := (c.coordinates_eq_one_iff _).mp hzero
    have hn := (cV.coordinates_eq_one_iff a).mpr hz
    exact ha'.symm.trans (congrArg Multiplicative.toAdd hn)
  have hfr : LinearMap.range fl=c.imageSpace V := by
    ext w
    constructor
    · rintro ⟨v,rfl⟩
      obtain ⟨a,ha⟩ := cV.onto (Multiplicative.ofAdd v)
      have ha' : (cV.coordinates a).toAdd=v := congrArg Multiplicative.toAdd ha
      exact (c.mem_imageSpace_iff V _).mpr
        ⟨inclusion hVQ a,a.property,(hfl a).symm.trans (congrArg fl ha')⟩
    · intro hw
      obtain ⟨a,ha,rfl⟩ := (c.mem_imageSpace_iff V w).mp hw
      exact ⟨(cV.coordinates ⟨a,ha⟩).toAdd,hfl ⟨a,ha⟩⟩
  let X := f.range
  let eX : X.toSubmodule≃ₗ[ZMod 2]N := (LinearEquiv.ofInjective fl hfi).symm
  obtain ⟨p,hp,hpc,hpk⟩ := exists_projection H H Q Z V le_rfl hZV q q hq
    (MonoidHom.id J) (fun _=>rfl) ρ τ c cQ
  have hpk' : p.toLinearMap.ker=X.toSubmodule := hpk.trans hfr.symm
  let eQ : (W⧸X.toSubmodule)≃ₗ[ZMod 2]N :=
    (Submodule.quotEquivOfEq _ _ hpk'.symm).trans (p.toLinearMap.quotKerEquivOfSurjective hp)
  have heQ (w:W) : eQ (X.toSubmodule.mkQ w)=p w := by
    exact p.toLinearMap.quotKerEquivOfSurjective_apply_mk hp w
  refine ⟨X,eX,eQ,?_,?_,hfr⟩
  · intro g x
    apply (LinearEquiv.ofInjective fl hfi).injective
    apply Subtype.ext
    change fl (eX (X.toRepresentation g x))=fl (τ g (eX x))
    rw [hfe]
    have he (y:X.toSubmodule) : fl (eX y)=y :=
      congrArg Subtype.val ((LinearEquiv.ofInjective fl hfi).apply_symm_apply y)
    rw [he,he]
    rfl
  · intro g x
    induction x using Submodule.Quotient.induction_on with
    | _ w =>
      change eQ (X.toSubmodule.mkQ (ρ g w))=τ g (eQ (X.toSubmodule.mkQ w))
      rw [heQ,heQ]
      exact IntertwiningMap.isIntertwining (ρ.comp (MonoidHom.id J)) τ p g w
end Representation.BinaryConjugationSection

namespace Representation.BinaryConjugationSection
open BinaryOffender
variable {G J W:Type*} [Group G] [Group J]
  [AddCommGroup W] [Module (ZMod 2) W]
  {H Q Z:Subgroup G} (ρ:Representation (ZMod 2) J W) (q:H→*J)
  (c:BinaryConjugationSection H Q Z (ρ.comp q))

include c in
/-- A centralizing original subgroup supplies its full section dimension
inside the common fixed space of the actual actor image. -/
theorem fixedDimension_ge_of_centralizing_subgroup [Finite Q]
    (S D:Subgroup G) (hDQ:D≤Q) (hSD:⁅S,D⁆=⊥)
    (n:ℕ) (hi:Z.relIndex D=2^n) :
    n≤Module.finrank (ZMod 2) (fixedSpace ρ ((S.subgroupOf H).map q)) := by
  let : Finite W := Finite.of_surjective (fun u:Q=>(c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  have hfix:c.imageSpace D≤fixedSpace ρ ((S.subgroupOf H).map q) := by
    intro w hw a
    obtain ⟨aH,ha,he⟩:=a.property
    change ρ (a:J) w=w
    rw [←he]
    exact c.fixed_on_imageSpace_of_commutator_le S D (hSD.le.trans bot_le) aH ha w hw
  rw [←c.imageSpace_finrank_of_index D hDQ n hi]
  exact Submodule.finrank_mono hfix

include c in
/-- An original subgroup centralizing modulo the kernel supplies its full section dimension
inside the common fixed space of the actual actor image. -/
theorem fixedDimension_ge_of_commutator_le [Finite Q]
    (S D:Subgroup G) (hDQ:D≤Q) (hSD:⁅S,D⁆≤Z)
    (n:ℕ) (hi:Z.relIndex D=2^n) :
    n≤Module.finrank (ZMod 2) (fixedSpace ρ ((S.subgroupOf H).map q)) := by
  let : Finite W := Finite.of_surjective (fun u:Q=>(c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  have hfix:c.imageSpace D≤fixedSpace ρ ((S.subgroupOf H).map q) := by
    intro w hw a
    obtain ⟨aH,ha,he⟩:=a.property
    change ρ (a:J) w=w
    rw [←he]
    exact c.fixed_on_imageSpace_of_commutator_le S D hSD aH ha w hw
  rw [←c.imageSpace_finrank_of_index D hDQ n hi]
  exact Submodule.finrank_mono hfix


include c in
/-- Quadraticity of the actual image bounds the literal original triple
commutator by the coordinate kernel. -/
theorem triple_commutator_le_of_quadratic
    (S:Subgroup G) (hSH:S≤H) [Q.Normal]
    (hq:IsQuadratic ρ ((S.subgroupOf H).map q)) : ⁅⁅Q,S⁆,S⁆≤Z := by
  rw [commutator_comm ⁅Q,S⁆ S]
  apply c.commutator_le_of_imageSpace_fixed S ⁅Q,S⁆ hSH (commutator_le_left _ _) 
  rw [commutator_comm Q S,c.imageSpace_commutator S Q hSH le_rfl]
  apply Submodule.span_le.mpr
  rintro _ ⟨a,ha,v,hv,rfl⟩ b
  exact hq (q b) (mem_map_of_mem q b.property) (q a) (mem_map_of_mem q ha) v

end Representation.BinaryConjugationSection

namespace Representation.BinaryConjugationSection
variable {G:Type*} [Group G]
/-- An elementary abelianization makes every quotient above the derived
group elementary; the original subgroup embedding is retained. -/
theorem elementary_quotient_of_derived_le
    (Q Z:Subgroup G) [(Z.subgroupOf Q).Normal]
    [IsElementaryAbelian 2 (Q⧸_root_.commutator Q)]
    (hQ:⁅Q,Q⁆≤Z) : IsElementaryAbelian 2 (Q⧸Z.subgroupOf Q) := by
  have hp (x:Q⧸Z.subgroupOf Q) : x^2=1 := by
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf Q) x
    rw [←map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    have hs : (QuotientGroup.mk' (_root_.commutator Q) a)^2=1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (Q⧸_root_.commutator Q)) _
    rw [←map_pow] at hs
    have hm := (QuotientGroup.eq_one_iff _).mp hs
    apply hQ
    rw [←Q.map_subtype_commutator]
    exact mem_map_of_mem Q.subtype hm
  exact {
    is_comm := ⟨fun a b=>(Commute.of_orderOf_dvd_two
      (fun x=>orderOf_dvd_of_pow_eq_one (hp x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }

end Representation.BinaryConjugationSection

namespace Representation.BinaryConjugationSection
open BinaryOffender SL2FourNatural
variable {G W:Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

/-- Marked natural group factors and a centralizing subgroup of section order
sixteen force the original triple commutator into the coordinate kernel. -/
theorem triple_commutator_le_of_natural_factors
    (H Q V Z:Subgroup G) [Finite Q] [Q.Normal] (hVQ:V≤Q) (hZV:Z≤V)
    (q:H→*SL) (hq:Function.Surjective q)
    (ρ:Representation (ZMod 2) SL W)
    (c:BinaryConjugationSection H Q Z (ρ.comp q))
    (cV:BinaryConjugationSection H V Z (naturalRepresentation.comp q))
    (cQ:BinaryConjugationSection H Q V (naturalRepresentation.comp q))
    (S D:Subgroup G) (hSH:S≤H) (hDQ:D≤Q) (hSD:⁅S,D⁆=⊥)
    (hi:Z.relIndex D=16) (P:Sylow 2 SL)
    (hP:(S.subgroupOf H).map q=(P:Subgroup SL)) : ⁅⁅Q,S⁆,S⁆≤Z := by
  let : Finite W := Finite.of_surjective (fun u:Q=>(c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  obtain ⟨X,eX,eQ,heX,heQ,hX⟩ := exists_natural_submodule H Q V Z hVQ hZV q hq
    ρ naturalRepresentation c cV cQ
  have hf : 4≤Module.finrank (ZMod 2) (fixedSpace ρ P) := by
    rw [←hP]
    exact c.fixedDimension_ge_of_centralizing_subgroup ρ q S D hDQ hSD 4 hi
  have hquad := SL2FourNaturalExtensions.sylow_isQuadratic_of_natural_sections
    ρ X eX eQ heX heQ P hf
  apply c.triple_commutator_le_of_quadratic ρ q S hSH
  rwa [hP]
/-- Marked natural group factors and a subgroup centralizing modulo the kernel of section order
sixteen force the original triple commutator into the coordinate kernel. -/
theorem triple_commutator_le_of_natural_factors_modulo
    (H Q V Z:Subgroup G) [Finite Q] [Q.Normal] (hVQ:V≤Q) (hZV:Z≤V)
    (q:H→*SL) (hq:Function.Surjective q)
    (ρ:Representation (ZMod 2) SL W)
    (c:BinaryConjugationSection H Q Z (ρ.comp q))
    (cV:BinaryConjugationSection H V Z (naturalRepresentation.comp q))
    (cQ:BinaryConjugationSection H Q V (naturalRepresentation.comp q))
    (S D:Subgroup G) (hSH:S≤H) (hDQ:D≤Q) (hSD:⁅S,D⁆≤Z)
    (hi:Z.relIndex D=16) (P:Sylow 2 SL)
    (hP:(S.subgroupOf H).map q=(P:Subgroup SL)) : ⁅⁅Q,S⁆,S⁆≤Z := by
  let : Finite W := Finite.of_surjective (fun u:Q=>(c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  obtain ⟨X,eX,eQ,heX,heQ,hX⟩ := exists_natural_submodule H Q V Z hVQ hZV q hq
    ρ naturalRepresentation c cV cQ
  have hf : 4≤Module.finrank (ZMod 2) (fixedSpace ρ P) := by
    rw [←hP]
    exact c.fixedDimension_ge_of_commutator_le ρ q S D hDQ hSD 4 hi
  have hquad := SL2FourNaturalExtensions.sylow_isQuadratic_of_natural_sections
    ρ X eX eQ heX heQ P hf
  apply c.triple_commutator_le_of_quadratic ρ q S hSH
  rwa [hP]

end Representation.BinaryConjugationSection
