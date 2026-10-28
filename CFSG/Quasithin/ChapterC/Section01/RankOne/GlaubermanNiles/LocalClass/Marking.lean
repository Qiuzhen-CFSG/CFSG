module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass
public import Stellmacher.OmegaOneCenterMap

/-!
# Changing the source marking in the Glauberman--Niles local class

A source isomorphism preserves the intrinsic omega center. Precomposing
an embedding therefore preserves its literal normal closure and the Sylow
image. The natural actor, module and intertwining law are transported
together through equality of that normal closure. The local-class theorem
thus retains the original abstract two-group when a subgroup is realized
inside different local overgroups.

The private coordinate expression exposes only the normal subgroup index
for dependent transport; it has exactly the three fields of NaturalModel.
Source: Aschbacher--Smith C.1.17--19, printed pp.126--127, and the common
Baumann group in 15.4.7, printed p.1158.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B C H : Type*} [Group B] [Group C] [Group H] [Finite H]

private def NaturalCoordinates (V : Subgroup H) [V.Normal]
    (F : Type) [Field F] [CharP F 2] : Prop :=
  let K := centralizer (V : Set H)
  let q := QuotientGroup.mk' K
  let A := (generalizedFitting (H ⧸ K)).comap q
  let U := ⁅V,A⁆
  let D := (centralizer (A : Set H)).subgroupOf U
  ∃ ai : generalizedFitting (H ⧸ K) ≃* commutator PSL(2,F),
    ∃ vi : (U ⧸ D) ≃* Multiplicative (Fin 2 → F),
      ∀ (a : A) (w : U),
      Multiplicative.toAdd (vi (QuotientGroup.mk' D
        ⟨(a : H) * (w : H) * (a : H)⁻¹,
          (inferInstance : U.Normal).conj_mem w w.property a⟩)) =
      Representation.specialLinearNatural 2
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm
          (ai ⟨q a,a.property⟩ : PSL(2,F)))
        (Multiplicative.toAdd (vi (QuotientGroup.mk' D w)))

private theorem naturalCoordinates_congr (V W : Subgroup H) [V.Normal] [W.Normal]
    (h : V = W) (F : Type) [Field F] [CharP F 2] :
    NaturalCoordinates V F ↔ NaturalCoordinates W F := by
  subst W
  rfl

/-- Equal literal normal closures carry the same full natural-module data. -/
theorem naturalModel_of_localV_eq (e : B →* H) (f : C →* H)
    (hV : localV e = localV f)
    {F : Type} [Field F] [CharP F 2] (m : NaturalModel e F) :
    Nonempty (NaturalModel f F) := by
  have he : NaturalCoordinates (localV e) F := ⟨m.actorIso,m.moduleIso,m.intertwining⟩
  have hf := (naturalCoordinates_congr (localV e) (localV f) hV F).mp he
  obtain ⟨ai,vi,hi⟩ := hf
  exact ⟨⟨ai,vi,hi⟩⟩

/-- Membership in the intrinsic central omega subgroup. -/
theorem mem_omegaCenter_iff (x : B) :
    x ∈ omegaCenter B ↔ x^2 = 1 ∧ ∀ b : B, b*x=x*b := by
  constructor
  · rintro ⟨z,hz,rfl⟩
    let : IsElementaryAbelian 2 (omega₁ (center B) (p := 2)) :=
      IsElementaryAbelian.omega₁_of_isMulCommutative (center B)
    exact ⟨congrArg (center B).subtype
      (elemPow_eq_one_of_isElementaryAbelian z hz),mem_center_iff.mp z.property⟩
  · rintro ⟨hx,hc⟩
    let z : center B := ⟨x,mem_center_iff.mpr hc⟩
    refine ⟨z,subset_closure ?_,rfl⟩
    change z^(2^1)=1
    apply Subtype.ext
    change x^(2^1)=1
    simpa only [pow_one] using hx

/-- The original central seed is preserved by a change of marking. -/
theorem omegaCenter_map_equiv (a : C ≃* B) :
    (omegaCenter C).map a.toMonoidHom = omegaCenter B := by
  ext b
  constructor
  · rintro ⟨c,hc,rfl⟩
    obtain ⟨hc2,hcc⟩ := mem_omegaCenter_iff c |>.mp hc
    apply mem_omegaCenter_iff _ |>.mpr
    refine ⟨?_,?_⟩
    · change a c ^ 2 = 1
      simpa only [map_pow,map_one] using congrArg a hc2
    · intro b
      obtain ⟨c',rfl⟩ := a.surjective b
      change a c' * a c = a c * a c'
      simpa only [map_mul] using congrArg a (hcc c')
  · intro hb
    obtain ⟨hb2,hbc⟩ := mem_omegaCenter_iff b |>.mp hb
    refine ⟨a.symm b,(mem_omegaCenter_iff _).mpr ⟨?_,?_⟩,a.apply_symm_apply b⟩
    · apply a.injective
      simpa only [map_pow,map_one,a.apply_symm_apply] using hb2
    · intro c
      apply a.injective
      simpa only [map_mul,a.apply_symm_apply] using hbc (a c)

omit [Finite H] in
/-- Precomposition preserves the literal normal closure, rather than
choosing an isomorphic substitute module. -/
theorem localV_precomp_equiv (e : B →* H) (a : C ≃* B) :
    localV (e.comp a.toMonoidHom) = localV e := by
  unfold localV
  rw [←map_map,omegaCenter_map_equiv]

/-- The local-class condition is invariant under the marked source isomorphism.
The natural module and its intertwining law are transported together. -/
theorem InLocalClass.precomp_equiv {e : B →* H} (h : InLocalClass e)
    (a : C ≃* B) : InLocalClass (e.comp a.toMonoidHom) := by
  refine ⟨h.injective.comp a.injective,?_,h.fitting,?_⟩
  · obtain ⟨T,hT,hm⟩ := h.sylow
    refine ⟨T,?_,hm⟩
    rw [MonoidHom.range_comp, a.toMonoidHom.range_eq_top_of_surjective a.surjective,←MonoidHom.range_eq_map,hT]
  · obtain ⟨n,hn,F,iF,iFin,iChar,hF,⟨m⟩⟩ := h.natural
    exact ⟨n,hn,F,iF,iFin,iChar,hF,
      naturalModel_of_localV_eq e (e.comp a.toMonoidHom) (localV_precomp_equiv e a).symm m⟩

end CFSG.Quasithin.ChapterC.GlaubermanNiles
