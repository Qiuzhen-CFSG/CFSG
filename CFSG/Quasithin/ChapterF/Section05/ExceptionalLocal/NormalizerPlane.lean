module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionRoots
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ExtendedAffinePlane

/-!
# The literal plane-core normalizer quotient in F.5.4

The ordinary plane two-core is elementary, so its center is the whole core.
Thus the original source plane-normalizer hypothesis identifies N_G(Q2)
with the given extended plane endpoint. The already marked affine S5
comparison gives a surjection of this exact normalizer with kernel Q2.
The first isomorphism theorem proves its relative quotient is S5.

Source: Aschbacher--Smith F.5.4(4), printed p.301. This part only needs the
original F.4.31 hypotheses, and retains all original ambient inclusions.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
local notation "PE" => Extension.plane 1 hn
local notation "P" => planeParabolic 1 hn
open BinaryPermutation
local notation "AF" => Multiplicative (core (Fin 5)) ⋊[AlternatingFiveExtension.coreAction] Equiv.Perm (Fin 5)
local notation "V" => Multiplicative (core (Fin 5))
variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

theorem normalizer_planeRootImage_eq_Q : Source.planeRootImage c i = Q c i true := by
  rw [Q_eq_map_pCore]
  have he : IsElementaryAbelian 2 (pCore 2 P) := by
    rw [BinaryCompletion.plane_eq_local]
    infer_instance
  have hc : center (pCore 2 P) = ⊤ := center_eq_top
  rw [Source.planeRootImage,hc,←MonoidHom.range_eq_map]
  change MonoidHom.range (((i.comp c.right).comp Source.planeInclusion).comp
    (pCore 2 P).subtype) = _
  rw [MonoidHom.range_comp,range_subtype]
  rfl

theorem normalizer_Q_eq_plane (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z) :
    normalizer (Q c i true : Set G) = M c i true := by
  rw [←normalizer_planeRootImage_eq_Q]
  exact h.plane_normalizer

theorem normalizer_Q_quotient (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z) :
    Nonempty (planeCoreNormalizerQuotient c i ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨e,_,heV,_⟩ := UnitaryTwo.ExtendedAffinePlane.exists_marked_plane_equiv
  let f : PE →* G := endpointMap c i true
  have hf : Function.Injective f := endpointMap_injective c i h.embedding_injective true
  let en : normalizer (Q c i true : Set G) ≃* PE :=
    (MulEquiv.subgroupCongr (normalizer_Q_eq_plane c i z h)).trans
      (MonoidHom.ofInjective hf).symm
  let π : normalizer (Q c i true : Set G) →* Equiv.Perm (Fin 5) :=
    (SemidirectProduct.rightHom : AF →* Equiv.Perm (Fin 5)).comp
      (e.symm.toMonoidHom.comp en.toMonoidHom)
  have hπ : Function.Surjective π := SemidirectProduct.rightHom_surjective.comp
    (e.symm.surjective.comp en.surjective)
  have hQ : Q c i true = UnitaryTwo.ExtendedAffinePlane.planeCore.map f := by
    rw [UnitaryTwo.ExtendedAffinePlane.planeCore,map_map,Q_eq_map_pCore]
    rfl
  have hker : π.ker = (Q c i true).subgroupOf (normalizer (Q c i true : Set G)) := by
    ext x
    change SemidirectProduct.rightHom (e.symm (en x)) = 1 ↔ (x : G) ∈ Q c i true
    have hmem : (x : G) ∈ Q c i true ↔
        (x : G) ∈ UnitaryTwo.ExtendedAffinePlane.planeCore.map f :=
      SetLike.ext_iff.mp hQ (x : G)
    rw [hmem]
    have hx : f (en x) = x.val := by
      change f ((MonoidHom.ofInjective hf).symm
        ((MulEquiv.subgroupCongr (normalizer_Q_eq_plane c i z h)) x)) = x.val
      exact congrArg Subtype.val ((MonoidHom.ofInjective hf).apply_symm_apply _)
    change _ ↔ ∃ a, a ∈ UnitaryTwo.ExtendedAffinePlane.planeCore ∧ f a = x.val
    constructor
    · intro hp
      refine ⟨en x,?_,hx⟩
      rw [←heV]
      exact ⟨e.symm (en x),by
        rw [SemidirectProduct.range_inl_eq_ker_rightHom]
        exact hp,e.apply_symm_apply _⟩
    · rintro ⟨a,ha,hae⟩
      have ha' : a = en x := hf (hae.trans hx.symm)
      rw [ha',←heV] at ha
      obtain ⟨b,hb,hbe⟩ := ha
      change e b = en x at hbe
      have hb' : e.symm (en x) = b := by rw [←hbe,e.symm_apply_apply]
      rw [hb']
      rw [SemidirectProduct.range_inl_eq_ker_rightHom] at hb
      exact hb
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπ)⟩

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
