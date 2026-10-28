module
public import CFSG.Quasithin.ChapterJ.Section05.SourceAction.RankThree
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Spheres
public import Theory.GroupAction.CosetTransport

/-!
# Marked coordinates on the original first suborbit

Orbit–stabilizer and the given genuine J.4.7 marking identify the unchanged
first F-orbit with native first-parabolic cosets. Equivariance transports
native sphere sizes and stabilizer transitivity to that original orbit.
Source: Aschbacher–Smith J.5.5(2–3), printed p.446.
-/

@[expose] public section
noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
open ReeF4.Octagon.Binary
local instance : Fintype (CosetGeometry.Vertex family):=Fintype.ofFinite _
variable {G:Type*} [Group G] {F:Subgroup G} {δ γ:Cosets F}
    (h:RudvalisAction F δ γ)

/-- The original first F-orbit is the native first-parabolic point space. -/
def pointEquiv : orbit F δ≃PointCoset :=
  (orbitEquivQuotientStabilizer F δ).trans
    ((cosetEquivMap h.marking (stabilizer F δ)).trans
      (quotientEquivOfEq h.first_marked))

theorem pointEquiv_apply_smul (f:F) :
    h.pointEquiv ⟨f•δ,mem_orbit δ f⟩=(h.marking f:PointCoset) := by
  have hh:(orbitEquivQuotientStabilizer F δ) ⟨f•δ,mem_orbit δ f⟩=
      (f:F⧸stabilizer F δ):=by
    apply (orbitEquivQuotientStabilizer F δ).symm.injective
    rw [Equiv.symm_apply_apply]
    exact Subtype.ext (orbitEquivQuotientStabilizer_symm_apply F δ f).symm
  change (quotientEquivOfEq h.first_marked)
    ((cosetEquivMap h.marking (stabilizer F δ))
      ((orbitEquivQuotientStabilizer F δ) ⟨f•δ,mem_orbit δ f⟩))=_
  rw [hh]
  rfl

theorem pointEquiv_smul (f:F) (v:orbit F δ) :
    h.pointEquiv (f•v)=h.marking f•h.pointEquiv v := by
  obtain ⟨k,hk⟩:=v.property
  have hv:v=⟨k•δ,mem_orbit δ k⟩:=Subtype.ext hk.symm
  subst v
  have he:f•(⟨k•δ,mem_orbit δ k⟩:orbit F δ)=⟨(f*k)•δ,mem_orbit δ (f*k)⟩:=
    Subtype.ext (mul_smul _ _ _).symm
  rw [he,h.pointEquiv_apply_smul,h.pointEquiv_apply_smul,map_mul]
  rfl

theorem pointEquiv_base : h.pointEquiv ⟨δ,mem_orbit_self δ⟩=(1:ReeF4.Model 0) := by
  simpa only [one_smul,map_one] using h.pointEquiv_apply_smul 1

/-- Half-incidence-distance labels on the unchanged first source orbit. -/
def localDistance (u v:orbit F δ) : Fin 5 :=
  ReeF4.Octagon.Binary.orderTwoFour.pointDistance (cosetPointEquiv (h.pointEquiv u))
    (cosetPointEquiv (h.pointEquiv v))

theorem localDistance_sphere_card (u:orbit F δ) (i:Fin 5) :
    Nat.card {v:orbit F δ // h.localDistance u v=i}=(![1,10,80,640,1024]:Fin 5→ℕ) i := by
  let e:=(h.pointEquiv).trans cosetPointEquiv
  have hh: {v:orbit F δ // h.localDistance u v=i}≃
      {v:ReeF4.Octagon.Binary.orderTwoFour.Point //
        ReeF4.Octagon.Binary.orderTwoFour.pointDistance (e u) v=i}:=
    e.subtypeEquiv (fun _=>Iff.rfl)
  rw [Nat.card_congr hh]
  exact ReeF4.Octagon.Binary.orderTwoFour.point_sphere_card (e u) i

theorem localDistance_eq_iff (u v:orbit F δ) (i:Fin 5) :
    h.localDistance u v=i ↔ pointDistance (h.pointEquiv u) (h.pointEquiv v)=2*(i:ℕ) := by
  rw [localDistance,ReeF4.Octagon.Binary.orderTwoFour.pointDistance_eq_iff]
  rfl

theorem localDistance_zero (u v:orbit F δ) : h.localDistance u v=0 ↔ u=v := by
  rw [localDistance,ReeF4.Octagon.Binary.orderTwoFour.pointDistance_zero]
  exact (cosetPointEquiv.injective.eq_iff).trans h.pointEquiv.injective.eq_iff

theorem localDistance_transitive (u v w:orbit F δ)
    (hd:h.localDistance u v=h.localDistance u w) :
    ∃f:F,f•u=u ∧ f•v=w := by
  have hd':pointDistance (h.pointEquiv u) (h.pointEquiv v)=
      pointDistance (h.pointEquiv u) (h.pointEquiv w):=by
    have hv:=(h.localDistance_eq_iff u v (h.localDistance u v)).mp rfl
    have hw:=(h.localDistance_eq_iff u w (h.localDistance u w)).mp rfl
    exact hv.trans ((congrArg (fun i:Fin 5=>2*(i:ℕ)) hd).trans hw.symm)
  obtain ⟨g,hgu,hgv⟩:=point_sphere_transitive _ _ _ hd'
  refine ⟨h.marking.symm g,h.pointEquiv.injective ?_,h.pointEquiv.injective ?_⟩
  · rw [h.pointEquiv_smul,h.marking.apply_symm_apply]; exact hgu
  · rw [h.pointEquiv_smul,h.marking.apply_symm_apply]; exact hgv

/-- The five distance classes are the actual first-parabolic suborbits. -/
theorem first_stabilizer_transitive (v w:orbit F δ)
    (hd:h.localDistance ⟨δ,mem_orbit_self δ⟩ v=
      h.localDistance ⟨δ,mem_orbit_self δ⟩ w) :
    ∃f:stabilizer F δ,f•v=w := by
  obtain ⟨f,hf,hvw⟩:=h.localDistance_transitive _ _ _ hd
  exact ⟨⟨f,congrArg Subtype.val hf⟩,hvw⟩

end CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
