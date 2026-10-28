module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Cyclic.Transport
public import Theory.Representation.BinaryOffender.InvolutionFixedKernel

/-!
# Cubic subgroups on a source offender plane

A three-subgroup of the actual conjugation image lifts from a Sylow subgroup
of its full preimage. Stabilization of the literal plane lifts to its ambient
normalizer, where the preceding residual conclusion forces centralization.
Inside an involution centralizer the pointwise kernel on its fixed space is
elementary abelian of exponent two. Hence a three-subgroup there is trivial.

Source: Aschbacher--Smith 15.2.13, printed pp.1111--1112, refs/quasithin.pdf.
Only the preceding plane and residual conclusions are assumed. These lemmas
also apply to the natural Omega branch; no restricted model is assumed.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
open Cyclic
variable {G : Type*} [Group G] [Finite G]

private theorem lift_three {D : Type*} [Group D]
    (f : G →* D) (hf : Function.Surjective f) (C : Subgroup D) (hp : IsPGroup 3 C) :
    ∃ X : Subgroup G, IsPGroup 3 X ∧ X.map f = C := by
  let L := C.comap f
  let q := f.subgroupComap C
  have hq := f.subgroupComap_surjective_of_surjective C hf
  let P : Sylow 3 L := Sylow.nonempty.some
  have ht : (P : Subgroup L).map q = ⊤ := by
    change (P.mapSurjective hq : Subgroup C) = ⊤
    exact top_unique ((hp.to_subgroup ⊤).le_sylow_of_normal _)
  refine ⟨(P : Subgroup L).map L.subtype, P.isPGroup'.map _, ?_⟩
  have he := congrArg (Subgroup.map C.subtype) ht
  rw [map_map, ← MonoidHom.range_eq_map, range_subtype] at he
  exact (map_map _ _ _).trans he

omit [Finite G] in
private theorem ambient_normalizer {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) (W : Submodule (ZMod 2) (Additive V))
    (X : Subgroup M)
    (hs : X.map (actionHom M V hn).rangeRestrict ≤
      subspaceStabilizer (imageRepresentation M V hn) W) :
    X.map M.subtype ≤ normalizer (ambientSpace V W : Set G) := by
  rintro _ ⟨x,hx,rfl⟩
  intro v
  constructor
  · rintro ⟨w,hw,rfl⟩
    let u : V := (actionHom M V hn) x w
    refine ⟨u,?_,rfl⟩
    exact (hs (mem_map_of_mem _ hx) (Additive.ofMul w)).2 hw
  · intro hv
    obtain ⟨w,hw,he⟩ := hv
    let u : V := (actionHom M V hn) x⁻¹ w
    have hu : (u : G) = v := by
      change (x : G)⁻¹ * (w : G) * ((x : G)⁻¹)⁻¹ = v
      change (w : G) = (x : G) * v * (x : G)⁻¹ at he
      rw [he]
      group
    refine ⟨u,?_,hu⟩
    exact (hs (mem_map_of_mem _ (X.inv_mem hx)) (Additive.ofMul w)).2 hw

/-- Every three-subgroup of the literal image stabilizing the source plane fixes it. -/
theorem three_image_plane_fixes {T : Sylow 2 G} {M Mc V E : Subgroup G}
    (h : ChosenSmallSource T M Mc V)
    (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hn : (T : Subgroup G) ≤ normalizer (E : Set G))
    (hbound : normalizer (E : Set G) ≤ Mc)
    (hres : threePrimeResidual Mc ≤ centralizer (centralInvolutions T : Set G)) :
    letI := h.prepared.elementary
    ∀ (W : Submodule (ZMod 2) (Additive V)), ambientSpace V W = E →
    ∀ C : Subgroup (internalActionImage M V h.prepared.normalized),
      IsPGroup 3 C → C ≤ subspaceStabilizer (imageRepresentation M V h.prepared.normalized) W →
      W ≤ fixedSpace (imageRepresentation M V h.prepared.normalized) C := by
  let := h.prepared.elementary
  intro W hWE C hp hs
  let f := (actionHom M V h.prepared.normalized).rangeRestrict
  obtain ⟨X,hX,he⟩ := lift_three f (actionHom M V h.prepared.normalized).rangeRestrict_surjective C hp
  have hXN : X.map M.subtype ≤ normalizer (E : Set G) := by
    rw [←hWE]
    exact ambient_normalizer h.prepared.normalized W X (he ▸ hs)
  have hXC := h.threeSubgroup_plane_normalizer_centralizes hEV hcard hn hbound hres
    (hX.map M.subtype) hXN
  intro v hv c
  have hcX : (c : internalActionImage M V h.prepared.normalized) ∈ X.map f :=
    he.symm ▸ c.property
  obtain ⟨x,hx,hxc⟩ := hcX
  have hev : (v.toMul : G) ∈ E := hWE ▸ (mem_ambientSpace W v.toMul).mpr hv
  have hc := hXC (mem_map_of_mem M.subtype hx) (v.toMul : G) hev
  change imageRepresentation M V h.prepared.normalized (c : internalActionImage M V _) v = v
  rw [←hxc]
  apply Additive.toMul.injective
  apply Subtype.ext
  change (x : G) * (v.toMul : G) * (x : G)⁻¹ = v.toMul
  change (v.toMul : G) * (x : G) = (x : G) * (v.toMul : G) at hc
  rw [←hc,mul_inv_cancel_right]

/-- A cubic image centralizing a source involution is trivial. -/
theorem three_image_centralizer_eq_bot {T : Sylow 2 G} {M Mc V E : Subgroup G}
    (h : ChosenSmallSource T M Mc V)
    (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hn : (T : Subgroup G) ≤ normalizer (E : Set G))
    (hbound : normalizer (E : Set G) ≤ Mc)
    (hres : threePrimeResidual Mc ≤ centralizer (centralInvolutions T : Set G)) :
    letI := h.prepared.elementary
    ∀ (t : internalActionImage M V h.prepared.normalized), t ^ 2 = 1 →
      ambientSpace V (fixedSpace (imageRepresentation M V h.prepared.normalized)
        (zpowers t)) = E →
    ∀ C : Subgroup (internalActionImage M V h.prepared.normalized),
      IsPGroup 3 C → C ≤ centralizer {t} → C = ⊥ := by
  let := h.prepared.elementary
  intro t ht hE C hp hC
  let ρ := imageRepresentation M V h.prepared.normalized
  have hs : C ≤ subspaceStabilizer ρ (fixedSpace ρ (zpowers t)) := by
    apply le_subspaceStabilizer
    intro g hg v hv
    rw [mem_fixedSpace_zpowers_iff] at hv ⊢
    rw [← Module.End.mul_apply, ← map_mul,
      ← mem_centralizer_singleton_iff.mp (hC hg), map_mul, Module.End.mul_apply, hv]
  have hfix := three_image_plane_fixes h hEV hcard hn hbound hres _ hE C hp hs
  let := involutionFixedKernel_elementary ρ (imageRepresentation_injective _ _ _) t ht
  have hle : C ≤ involutionFixedKernel ρ t := by
    intro c hc
    exact ⟨hC hc, fun v hv => hfix hv ⟨c,hc⟩⟩
  have hp2 : IsPGroup 2 C :=
    (IsElementaryAbelian.isPGroup 2 (involutionFixedKernel ρ t)).to_le hle
  have he := IsPGroup.disjoint_of_ne 2 3 (by decide) C C hp2 hp
  exact disjoint_self.mp he

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
