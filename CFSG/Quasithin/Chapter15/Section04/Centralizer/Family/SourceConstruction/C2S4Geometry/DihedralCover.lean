module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.C2S4Geometry.DihedralCover.Model

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.C2S4Geometry.Basic
public import Theory.GroupTheory.SylowKernelCore

/-!
# The local dihedral cover for Lemma 15.4.13

Given an actual equivalence XT ≃ C₂ × S₄, conjugate the image of the supplied
Sylow subgroup to the square-action Sylow. This gives compatible ambient and
Sylow coordinates. The identity-first-coordinate D₈ then supplies the
reflection t, the central involution z, and the index-two subgroup R.

Two-perfectness and T-invariance identify X with O²(XT). Transporting the
model residual-core calculation through the same ambient coordinates proves
R = ⟨t⟩O₂(X). The two model involution classes transport inside the literal XT,
with its subtype inclusions retained. No simplicity or exclusion hypothesis
is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 15.4.13, printed p.1161. This constructs the `DihedralCover` consumed
by the parent's transfer and missing-class theorems.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.C2S4Geometry

private theorem aligned_coordinates {H : Type*} [Group H] [Finite H]
    (U : Sylow 2 H) (e : H ≃* CoverModel.M) :
    ∃ f : H ≃* CoverModel.M, ∃ a : U ≃* CoverModel.S,
      ∀ u : U, f (u : H) = CoverModel.j (a u) := by
  classical
  let W := U.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq CoverModel.M W CoverModel.sylow
  let f := e.trans (MulAut.conj g)
  have hm : (U : Subgroup H).map f.toMonoidHom = CoverModel.j.range := by
    calc
      _ = (W : Subgroup CoverModel.M).map (MulAut.conj g).toMonoidHom := by
        change (U : Subgroup H).map f.toMonoidHom =
          ((U : Subgroup H).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom
        rw [map_map]; rfl
      _ = ((g • W : Sylow 2 CoverModel.M) : Subgroup CoverModel.M) := rfl
      _ = CoverModel.j.range := congrArg Sylow.toSubgroup hg
  let a₀ := (f.subgroupMap (U : Subgroup H)).trans (MulEquiv.subgroupCongr hm)
  refine ⟨f, a₀.trans (MonoidHom.ofInjective CoverModel.j_injective).symm, ?_⟩
  intro u
  exact (MonoidHom.apply_ofInjective_symm CoverModel.j_injective (a₀ u)).symm

variable {G : Type*} [Group G] [Finite G]

/-- The dihedral subgroup and its two involution classes inside the actual XT. -/
theorem exists_dihedralCover (T : Sylow 2 G) (X : Subgroup G)
    (hp : IsPPerfect 2 X) (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (e : (X ⊔ (T : Subgroup G) : Subgroup G) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) :
    Nonempty (DihedralCover T X) := by
  classical
  let H := X ⊔ (T : Subgroup G)
  let hTH : (T : Subgroup G) ≤ H := le_sup_right
  let i : T →* H := inclusion hTH
  obtain ⟨f,a₀,ha₀⟩ := aligned_coordinates (T.subtype hTH) e
  let a : T ≃* CoverModel.S := (subgroupOfEquivOfLe hTH).symm.trans a₀
  have ha (u : T) : f (i u) = CoverModel.j (a u) :=
    ha₀ ((subgroupOfEquivOfLe hTH).symm u)
  let b : CoverModel.M →* G := H.subtype.comp f.symm.toMonoidHom
  have hb : b.comp f.toMonoidHom = H.subtype := by
    ext u
    simp [b]
  have hbj : b.comp CoverModel.j = (T : Subgroup G).subtype.comp a.symm.toMonoidHom := by
    ext u
    have h := congrArg f.symm (ha (a.symm u))
    simp only [f.symm_apply_apply, a.apply_symm_apply] at h
    exact congrArg H.subtype h.symm
  have hcore : ((pResidual 2 H).pCoreIn 2).map f.toMonoidHom = CoverModel.B := by
    rw [map_pCoreIn_of_injective 2 _ _ f.injective, map_pResidual, CoverModel.residual_core]
  have hB : CoverModel.B.map b = X.pCoreIn 2 := by
    rw [← hcore, map_map, hb, map_pCoreIn_of_injective 2 _ _ H.subtype_injective]
    rw [embedded_residual_eq_member T X hp hn]
  let R' := CoverModel.R.map a.symm.toMonoidHom
  refine ⟨{
    t := a.symm CoverModel.t
    z := a.symm CoverModel.z
    R := R'
    t_order := (a.symm.orderOf_eq _).trans CoverModel.t_order
    t_outside_core := ?_
    z_order := (a.symm.orderOf_eq _).trans CoverModel.z_order
    z_mem_frattini := ?_
    R_eq := ?_
    R_index := ?_
    R_equiv := ?_
    center_inter := ?_
    cover := ?_
  }⟩
  · intro ht
    apply CoverModel.t_outside_core
    rw [← pCore_map_iso 2 f]
    refine ⟨i (a.symm CoverModel.t), ?_, ?_⟩
    · obtain ⟨u,hu,he⟩ := ht
      have hEq : u = i (a.symm CoverModel.t) := Subtype.ext he
      exact hEq ▸ hu
    · simpa only [MulEquiv.apply_symm_apply, MulEquiv.coe_toMonoidHom] using ha (a.symm CoverModel.t)
  · rw [← frattini_map_equiv a.symm]
    exact mem_map.mpr ⟨CoverModel.z, CoverModel.z_mem_frattini, rfl⟩
  · change (CoverModel.R.map a.symm.toMonoidHom).map (T : Subgroup G).subtype = _
    have hm : (CoverModel.R.map a.symm.toMonoidHom).map (T : Subgroup G).subtype =
        (CoverModel.R.map CoverModel.j).map b := by
      rw [map_map, map_map, hbj]
    rw [hm, CoverModel.R_image, Subgroup.map_sup, MonoidHom.map_zpowers, hB]
    have he := DFunLike.congr_fun hbj CoverModel.t
    exact congrArg (fun x : G => zpowers x ⊔ X.pCoreIn 2) he
  · exact (index_map_equiv CoverModel.R a.symm).trans CoverModel.index_R
  · exact ⟨(CoverModel.R.equivMapOfInjective a.symm.toMonoidHom a.symm.injective).symm.trans
      CoverModel.rEquiv⟩
  · change center T ⊓ CoverModel.R.map a.symm.toMonoidHom = frattini T
    rw [← center_map_equiv a.symm, ← map_inf _ _ _ a.symm.injective,
      CoverModel.center_inter, frattini_map_equiv]
  · intro r hr ho
    have hmem : a r ∈ CoverModel.R := by
      obtain ⟨u,hu,he⟩ := hr
      have he' : u = a r := by
        simpa only [MulEquiv.coe_toMonoidHom, a.apply_symm_apply] using congrArg a he
      exact he' ▸ hu
    have horder : orderOf (a r) = 2 := (a.orderOf_eq r).trans ho
    have h := CoverModel.cover (a r) hmem horder
    have htransfer (q : CoverModel.S) (h : IsConj (CoverModel.j (a r)) (CoverModel.j q)) :
        IsConj (i r) (i (a.symm q)) := by
      have hh := f.symm.toMonoidHom.map_isConj h
      have h1 : f.symm (CoverModel.j (a r)) = i r := by rw [← ha, f.symm_apply_apply]
      have h2 : f.symm (CoverModel.j q) = i (a.symm q) := by
        have hh := ha (a.symm q)
        rw [a.apply_symm_apply] at hh
        rw [← hh, f.symm_apply_apply]
      simpa only [MulEquiv.coe_toMonoidHom, h1, h2] using hh
    exact h.imp (htransfer CoverModel.t) (htransfer CoverModel.z)

end CFSG.Quasithin.Chapter15.Section04.FamilySource.C2S4Geometry
