module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Pointwise
/-!
# Internal conjugators preserving a prescribed Sylow image

Choose a pair of conjugates with minimal generated-subgroup order among pairs
having the prescribed quotient image. Sylow conjugacy inside this subgroup
replaces the external conjugator by an internal one without changing the
quotient image. Minimality then preserves the whole generated subgroup.
This is the rechoice step in Aschbacher–Smith E.2.9, printed p.221.
-/
public section
namespace Subgroup
open scoped Pointwise
variable {G D : Type*} [Group G] [Finite G] [Group D]

omit [Finite G] in
private theorem map_conjugate_join (f : G →* D) (V : Subgroup G) (g : G) :
    (V ⊔ V.map (MulAut.conj g).toMonoidHom).map f =
      V.map f ⊔ (V.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_sup, map_map, map_map]
  congr 2
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

/-- If a p-subgroup has Sylow image, a generated pair with prescribed full
image can be chosen with its conjugator inside the generated subgroup. -/
theorem exists_internal_conjugator_of_sylow_image {p : ℕ} [Fact p.Prime]
    (f : G →* D) (V : Subgroup G) (hVp : IsPGroup p V)
    (S : Sylow p D) (hVS : V.map f = S)
    (hex : ∃ g : G, (V ⊔ V.map (MulAut.conj g).toMonoidHom).map f = ⊤) :
    ∃ g : G, g ∈ V ⊔ V.map (MulAut.conj g).toMonoidHom ∧
      (V ⊔ V.map (MulAut.conj g).toMonoidHom).map f = ⊤ := by
  classical
  let pair (g : G) := V ⊔ V.map (MulAut.conj g).toMonoidHom
  let good : Set G := {g | (pair g).map f = ⊤}
  obtain ⟨g, hg, hmin⟩ := Set.exists_min_image good (fun x => Nat.card (pair x))
    (Set.toFinite _) hex
  let I := pair g
  let q := f.comp I.subtype
  have hq : Function.Surjective q := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, range_subtype]
    exact hg
  let W := V.map (MulAut.conj g).toMonoidHom
  have hVI : V ≤ I := le_sup_left
  have hWI : W ≤ I := le_sup_right
  obtain ⟨P,hP⟩ := hVp.comap_subtype.exists_le_sylow (P := V.subgroupOf I)
  have hWp : IsPGroup p W := hVp.map _
  obtain ⟨R,hR⟩ := hWp.comap_subtype.exists_le_sylow (P := W.subgroupOf I)
  have hPV : (P : Subgroup I).map q = V.map f := by
    have hVP : V.map f ≤ (P : Subgroup I).map q := by
      have hh := map_mono (f := q) hP
      simpa only [q, ← map_map, map_subgroupOf_eq_of_le hVI] using hh
    exact (S.is_maximal' (P.isPGroup'.map q) (hVS ▸ hVP)).trans hVS.symm
  have hRW : (R : Subgroup I).map q = W.map f := by
    let Sg := (MulAut.conj (f g)) • S
    have hWS : W.map f = (Sg : Subgroup D) := by
      dsimp only [W]
      rw [map_map]
      change V.map _ = (S : Subgroup D).map (MulAut.conj (f g)).toMonoidHom
      rw [← hVS]
      rw [map_map]
      congr 1
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
    have hWR : W.map f ≤ (R : Subgroup I).map q := by
      have hh := map_mono (f := q) hR
      simpa only [q, ← map_map, map_subgroupOf_eq_of_le hWI] using hh
    exact (Sg.is_maximal' (R.isPGroup'.map q) (hWS ▸ hWR)).trans hWS.symm
  obtain ⟨x,hx⟩ := MulAction.exists_smul_eq I P R
  have hconj : (V.map f).map (MulAut.conj (f (x : G))).toMonoidHom = W.map f := by
    rw [← hPV, ← hRW, map_map]
    have hx' : (P : Subgroup I).map (MulAut.conj x).toMonoidHom = (R : Subgroup I) :=
      congrArg Sylow.toSubgroup hx
    rw [← hx', map_map]
    congr 1
    ext a
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
    rfl
  have hxgood : (x : G) ∈ good := by
    change (pair (x : G)).map f = ⊤
    dsimp only [pair]
    rw [map_conjugate_join, hconj, ← Subgroup.map_sup]
    exact hg
  have hpair : pair (x : G) ≤ I := by
    refine sup_le hVI ?_
    rintro a ⟨v,hv,rfl⟩
    exact I.mul_mem (I.mul_mem x.property (hVI hv)) (I.inv_mem x.property)
  have he : pair (x : G) = I := eq_of_le_of_card_ge hpair (hmin x hxgood)
  refine ⟨x, ?_, hxgood⟩
  change (x : G) ∈ pair (x : G)
  rw [he]
  exact x.property
end Subgroup
