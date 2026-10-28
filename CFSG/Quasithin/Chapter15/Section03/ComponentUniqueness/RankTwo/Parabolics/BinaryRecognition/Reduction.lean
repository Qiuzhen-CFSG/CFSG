module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Models
public import Theory.SpecificGroups.BinaryLinear.FourParabolicRadical
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Quotient and coordinate reductions for binary parabolic recognition

The binary PSL predicates give genuine natural-action models after transporting
their specified coefficient field to F₂. For a self-centralizing normal
component D generating the ambient group with S, inner action by S forces D
to be the whole ambient group. These observations reduce the recognition in
the last paragraph of 15.3.35 to the actual binary linear models.

Once geometric recognition supplies a two-plane stabilizer, extend an
isomorphism of two-planes to the whole vector space. Conjugation by this
linear equivalence carries the stabilizer to the fixed plane used by
`FourParabolicRadical`, retaining the subgroup marking under the original
centralizer-quotient map.

The graph-action exclusion and geometric recognition are separate obligations.
No theorem here supplies either one. In particular, a small binary model alone
does not produce the marked equivalence required by `no_endNodeParabolic`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final paragraph
of the proof of 15.3.35, printed p.1139. Coefficient-field transport uses the
attributed ATLAS port `Theory.AtlasPort.ExceptionalIsomorphisms.Support`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.BinaryRecognition
open BinaryLinear.OuterCyclic
variable {G X : Type*} [Group G] [Group X]

/-- Replace the field witness in `IsPSL` by the actual natural binary model. -/
theorem exists_binary_linear_equiv {n : ℕ} (hn : 0 < n)
    (h : ClassicalGroup.IsPSL X n 2) : Nonempty (X ≃* LinearGroup n) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let _ := Fintype.ofFinite F
  let f : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact ⟨e.trans ((Atlas.fieldEquivPSL n f.symm).trans (projectiveEquivLinear hn))⟩

/-- Both alternatives carry concrete binary matrix equivalences. -/
theorem smallBinaryModel_linear (h : SmallBinaryModel X) :
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ Nonempty (X ≃* LinearGroup n) := by
  rcases h with h | h
  · exact ⟨4, Or.inl rfl, exists_binary_linear_equiv (by decide) h⟩
  · exact ⟨5, Or.inr rfl, exists_binary_linear_equiv (by decide) h⟩

/-- A self-centralizing component and an inner-acting supplement generate
only the component. The supplement need not be a Sylow subgroup here. -/
theorem eq_top_of_inner_action (D S : Subgroup X) [D.Normal]
    (hc : centralizer (D : Set X) = ⊥) (hgen : D ⊔ S = ⊤)
    (hinner : ∀ s ∈ S, MulAut.conjNormal (H := D) s ∈ MulAut.innerSubgroup D) :
    D = ⊤ := by
  have hSD : S ≤ D := by
    intro s hs
    have h : s ∈ (MulAut.innerSubgroup D).comap MulAut.conjNormal := hinner s hs
    rwa [MulAut.conjNormal_comap_innerSubgroup, hc, sup_bot_eq] at h
  rw [sup_eq_left.mpr hSD] at hgen
  exact hgen

/-- Generation by L and S survives the actual centralizer quotient. -/
theorem component_join_eq_top (L S : Subgroup G) [L.Normal]
    (hgen : L ⊔ S = ⊤) :
    centralizerQuotientComponent L ⊔ S.map (centralizerQuotientMap L) = ⊤ := by
  change L.map (centralizerQuotientMap L) ⊔ S.map (centralizerQuotientMap L) = _
  rw [← Subgroup.map_sup, hgen]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

/-- Extend a component model to the ambient group once the component is all of it. -/
noncomputable def ambientEquivOfComponentEqTop (D : Subgroup X) (hD : D = ⊤)
    {A : Type*} [Group A] (e : D ≃* A) : X ≃* A :=
  (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hD.symm)).trans e

/-- The extended equivalence retains the original component marking. -/
@[simp] theorem ambientEquivOfComponentEqTop_apply (D : Subgroup X) (hD : D = ⊤)
    {A : Type*} [Group A] (e : D ≃* A) (x : D) :
    ambientEquivOfComponentEqTop D hD e x = e x := rfl

private def planeEquiv : BinaryLinear.FourParabolicRadical.Vec ≃ₗ[ZMod 2]
    BinaryLinear.FourParabolicRadical.plane where
  toFun v := ⟨(v, 0), rfl⟩
  invFun v := v.val.1
  left_inv _ := rfl
  right_inv v := by
    apply Subtype.ext
    exact Prod.ext rfl (by exact v.property.symm)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The fixed plane in the radical model has dimension two. -/
theorem finrank_plane :
    Module.finrank (ZMod 2) BinaryLinear.FourParabolicRadical.plane = 2 := by
  rw [← planeEquiv.finrank_eq]
  exact Module.finrank_fin_fun (ZMod 2)

private theorem map_parabolic {V U : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup U] [Module (ZMod 2) U]
    (e : V ≃ₗ[ZMod 2] U) (W : Submodule (ZMod 2) V) :
    (BinaryLinear.parabolic W).map
        (BinaryLinear.SmallParabolicLevi.linearGroupCongr e).toMonoidHom =
      BinaryLinear.parabolic (W.map e.toLinearMap) := by
  have hmem (x : U) : x ∈ W.map e.toLinearMap ↔ e.symm x ∈ W := by
    constructor
    · rintro ⟨v, hv, rfl⟩
      change e.symm (e v) ∈ W
      rw [e.symm_apply_apply]
      exact hv
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  ext g
  rw [Subgroup.mem_map_equiv]
  change (∀ v, e.symm (g (e v)) ∈ W ↔ v ∈ W) ↔
    ∀ x, g x ∈ W.map e.toLinearMap ↔ x ∈ W.map e.toLinearMap
  constructor
  · intro hg x
    rw [hmem, hmem]
    simpa only [e.apply_symm_apply] using hg (e.symm x)
  · intro hg v
    simpa only [hmem, e.symm_apply_apply] using hg (e v)

private theorem exists_plane_coordinates
    (W : Submodule (ZMod 2) (Space 4)) (hW : Module.finrank (ZMod 2) W = 2) :
    ∃ e : Space 4 ≃ₗ[ZMod 2] BinaryLinear.FourParabolicRadical.Space,
      W.map e.toLinearMap = BinaryLinear.FourParabolicRadical.plane := by
  let a := BinaryLinear.FourParabolicRadical.spaceEquiv.symm
  let U := W.map a.toLinearMap
  have hU : Module.finrank (ZMod 2) U = 2 := by
    rw [← (a.submoduleMap W).finrank_eq]
    exact hW
  let f : U ≃ₗ[ZMod 2] BinaryLinear.FourParabolicRadical.plane :=
    LinearEquiv.ofFinrankEq _ _ (hU.trans finrank_plane.symm)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨a.trans g, ?_⟩
  have hmap : U.map g.toLinearMap = BinaryLinear.FourParabolicRadical.plane := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hg ⟨x, hx⟩ ▸ (f ⟨x, hx⟩).property
    · intro x hx
      obtain ⟨u, hu⟩ := f.surjective ⟨x, hx⟩
      exact ⟨u, u.property, (hg u).symm.trans (congrArg Subtype.val hu)⟩
  change (W.map a.toLinearMap).map g.toLinearMap = _ at hmap
  rw [← Submodule.map_comp] at hmap
  exact hmap

/-- Geometric recognition of a two-plane stabilizer gives the literal fixed
parabolic marking, through an explicitly constructed coordinate change. -/
theorem exists_marked_equiv_of_plane (J : Subgroup X)
    (e : X ≃* LinearGroup 4) (W : Submodule (ZMod 2) (Space 4))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hJ : J.map e.toMonoidHom = BinaryLinear.parabolic W) :
    ∃ a : X ≃* BinaryLinear.FourParabolicRadical.Lin,
      J.map a.toMonoidHom =
        BinaryLinear.parabolic BinaryLinear.FourParabolicRadical.plane := by
  obtain ⟨b, hb⟩ := exists_plane_coordinates W hW
  refine ⟨e.trans (BinaryLinear.SmallParabolicLevi.linearGroupCongr b), ?_⟩
  change J.map ((BinaryLinear.SmallParabolicLevi.linearGroupCongr b).toMonoidHom.comp
    e.toMonoidHom) = _
  rw [← Subgroup.map_map, hJ, map_parabolic, hb]

/-- Compose the recognized plane marking with the original quotient map.
This is the exact marked output used by the final radical contradiction;
the geometric plane recognition remains an explicit premise here. -/
theorem exists_quotient_marking_of_plane (L Yplus S : Subgroup G) [L.Normal]
    (e : CentralizerQuotient L ≃* LinearGroup 4)
    (W : Submodule (ZMod 2) (Space 4)) (hW : Module.finrank (ZMod 2) W = 2)
    (hJ : ((Yplus ⊔ S).map (centralizerQuotientMap L)).map e.toMonoidHom =
      BinaryLinear.parabolic W) :
    ∃ a : CentralizerQuotient L ≃* BinaryLinear.FourParabolicRadical.Lin,
      (Yplus ⊔ S).map (a.toMonoidHom.comp (centralizerQuotientMap L)) =
        BinaryLinear.parabolic BinaryLinear.FourParabolicRadical.plane := by
  obtain ⟨a, ha⟩ := exists_marked_equiv_of_plane _ e W hW hJ
  exact ⟨a, by simpa only [Subgroup.map_map] using ha⟩

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.BinaryRecognition
