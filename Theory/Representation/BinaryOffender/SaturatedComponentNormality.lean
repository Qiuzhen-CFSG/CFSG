module
public import Theory.Representation.BinaryOffender.SubgroupMovedDimension
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryOffender.ComponentSeedNormality
public import Theory.Representation.CyclicFixedRank

/-!
# Saturated displacement and component normalization

If conjugates of an element generate over a perfect moving subgroup, a
near-sharp dimension bound forces its displacement on the entire space to
equal its displacement on the invariant commutator space. For an Irr⁺
component commutator, a conjugate component would centralize that space.
Consequently the element centralizer normalizes the original component.

Source application: Aschbacher--Smith, proof of 12.6.26, printed p.833.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A strict dimension bound makes restriction preserve the entire displacement. -/
theorem commutator_eq_of_saturated_conjugate_bound
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) (I : Submodule (ZMod 2) V)
    (hKI : K ≤ subspaceStabilizer ρ I) (hfull : subspaceCommutator ρ I K = I)
    (v : G) (hvI : v ∈ subspaceStabilizer ρ I) {n r : ℕ} (c : Fin n → K)
    (hgen : K ≤ ⨆ i, (zpowers v).map (MulAut.conj (c i : G)).toMonoidHom)
    (hlow : n * (r - 1) < Module.finrank (ZMod 2) I)
    (hhigh : Module.finrank (ZMod 2) (ρ v - LinearMap.id).range ≤ r) :
    subspaceCommutator ρ I (zpowers v) = subspaceCommutator ρ ⊤ (zpowers v) := by
  let A := subspaceStabilizer ρ I
  let τ := stabilizerRepresentation ρ I
  let K' := K.subgroupOf A
  let v' : A := ⟨v,hvI⟩
  let c' (i : Fin n) : A := ⟨c i,hKI (c i).property⟩
  have hmap (i : Fin n) :
      ((zpowers v').map (MulAut.conj (c' i)).toMonoidHom).map A.subtype =
        (zpowers v).map (MulAut.conj (c i : G)).toMonoidHom := by
    rw [map_map,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    rfl
  have hgen' : K' ≤ ⨆ i, (zpowers v').map (MulAut.conj (c' i)).toMonoidHom := by
    apply (map_le_map_iff_of_injective A.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hKI,Subgroup.map_iSup]
    simpa only [hmap] using hgen
  have hm : subspaceCommutator τ ⊤ K' = ⊤ := by
    have hh := subspaceCommutator_map_embedding (ρ.comp A.subtype) τ (MonoidHom.id A)
      I.subtype (fun _ _ => rfl) K' ⊤
    rw [Submodule.map_top,Submodule.range_subtype,Subgroup.map_id,
      subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hKI,hfull] at hh
    apply Submodule.map_injective_of_injective I.subtype_injective
    rw [Submodule.map_top,Submodule.range_subtype]
    exact hh.symm
  have hd := moved_finrank_le_mul_displacement_of_conjugates τ K' v' c' hgen'
  rw [hm,finrank_top] at hd
  let j : (τ v' - LinearMap.id).range →ₗ[ZMod 2] (ρ v - LinearMap.id).range := {
    toFun x := ⟨x.val.val, by
      obtain ⟨y,hy⟩ := x.property
      exact ⟨y.val,congrArg Subtype.val hy⟩⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : (ρ v - LinearMap.id).range => w.val) he
  have hdim : Module.finrank (ZMod 2) (τ v' - LinearMap.id).range =
      Module.finrank (ZMod 2) (ρ v - LinearMap.id).range := by
    apply le_antisymm (LinearMap.finrank_le_finrank_of_injective hj)
    by_contra hh
    have hle : Module.finrank (ZMod 2) (τ v' - LinearMap.id).range ≤ r-1 := by omega
    have hmul := Nat.mul_le_mul_left n hle
    exact (not_lt_of_ge (hd.trans hmul)) hlow
  have hjs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hj
  apply le_antisymm (subspaceCommutator_mono_left ρ le_top (zpowers v))
  rw [Representation.CyclicFixedRank.commutator_eq_range]
  intro x hx
  obtain ⟨y,hy⟩ := hjs ⟨x,hx⟩
  obtain ⟨w,hw⟩ := y.property
  have he : ρ v w.val - w.val = x :=
    (congrArg Subtype.val hw).trans (congrArg Subtype.val hy)
  exact he ▸ Submodule.subset_span ⟨v,mem_zpowers v,w.val,w.property,rfl⟩

/-- The saturated displacement lies inside the invariant moving space. -/
theorem range_le_of_saturated_conjugate_bound
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) (I : Submodule (ZMod 2) V)
    (hKI : K ≤ subspaceStabilizer ρ I) (hfull : subspaceCommutator ρ I K = I)
    (v : G) (hvI : v ∈ subspaceStabilizer ρ I) {n r : ℕ} (c : Fin n → K)
    (hgen : K ≤ ⨆ i, (zpowers v).map (MulAut.conj (c i : G)).toMonoidHom)
    (hlow : n * (r - 1) < Module.finrank (ZMod 2) I)
    (hhigh : Module.finrank (ZMod 2) (ρ v - LinearMap.id).range ≤ r) :
    (ρ v - LinearMap.id).range ≤ I := by
  rw [←Representation.CyclicFixedRank.commutator_eq_range,
    ←commutator_eq_of_saturated_conjugate_bound ρ K I hKI hfull v hvI c hgen hlow hhigh]
  exact subspaceCommutator_le_of_invariant ρ (zpowers_le.mpr hvI)

/-- A displacement contained in an Irr⁺ component commutator prevents the
involution centralizer from permuting that component. -/
theorem component_normalized_by_centralizer_of_moved_containment [Finite G]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (K : Subgroup G) (hK : Theory.GroupTheory.IsComponent G K)
    (hi : IsIrrPlus ρ K (subspaceCommutator ρ ⊤ K))
    (v : G) (hc : ⁅K,zpowers v⁆ = K)
    (hm : (ρ v - LinearMap.id).range ≤ subspaceCommutator ρ ⊤ K) :
    centralizer ({v} : Set G) ≤ normalizer (K : Set G) := by
  let := hK.2
  have hKn : K ≠ ⊥ := by
    intro he
    apply hi.not_le_fixedSpace ρ
    rw [he]
    simp
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hne
  let J := K.map (MulAut.conj g).toMonoidHom
  have hJ : Theory.GroupTheory.IsComponent G J := hK.map_conj g
  let := hJ.2
  have hJK : J ≤ centralizer (K : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hJ.commutator_eq_bot_of_ne hK hne)
  have hfix : subspaceCommutator ρ ⊤ K ≤ fixedSpace ρ J :=
    hi.le_fixedSpace_of_perfect_centralizes ρ hJK
      (subspaceCommutator_invariant_normalizer ρ
        (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
        (hJK.trans (Subgroup.centralizer_le_normalizer _)))
  have hgv : g*v=v*g := mem_centralizer_singleton_iff.mp hg
  have hgf : ∀ x ∈ (ρ v - LinearMap.id).range, ρ g x ∈ (ρ v - LinearMap.id).range := by
    rintro _ ⟨y,rfl⟩
    refine ⟨ρ g y,?_⟩
    change ρ v (ρ g y) - ρ g y = ρ g (ρ v y - y)
    rw [map_sub]
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul,hgv]
  have hfixed : (ρ v - LinearMap.id).range ≤ fixedSpace ρ K := by
    intro x hx k
    have he := hfix (hm (hgf x hx))
      ⟨g*k.val*g⁻¹,mem_map_of_mem (MulAut.conj g).toMonoidHom k.property⟩
    change ρ (g*k.val*g⁻¹) (ρ g x)=ρ g x at he
    have hh := congrArg (ρ g⁻¹) he
    change ρ k.val x = x
    simpa only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel_left,
      inv_mul_cancel,mul_one,map_one,Module.End.one_apply] using hh
  apply moved_not_fixed_of_perfect_commutator ρ hf hKn hc
  rwa [Representation.CyclicFixedRank.commutator_eq_range]
end Representation.BinaryOffender
