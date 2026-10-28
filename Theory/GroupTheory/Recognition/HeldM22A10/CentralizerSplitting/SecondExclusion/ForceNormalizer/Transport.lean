module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Ambient

/-!
# Transport of the second Held candidate assertion

Every subgroup of the embedded model Sylow pulls back to a model subgroup,
with an actual multiplicative equivalence to its image. Relative centricity
and intrinsic radicality pull back through this embedding. For radicality,
conjugation of automorphisms along that equivalence preserves both the two-core
and the inner automorphisms. Characteristic intersections with the transfer
subgroup then move forward, and the exceptional alternative becomes equality
with the specified ambient exceptional subgroup.

This is the conditional transport used in the transfer proof for
Huppert--Blackburn III, XII.1.18(b), p.314 (citing Held, J. Algebra 8 (1968),
436--449). The concrete `CandidateProperty` remains an explicit input; its
proof and the final exclusion belong to the assembly owner.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer

private theorem centric_of_map_injective
    {H K : Type*} [Group H] [Group K] (f : H →* K) (hf : Function.Injective f)
    (S U : Subgroup H)
    (hc : S.map f ⊓ centralizer (U.map f : Set K) ≤ U.map f) :
    S ⊓ centralizer (U : Set H) ≤ U := by
  intro x hx
  apply (mem_map_iff_mem hf).mp
  apply hc
  refine ⟨mem_map_of_mem f hx.1, ?_⟩
  apply mem_centralizer_iff.mpr
  rintro _ ⟨y, hy, rfl⟩
  simpa only [map_mul] using congrArg f (mem_centralizer_iff.mp hx.2 y hy)

private theorem intrinsicRadicalIn_of_map_injective
    {H K : Type*} [Group H] [Group K] (f : H →* K) (hf : Function.Injective f)
    (S U : Subgroup H) (hrad : IntrinsicRadicalIn (S.map f) (U.map f)) :
    IntrinsicRadicalIn S U := by
  let V := U.map f
  let u : U ≃* V := U.equivMapOfInjective f hf
  let a := MulAut.congr u
  rintro b ⟨⟨g, hg, rfl⟩, hp⟩
  have hnorm : f g ∈ normalizer (V : Set K) :=
    le_normalizer_map f (mem_map_of_mem f g.property)
  let g' : normalizer (V : Set K) := ⟨f g, hnorm⟩
  have hact : a (U.normalizerMonoidHom g) = V.normalizerMonoidHom g' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨x, rfl⟩ := u.surjective x
    apply Subtype.ext
    change f (g * (u.symm (u x) : U) * (g : H)⁻¹) = f g * f x * (f g)⁻¹
    rw [u.symm_apply_apply, map_mul, map_mul, map_inv]
  have haP : a (U.normalizerMonoidHom g) ∈ pCore 2 (MulAut V) := by
    rw [← pCore_map_iso 2 a]
    exact mem_map_of_mem a.toMonoidHom hp
  obtain ⟨v, hv⟩ := hrad ⟨⟨g', mem_map_of_mem f hg, hact.symm⟩, haP⟩
  refine ⟨u.symm v, a.injective ?_⟩
  rw [← hv]
  apply MulEquiv.ext
  intro x
  change u (u.symm v * u.symm x * (u.symm v)⁻¹) = v * x * v⁻¹
  simp only [map_mul, map_inv, u.apply_symm_apply]

private theorem characteristic_subgroupOf_map_injective
    {H K : Type*} [Group H] [Group K] (f : H →* K) (hf : Function.Injective f)
    (M U : Subgroup H) (hc : (M.subgroupOf U).Characteristic) :
    ((M.map f).subgroupOf (U.map f)).Characteristic := by
  let u := U.equivMapOfInjective f hf
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y, rfl⟩ := u.surjective x
  have hy : y ∈ M.subgroupOf U := (mem_map_iff_mem hf).mp hx
  have ha := characteristic_iff_le_comap.mp hc (MulAut.congr u.symm a) hy
  have htrans : u (MulAut.congr u.symm a y) = a (u y) := by
    change u (u.symm (a (u y))) = a (u y)
    exact u.apply_symm_apply _
  change a (u y) ∈ (M.map f).subgroupOf (U.map f)
  rw [← htrans]
  exact mem_map_of_mem f ha

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
    (e : D.centralizer ≃* NonsplitModels.Second)

/-- Transport the concrete candidate assertion through the actual centralizer
embedding. No normalizer-control or simplicity hypothesis is needed. -/
public theorem ambient_candidates_of_candidates (h : CandidateProperty) :
    AmbientCandidateProperty D e := by
  intro U hUS hcent hrad
  let f := embedding D e
  have hf := embedding_injective D e
  let R := U.comap f
  change Model.sylowSubgroup.map f ⊓ centralizer (U : Set G) ≤ U at hcent
  change IntrinsicRadicalIn (Model.sylowSubgroup.map f) U at hrad
  have hmap : R.map f = U :=
    map_comap_eq_self (hUS.trans (map_le_range f Model.sylowSubgroup))
  have hRS : R ≤ Model.sylowSubgroup :=
    (map_le_map_iff_of_injective hf).mp (by rwa [hmap])
  have hRcent : Model.sylowSubgroup ⊓ centralizer (R : Set NonsplitModels.Second) ≤ R :=
    centric_of_map_injective f hf Model.sylowSubgroup R (by
      simpa only [hmap] using hcent)
  have hRrad : IntrinsicRadicalIn Model.sylowSubgroup R :=
    intrinsicRadicalIn_of_map_injective f hf Model.sylowSubgroup R (by
      simpa only [hmap] using hrad)
  rcases h R hRS hRcent hRrad with hchar | hexceptional
  · left
    have hc := characteristic_subgroupOf_map_injective f hf Model.transferSubgroup R hchar
    change ((Model.transferSubgroup.map f).subgroupOf U).Characteristic
    rw [← hmap]
    exact hc
  · right
    rw [← hmap, hexceptional]
    rfl

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer
