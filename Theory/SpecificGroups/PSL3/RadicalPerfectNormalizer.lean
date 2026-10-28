module
public import Theory.SpecificGroups.SL3.RadicalPerfectNormalizer
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.GroupTheory.PRadical.CentralCoprimeLift
public import Theory.GroupTheory.PRadical.NormalComponentImages
/-!
# Perfect subgroups normal in binary PSL₃ radical normalizers

Lift the radical and the perfect subgroup through the actual scalar quotient.
The full normalizer lifts with the radical. The solvable residual of the
perfect subgroup's preimage is identified by the SL₃ radical-normalizer
theorem with a point or line local. Its projection is injective, even when
the scalar center has order three. Thus the specified perfect subgroup has
SL₂(F) as its two-core quotient.

Source: Aschbacher--Smith C.4.5--7 and 4.3.16, printed pp.152--153,618.
-/
public section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree.RadicalNormalizer
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem injective_project_of_local_frame (U C : Subgroup SL(3,F))
    (a : SL(3,F) ≃* SL(3,F)) (hU : U.map a.toMonoidHom = C)
    (hi : Function.Injective ((projection F).comp C.subtype)) :
    Function.Injective ((projection F).comp U.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hxZ : (x : SL(3,F)) ∈ center SL(3,F) := by
    rw [←projection_ker F]
    exact hx
  have haZ : a x ∈ center SL(3,F) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := a.surjective y
    exact (map_mul a _ _).symm.trans ((congrArg a (mem_center_iff.mp hxZ z)).trans (map_mul a _ _))
  have haC : a x ∈ C := hU ▸ mem_map_of_mem a.toMonoidHom x.property
  have ha1 : (⟨a x,haC⟩ : C) = 1 := by
    apply hi
    change projection F (a x) = projection F 1
    rw [map_one]
    apply MonoidHom.mem_ker.mp
    rwa [projection_ker F]
  have hx1 : a (x : SL(3,F)) = a 1 := by
    simpa only [map_one,Subgroup.coe_one] using congrArg Subtype.val ha1
  exact Subtype.ext (a.injective hx1)

/-- The actual perfect normal subgroup has the full coefficient-field Levi quotient. -/
theorem projective_radical_perfect_normal_quotient
    (R B : Subgroup PSL(3,F)) (hR : R.IsPRadical 2)
    [Group.IsPerfect B] (hne : B ≠ ⊥)
    (hBN : B ≤ normalizer (R : Set PSL(3,F)))
    (hNB : normalizer (R : Set PSL(3,F)) ≤ normalizer (B : Set PSL(3,F)))
    {n : ℕ} (hn : 1<n) (hF : Nat.card F = 2^n) :
    Nonempty ((B ⧸ pCore 2 B) ≃* SL(2,F)) := by
  have hker : Nat.Coprime 2 (Nat.card (projection F).ker) := by
    rw [projection_ker]
    exact (Matrix.SL3.odd_card_center F).coprime_two_left
  obtain ⟨A,hA,_,hnA⟩ := exists_radical_lift_of_central_coprime (projection F)
    (projection_surjective F) (by rw [projection_ker]) hker R hR
  let q := projection F
  let U := (solvableResidual (B.comap q)).map (B.comap q).subtype
  let : Group.IsPerfect U := Group.IsPerfect.map _
  have hU : U.map q = B := by
    rw [map_solvableResidual_comap q (projection_surjective F),solvableResidual_eq_top,
      ←MonoidHom.range_eq_map,range_subtype]
  have hUn : U ≠ ⊥ := by
    intro he
    exact hne (by rw [←hU,he,Subgroup.map_bot])
  have hUN : U ≤ normalizer (A : Set SL(3,F)) := by
    rw [←hnA]
    exact (map_subtype_le _).trans (comap_mono hBN)
  have hNU : normalizer (A : Set SL(3,F)) ≤ normalizer (U : Set SL(3,F)) := by
    rw [←hnA]
    apply (comap_mono hNB).trans
    rw [comap_normalizer_eq_of_surjective _ (projection_surjective F)]
    exact normalizer_le_normalizer_characteristic_image (B.comap q) (solvableResidual _)
  obtain ⟨e,he⟩ := radical_perfect_normal_frame A U hA hUn hUN hNU hn hF
  let a := Matrix.HigherLinear.SubspaceTransport.slConj e
  have hb (C : Subgroup SL(3,F)) (hUC : U.map a.toMonoidHom = C)
      (hi : Function.Injective ((projection F).comp C.subtype)) : Nonempty (B ≃* C) := by
    have hu := injective_project_of_local_frame U C a hUC hi
    let k := MulEquiv.ofBijective (q.subgroupMap U)
      ⟨fun x y he => hu (congrArg Subtype.val he),q.subgroupMap_surjective U⟩
    exact ⟨((MulEquiv.subgroupCongr hU).symm.trans k.symm).trans
      ((a.subgroupMap U).trans (MulEquiv.subgroupCongr hUC))⟩
  rcases he with he | he
  · obtain ⟨b⟩ := hb _ he.2 (pointLocal_projection_injective F)
    exact ⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
      (pointLocalSLCoreQuotientEquiv F)⟩
  · obtain ⟨b⟩ := hb _ he.2 (lineLocal_projection_injective F)
    exact ⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
      (lineLocalSLCoreQuotientEquiv F)⟩
end Matrix.PSL3.LinearThree.RadicalNormalizer
