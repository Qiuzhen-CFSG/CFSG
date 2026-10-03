module

public import Theory.SpecificGroups.Suzuki.SubgroupOvoid
public import Theory.GroupTheory.FrobeniusAbelianImage

/-!
# Frobenius kernels inside Suzuki point stabilizers

A finite Frobenius group embedded in a Suzuki Borel has its kernel inside
the root group. Indeed, the Borel modulo the root group is a cyclic image
of the split torus, and every abelian image kills a Frobenius kernel.
Consequently these kernels are 2-groups. Conjugating an arbitrary ovoid
point to infinity gives the corresponding result for subgroup subactions.

Source: Huppert--Blackburn, *Finite Groups III*, XI.3.12(e), using the
root-by-torus structure of XI.3.3.
-/

namespace BenderSuzuki.MatrixGroups

/-- Every Frobenius kernel mapped into a Suzuki Borel lies in the root group. -/
public theorem suzukiBorel_frobeniusKernel_le_root
    {m : ℕ} (hm : 0 < m) {G : Type*} [Group G] [Finite G]
    {F D : Subgroup G} (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (f : G →* SuzukiBorelSubgroup m) :
    F ≤ ((SuzukiRootSubgroup m).subgroupOf (SuzukiBorelSubgroup m)).comap f := by
  let B := SuzukiBorelSubgroup m
  let U := (SuzukiRootSubgroup m).subgroupOf B
  let T := (SuzukiSplitTorus m).subgroupOf B
  have hroot : SuzukiRootSubgroup m ≤ B := by
    dsimp only [B]
    rw [suzukiBorelSubgroup_eq_sup]
    exact le_sup_left
  have htorus : SuzukiSplitTorus m ≤ B := by
    dsimp only [B]
    rw [suzukiBorelSubgroup_eq_sup]
    exact le_sup_right
  let : U.Normal := suzukiRootSubgroup_normal_in_borel m
  let : IsCyclic (SuzukiSplitTorus m) := suzukiSplitTorus_isCyclic m hm
  let eT : T ≃* SuzukiSplitTorus m := Subgroup.subgroupOfEquivOfLe htorus
  let : IsCyclic T := isCyclic_of_surjective eT.symm eT.symm.surjective
  let q : B →* B ⧸ U := QuotientGroup.mk' U
  let t : T →* B ⧸ U := q.comp T.subtype
  have hsup : U ⊔ T = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hroot htorus]
    change (SuzukiRootSubgroup m ⊔ SuzukiSplitTorus m).subgroupOf B = ⊤
    rw [← suzukiBorelSubgroup_eq_sup, Subgroup.subgroupOf_self]
  have ht : Function.Surjective t := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective U y
    have hb : b ∈ U ⊔ T := by rw [hsup]; trivial
    obtain ⟨u, hu, v, hv, huv⟩ := Subgroup.mem_sup_of_normal_left.mp hb
    refine ⟨⟨v, hv⟩, ?_⟩
    change q v = q b
    have hqu : q u = 1 := (QuotientGroup.eq_one_iff (N := U) u).mpr hu
    rw [← huv, map_mul, hqu, one_mul]
  let : IsCyclic (B ⧸ U) := isCyclic_of_surjective t ht
  have hker : F ≤ (q.comp f).ker := hFrob.le_ker_of_isMulCommutative (q.comp f)
  intro x hx
  exact (QuotientGroup.eq_one_iff (N := U) (f x)).mp (hker hx)

/-- A Frobenius kernel in a group embedded in a Suzuki Borel is a 2-group. -/
public theorem suzukiBorel_frobeniusKernel_isPGroup
    {m : ℕ} (hm : 0 < m) {G : Type*} [Group G] [Finite G]
    {F D : Subgroup G} (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (f : G →* SuzukiBorelSubgroup m) (hf : Function.Injective f) :
    IsPGroup 2 F := by
  let U := (SuzukiRootSubgroup m).subgroupOf (SuzukiBorelSubgroup m)
  have hroot : SuzukiRootSubgroup m ≤ SuzukiBorelSubgroup m := by
    rw [suzukiBorelSubgroup_eq_sup]
    exact le_sup_left
  have hle := suzukiBorel_frobeniusKernel_le_root hm hFrob f
  let lift : F →* U := (f.comp F.subtype).codRestrict U (fun x => hle x.property)
  have hlift : Function.Injective lift := by
    intro x y h
    apply Subtype.ext
    exact hf (congrArg Subtype.val h)
  let eU : U ≃* SuzukiRootSubgroup m := Subgroup.subgroupOfEquivOfLe hroot
  exact ((suzukiRootSubgroup_isPGroup m hm).of_injective eU.toMonoidHom eU.injective).of_injective
    lift hlift

/-- Frobenius kernels in point stabilizers of an ovoid subaction are
2-groups. This uses only the embedding into an ambient point stabilizer. -/
public theorem suzukiSubaction_frobeniusKernel_isPGroup
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (X : SubMulAction H (SuzukiOvoid m)) (a : X)
    {F D : Subgroup (MulAction.stabilizer H a)}
    (hFrob : IsFrobeniusGroupWithKernelComplement F D) : IsPGroup 2 F := by
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m)
    (suzukiOvoidInfinity m) a.val
  let S := MulAction.stabilizer H a
  let f₀ : S →* SuzukiMatrixGroup m :=
    (MulAut.conj k⁻¹).toMonoidHom.comp (H.subtype.comp S.subtype)
  have hf₀ : Function.Injective f₀ :=
    (MulAut.conj k⁻¹).injective.comp (H.subtype_injective.comp S.subtype_injective)
  have hmem (r : S) : f₀ r ∈ SuzukiBorelSubgroup m := by
    rw [suzukiBorelSubgroup_eq_stabilizer m hm, MulAction.mem_stabilizer_iff]
    change (k⁻¹ * r.val.val * k) • suzukiOvoidInfinity m = suzukiOvoidInfinity m
    have hra : r.val.val • a.val = a.val := congrArg Subtype.val r.property
    rw [mul_smul, mul_smul, hk, hra, ← hk, inv_smul_smul]
  let f : S →* SuzukiBorelSubgroup m := f₀.codRestrict _ hmem
  exact suzukiBorel_frobeniusKernel_isPGroup hm hFrob f
    (fun _ _ h => hf₀ (congrArg Subtype.val h))

end BenderSuzuki.MatrixGroups
