module

public import Theory.SpecificGroups.Suzuki.MaximalNonsplitTori

/-!
# Abelian subgroups of Suzuki groups

Every nontrivial abelian subgroup lies in a unique member of the root/torus
partition. For root elements the unique fixed point puts the centralizer in
the Borel; the Frobenius property puts it in the root group. For split elements
the centralizer preserves the fixed pair, and the Weyl coset is excluded by
the unique fixed point of an involution. Nonsplit centralizers are already
maximal nonsplit tori. Uniqueness then controls normalizers.

Source: Huppert--Blackburn, *Finite Groups III*, XI.3.10 and XI.3.12(e).
-/

namespace BenderSuzuki.MatrixGroups

open scoped Pointwise

/-- The centralizer of a nonidentity root element lies in the root group. -/
public theorem suzukiRootSubgroup_centralizer_le (m : ℕ) (hm : 0 < m)
    {x : SuzukiMatrixGroup m} (hx : x ∈ SuzukiRootSubgroup m) (hne : x ≠ 1) :
    Subgroup.centralizer {x} ≤ SuzukiRootSubgroup m := by
  intro y hy
  have hc : Commute y x := Subgroup.mem_centralizer_singleton_iff.mp hy
  have hyB : y ∈ SuzukiBorelSubgroup m := by
    rw [suzukiBorelSubgroup_eq_stabilizer m hm, MulAction.mem_stabilizer_iff]
    apply (suzukiRootSubgroup_fixed_iff m hm x hx hne _).mp
    rw [← mul_smul, ← hc.eq, mul_smul, suzukiRootSubgroup_fix_infinity m hm x hx]
  by_contra hyR
  obtain ⟨r, hr⟩ := suzukiBorelSubgroup_conjugate_into_split m hm y hyB hyR
  let f := (MulAut.conj (r : SuzukiMatrixGroup m)⁻¹).toMonoidHom
  have hfx : f x ∈ SuzukiRootSubgroup m := by
    change (r : SuzukiMatrixGroup m)⁻¹ * x * r ∈ _
    exact (SuzukiRootSubgroup m).mul_mem
      ((SuzukiRootSubgroup m).mul_mem ((SuzukiRootSubgroup m).inv_mem r.property) hx)
      r.property
  have hfy : f y ∈ SuzukiSplitTorus m := by simpa [f] using hr
  have hfyne : f y ≠ 1 := by
    intro h
    have : y = 1 := (MulAut.conj (r : SuzukiMatrixGroup m)⁻¹).injective
      (h.trans (map_one f).symm)
    exact hyR (this ▸ (SuzukiRootSubgroup m).one_mem)
  have h := suzukiRootSubgroup_eq_one_of_commute_split m hm (f y) (f x)
    hfy hfyne hfx (hc.map f)
  exact hne ((MulAut.conj (r : SuzukiMatrixGroup m)⁻¹).injective
    (h.trans (map_one f).symm))

/-- The centralizer of a nonidentity split-torus element is the split torus. -/
public theorem suzukiSplitTorus_centralizer_eq (m : ℕ) (hm : 0 < m)
    {x : SuzukiMatrixGroup m} (hx : x ∈ SuzukiSplitTorus m) (hne : x ≠ 1) :
    Subgroup.centralizer {x} = SuzukiSplitTorus m := by
  let : IsCyclic (SuzukiSplitTorus m) := suzukiSplitTorus_isCyclic m hm
  apply le_antisymm ?_ ((Subgroup.le_centralizer _).trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx)))
  intro y hy
  have hc : Commute y x := Subgroup.mem_centralizer_singleton_iff.mp hy
  have hyN : y ∈ MulAction.stabilizer (SuzukiMatrixGroup m) (suzukiOvoidPair m) := by
    rw [MulAction.mem_stabilizer_set' (Set.toFinite _)]
    intro a ha
    apply (suzukiSplitTorus_fixed_pair m hm x hx hne _).mp
    rw [← mul_smul, ← hc.eq, mul_smul,
      (suzukiSplitTorus_fixed_pair m hm x hx hne a).mpr ha]
  rcases (suzukiOvoidPair_stabilizer_forms m y).mp hyN with hyT | ⟨t, rfl⟩
  · exact hyT
  exfalso
  have hy2 : orderOf ((t : SuzukiMatrixGroup m) * suzukiWeyl m) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]
      calc
        _ = (t : SuzukiMatrixGroup m) *
            (suzukiWeyl m * t * suzukiWeyl m) := by group
        _ = 1 := by rw [suzukiWeyl_conj_splitTorus]; exact mul_inv_cancel _
    · intro h
      have hw : suzukiWeyl m = (t : SuzukiMatrixGroup m)⁻¹ := eq_inv_of_mul_eq_one_right h
      exact suzukiWeyl_not_mem_splitTorus m (hw ▸ (SuzukiSplitTorus m).inv_mem t.property)
  obtain ⟨a, ha, hu⟩ := suzukiOvoid_involution_unique_fixed m hm _ hy2
  have hxa : x • a = a := hu _ (by
    change ((t : SuzukiMatrixGroup m) * suzukiWeyl m) • (x • a) = x • a
    rw [← mul_smul, hc.eq, mul_smul, ha])
  have hpair := (suzukiSplitTorus_fixed_pair m hm x hx hne a).mp hxa
  have ht := (mem_suzukiSplitTorus_iff_fix_pair m t).mp t.property
  rcases (show a = suzukiOvoidInfinity m ∨ a = suzukiOvoidZero m from hpair) with rfl | rfl
  · exact suzukiOvoidInfinity_ne_zero m
      (by simpa only [mul_smul, suzukiWeyl_smul_infinity, ht.2] using ha.symm)
  · exact suzukiOvoidInfinity_ne_zero m
      (by simpa only [mul_smul, suzukiWeyl_smul_zero, ht.1] using ha)

/-- Conjugation preserves the Suzuki partition. -/
public theorem SuzukiPartitionMember.map_conj {m : ℕ}
    {U : Subgroup (SuzukiMatrixGroup m)} (hU : SuzukiPartitionMember m U)
    (g : SuzukiMatrixGroup m) :
    SuzukiPartitionMember m (U.map (MulAut.conj g).toMonoidHom) := by
  rw [suzukiPartitionMember_iff] at hU ⊢
  have hmap (V : Subgroup (SuzukiMatrixGroup m)) (h : SuzukiMatrixGroup m) :
      (V.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
        V.map (MulAut.conj (g * h)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rcases hU with ⟨h, rfl⟩ | ⟨h, rfl⟩ | hU
  · exact Or.inl ⟨g * h, hmap _ h⟩
  · exact Or.inr (Or.inl ⟨g * h, hmap _ h⟩)
  · exact Or.inr (Or.inr (hU.map_conj g))

private theorem centralizer_le_conjugate {G : Type*} [Group G]
    (U : Subgroup G) (g : G)
    (hU : ∀ x ∈ U, x ≠ 1 → Subgroup.centralizer {x} ≤ U)
    {x : G} (hx : x ∈ U.map (MulAut.conj g).toMonoidHom) (hne : x ≠ 1) :
    Subgroup.centralizer {x} ≤ U.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hz1 : z ≠ 1 := by intro h; apply hne; simp [h]
  intro y hy
  let f := (MulAut.conj g).toMonoidHom
  let fi := (MulAut.conj g).symm.toMonoidHom
  have hc : Commute y (f z) := Subgroup.mem_centralizer_singleton_iff.mp hy
  have hcz : Commute (fi y) z := by
    simpa only [f, fi, MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using hc.map fi
  refine ⟨fi y, hU z hz hz1 (Subgroup.mem_centralizer_singleton_iff.mpr hcz.eq), ?_⟩
  exact (MulAut.conj g).apply_symm_apply y

/-- Each partition member contains the centralizer of every nonidentity member. -/
public theorem SuzukiPartitionMember.centralizer_le {m : ℕ} (hm : 0 < m)
    {U : Subgroup (SuzukiMatrixGroup m)} (hU : SuzukiPartitionMember m U)
    {x : SuzukiMatrixGroup m} (hx : x ∈ U) (hne : x ≠ 1) :
    Subgroup.centralizer {x} ≤ U := by
  rw [suzukiPartitionMember_iff] at hU
  rcases hU with ⟨g, rfl⟩ | ⟨g, rfl⟩ | hU
  · exact centralizer_le_conjugate _ g
      (fun _ hz hz1 => suzukiRootSubgroup_centralizer_le m hm hz hz1) hx hne
  · exact centralizer_le_conjugate _ g
      (fun _ hz hz1 => (suzukiSplitTorus_centralizer_eq m hm hz hz1).le) hx hne
  · exact (hU.centralizer_eq hm hx hne).le

/-- A nontrivial abelian subgroup lies in exactly one partition member. -/
public theorem suzukiAbelianSubgroup_partition_existsUnique {m : ℕ} (hm : 0 < m)
    (A : Subgroup (SuzukiMatrixGroup m)) [IsMulCommutative A] (hne : A ≠ ⊥) :
    ∃! U, SuzukiPartitionMember m U ∧ A ≤ U := by
  obtain ⟨x, hxA, hx⟩ := A.bot_or_exists_ne_one.resolve_left hne
  obtain ⟨U, ⟨hU, hxU⟩, hu⟩ := suzukiPartition_existsUnique m hm x hx
  refine ⟨U, ⟨hU, ?_⟩, fun V hV => hu V ⟨hV.1, hV.2 hxA⟩⟩
  exact (Subgroup.le_centralizer A).trans
    ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxA)).trans
      (hU.centralizer_le hm hxU hx))

/-- Normalizing a nontrivial subgroup of a partition member normalizes that member. -/
public theorem SuzukiPartitionMember.normalizer_le {m : ℕ} (hm : 0 < m)
    {U A : Subgroup (SuzukiMatrixGroup m)} (hU : SuzukiPartitionMember m U)
    (hA : A ≤ U) (hne : A ≠ ⊥) :
    Subgroup.normalizer (A : Set (SuzukiMatrixGroup m)) ≤
      Subgroup.normalizer (U : Set (SuzukiMatrixGroup m)) := by
  obtain ⟨x, hxA, hx⟩ := A.bot_or_exists_ne_one.resolve_left hne
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  change A.map (MulAut.conj g).toMonoidHom = A at hg
  have hxmap : x ∈ U.map (MulAut.conj g).toMonoidHom := by
    apply Subgroup.map_mono hA
    rwa [hg]
  by_contra hneU
  exact hx (Subgroup.disjoint_def.mp ((hU.map_conj g).disjoint hm hU hneU)
    hxmap (hA hxA))

end BenderSuzuki.MatrixGroups
