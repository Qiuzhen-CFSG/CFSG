module

public import Theory.SpecificGroups.Triality.RootGeometryBasic
public import Theory.SpecificGroups.Triality.ConcreteBruhat
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedCellCount
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates
public import Mathlib.GroupTheory.Sylow

/-!
# Transfer steps for triality parabolic geometry

Restriction of a split p-subgroup to the elementary fixed points, followed by
the actual central quotient, remains a p-subgroup. Moreover, restriction to the
elementary subgroup loses no fixed positive elements. Every p-subgroup of a
parabolic lies in its embedded O^{p′}; this proves the local-factor containment
as soon as the positive p-group calculation is supplied, including q = 2.

For the remaining geometry, split intersection descends when the elementary
center lies in the split Borel, and generation over the Borel by p-elements
implies supplementation by the local factor. These are conditional transfer
lemmas. The positive normal form, cardinality, Sylow maximality, central-kernel
containment, and finite Bruhat generation still require concrete matrix proofs.

Sources: GLS3 2.3.4–8 and 2.6.4–8 (`refs/KGroup/GLS3/chapter2.tex`);
Aschbacher–Smith F.1.4–12, especially F.1.12(I)(4), printed pp. 260–264
(`refs/quasithin.pdf`). No claim of the source parabolic geometry is made from
these transfer lemmas alone.
-/

public section
namespace Triality.Standard.Parabolics
noncomputable section

theorem unipotent_isPGroup_of_split (P : Parameters)
    (hU : IsPGroup P.prime (positiveSubgroup P)) : IsPGroup P.prime (unipotent P) := by
  exact (hU.comap_of_injective (elementaryInclusion P)
    (fun x y h => Subtype.ext (Subtype.ext h))).map (toCarrier P)

theorem pSubgroup_le_localFactor (P : Parameters) (a : Node)
    (S : Subgroup (Carrier P)) (hS : IsPGroup P.prime S)
    (hSP : S ≤ parabolic P a) : S ≤ localFactor P a := by
  intro g hg
  obtain ⟨k, hk⟩ := hS ⟨g, hg⟩
  exact mem_localFactor_of_pow P a g (hSP hg) k (congrArg Subtype.val hk)

/-- The p-group property supplies the elementary membership of every fixed positive element. -/
theorem fixedPositive_le_elementary (P : Parameters)
    (hU : IsPGroup P.prime (positiveSubgroup P)) :
    (positiveSubgroup P).comap (fixedSubgroup P).subtype ≤ elementarySubgroup P := by
  intro g hg
  obtain ⟨k, hk⟩ := hU ⟨g.val, hg⟩
  apply mem_elementarySubgroup_of_pow P g k
  exact Subtype.ext (congrArg (fun x : positiveSubgroup P => (x : SplitGroup P)) hk)

/-- Restricting the positive fixed points to the elementary group loses no elements. -/
theorem map_restrictedPositive (P : Parameters)
    (hU : IsPGroup P.prime (positiveSubgroup P)) :
    ((positiveSubgroup P).comap (elementaryInclusion P)).map
      (elementarySubgroup P).subtype =
        (positiveSubgroup P).comap (fixedSubgroup P).subtype :=
  Subgroup.map_subgroupOf_eq_of_le (fixedPositive_le_elementary P hU)

theorem unipotent_le_localFactor (P : Parameters) (a : Node)
    (hU : IsPGroup P.prime (unipotent P)) : unipotent P ≤ localFactor P a :=
  pSubgroup_le_localFactor P a _ hU
    ((unipotent_le_borel P).trans (borel_le_parabolic P a))

theorem sylow_le_localFactor (P : Parameters) (a : Node)
    (S : Sylow P.prime (Carrier P)) (hSP : (S : Subgroup _) ≤ parabolic P a) :
    (S : Subgroup _) ≤ localFactor P a :=
  pSubgroup_le_localFactor P a _ S.isPGroup' hSP

theorem localFactor_sup_borel_of_generators (P : Parameters) (a : Node)
    (s : Set (Carrier P))
    (hgen : borel P ⊔ Subgroup.closure s = parabolic P a)
    (hs : ∀ g ∈ s, ∃ k : ℕ, g ^ (P.prime ^ k) = 1) :
    localFactor P a ⊔ borel P = parabolic P a := by
  apply le_antisymm (sup_le (localFactor_le_parabolic P a) (borel_le_parabolic P a))
  rw [← hgen]
  apply sup_le le_sup_right
  apply (Subgroup.closure_le _).mpr
  intro g hg
  obtain ⟨k, hk⟩ := hs g hg
  apply Subgroup.mem_sup_left
  apply mem_localFactor_of_pow P a g _ k hk
  rw [← hgen]
  exact Subgroup.mem_sup_right (Subgroup.subset_closure hg)

/-- Exact overlap descends only after the actual central-kernel containment is known. -/
theorem parabolic_inf_of_split (P : Parameters)
    (hinter : splitParabolic P .arms ⊓ splitParabolic P .central = splitBorel P)
    (hcenter : Subgroup.center (ElementaryGroup P) ≤
      (splitBorel P).comap (elementaryInclusion P)) :
    parabolic P .arms ⊓ parabolic P .central = borel P := by
  have hle (a : Node) : splitBorel P ≤ splitParabolic P a := le_sup_left
  rw [parabolic, parabolic, ← descendSubgroup_inf_of_center_le P _ _
    (hcenter.trans (Subgroup.comap_mono (hle .arms)))
    (hcenter.trans (Subgroup.comap_mono (hle .central))), hinter]
  rfl

/-! Concrete binary assembly of the two root parabolics. -/

theorem unipotent_isPGroup_binary (P : Parameters) (hp : P.prime = 2) :
    IsPGroup 2 (unipotent P) := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  exact unipotent_isPGroup_of_split _
    (PositiveCoordinates.isPGroup_positiveSubgroup_binary n hn)

theorem card_unipotent_binary (P : Parameters) (hp : P.prime = 2) :
    Nat.card (unipotent P) = P.q ^ 12 := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  exact ConcreteBruhat.FixedCellCount.card_unipotent n hn

@[expose] def unipotentSylow (P : Parameters) (hp : P.prime = 2) : Sylow 2 (Carrier P) :=
  (unipotent_isPGroup_binary P hp).toSylow (by
    intro hd
    exact (Nat.not_even_iff_odd.mpr
      (ConcreteBruhat.odd_unipotent_index P hp)) (even_iff_two_dvd.mpr hd))

@[simp] theorem coe_unipotentSylow (P : Parameters) (hp : P.prime = 2) :
    (unipotentSylow P hp : Subgroup (Carrier P)) = unipotent P := rfl

theorem unipotentSylow_le_localFactor (P : Parameters) (hp : P.prime = 2)
    (a : Node) :
    (unipotentSylow P hp : Subgroup (Carrier P)) ≤ localFactor P a := by
  rw [coe_unipotentSylow]
  apply unipotent_le_localFactor
  rw [hp]
  exact unipotent_isPGroup_binary P hp

theorem parabolic_inf_binary (P : Parameters) (hp : P.prime = 2) :
    parabolic P .arms ⊓ parabolic P .central = borel P := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  apply le_antisymm
  · intro g hg
    rcases ConcreteBruhat.FoldedCellGeometry.parabolic_cell_cover n hn .arms g hg.1 with h | h
    · exact h
    rcases ConcreteBruhat.FoldedCellGeometry.parabolic_cell_cover n hn .central g hg.2 with hc | hc2
    · exact hc
    rw [ConcreteBruhat.cell_eq_bruhatCell] at h hc2
    exact (ConcreteBruhat.simpleReflection_ne n hn .arms .central (by decide)
      ((ConcreteBruhat.titsSystem n hn).doubleCoset_index_unique h hc2)).elim
  · exact le_inf (borel_le_parabolic _ .arms) (borel_le_parabolic _ .central)

private theorem simple_mem_binary (n : ℕ) (hn : 0 < n) (a : Node) :
    ConcreteBruhat.simpleReflection n hn a ∈ (ConcreteBruhat.titsSystem n hn).S := by
  rw [ConcreteBruhat.titsSystem_S]
  exact Set.mem_range_self a

theorem parabolic_ne_top_binary (P : Parameters) (hp : P.prime = 2) (a : Node) :
    parabolic P a ≠ ⊤ := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  rw [ConcreteBruhat.parabolic_eq_standardParabolic,
    ← (ConcreteBruhat.titsSystem n hn).standardParabolic_S]
  intro he
  have heq := ((ConcreteBruhat.titsSystem n hn).standardParabolic_eq_iff
    (Set.singleton_subset_iff.mpr (simple_mem_binary n hn a)) Set.Subset.rfl).mp he
  obtain ⟨b, hab⟩ : ∃ b : Node, b ≠ a := by
    cases a
    · exact ⟨.central, by decide⟩
    · exact ⟨.arms, by decide⟩
  have hb := simple_mem_binary n hn b
  rw [← heq, Set.mem_singleton_iff] at hb
  exact ConcreteBruhat.simpleReflection_ne n hn b a hab hb

theorem parabolic_sup_binary (P : Parameters) (hp : P.prime = 2) :
    parabolic P .arms ⊔ parabolic P .central = ⊤ := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  rw [ConcreteBruhat.parabolic_eq_standardParabolic,
    ConcreteBruhat.parabolic_eq_standardParabolic]
  let T := ConcreteBruhat.titsSystem n hn
  apply top_unique
  rw [← T.standardParabolic_S]
  apply T.standardParabolic_le _
    ((T.B_le_standardParabolic _).trans le_sup_left)
  intro s hs
  rcases (ConcreteBruhat.mem_titsSystem_S_iff n hn s).mp hs with rfl | rfl
  · exact fun g hg => Subgroup.mem_sup_left
      (T.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _) hg)
  · exact fun g hg => Subgroup.mem_sup_right
      (T.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _) hg)

theorem localFactor_sup_borel_binary (P : Parameters) (hp : P.prime = 2) (a : Node) :
    localFactor P a ⊔ borel P = parabolic P a := by
  obtain ⟨s, hgen, hs⟩ := ConcreteBruhat.exists_characteristic_power_generators P hp a
  exact localFactor_sup_borel_of_generators P a s hgen hs

end
end Triality.Standard.Parabolics
