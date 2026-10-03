module
public import ABG.ChapterII.Section3.CentralSylowPreimageNonsplitting
public import GorensteinWalter.PSL2DihedralSylow
public import GorensteinWalter.DihedralCore
public import GorensteinWalter.KleinFourMapInjective

/-!
# The actual central PSL2 preimage

The inverse image E of a normal PSL2 subgroup of G/N is a normal subgroup
of G. Suppose N is the globally central, cyclic, nontrivial center image
of a Sylow two-subgroup whose every Klein four meets its center. The
internal kernel Z=N intersect E is cyclic,
nontrivial, central and a two-group. Restricting the original quotient map
identifies E/Z with the same PSL2 group, not merely an abstract quotient.

Every odd PSL2 has a dihedral Sylow two-subgroup and hence a Klein four
subgroup. Transporting it to E/Z invokes the central-Sylow nonsplitting
lemma. These are precisely the inputs for the cyclic central cover
recognition in ABG II.3 Proposition2, article p22, and Lemma2, article p24.
The original semidihedral/wreathed endpoint is preserved as a wrapper;
generalized Q-group geometry supplies the same four-subgroup premise.
The field of order three and arbitrary nontrivial cyclic two-kernels remain.
-/

namespace ABG
open BenderSuzuki.MatrixGroups GorensteinWalter

private noncomputable def preimageQuotientEquiv
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (L : Subgroup (G ⧸ N)) :
    (L.comap (QuotientGroup.mk' N) ⧸
      N.subgroupOf (L.comap (QuotientGroup.mk' N))) ≃* L := by
  let E := L.comap (QuotientGroup.mk' N)
  let f : E →* L := {
    toFun := fun x => ⟨QuotientGroup.mk' N x.1, x.2⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun x y => Subtype.ext (map_mul _ x.1 y.1) }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N y.1
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change QuotientGroup.mk' N x ∈ L
    rw [hx]
    exact y.2
  have hker : f.ker = N.subgroupOf E := by
    ext x
    change (⟨QuotientGroup.mk' N x.1, x.2⟩ : L) = 1 ↔ x.1 ∈ N
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff x.1
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

public theorem psl2_preimage_central_cover_data_of_four
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hfour : ∀ V : Subgroup S, IsKleinFour V → V ⊓ Subgroup.center S ≠ ⊥)
    (N : Subgroup G) [N.Normal]
    (hN : N = subgroupCenter (S : Subgroup G))
    (hcentral : N ≤ Subgroup.center G) (hcyclic : IsCyclic N) (hne : N ≠ ⊥)
    (F : Type*) [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (L : Subgroup (G ⧸ N)) [L.Normal] (eL : L ≃* PSL2 F) :
    let E := L.comap (QuotientGroup.mk' N)
    let Z := N.subgroupOf E
    E.Normal ∧ N ≤ E ∧ IsCyclic Z ∧ Z ≠ ⊥ ∧
      Z ≤ Subgroup.center E ∧ IsPGroup 2 Z ∧
      Nonempty ((E ⧸ Z) ≃* PSL2 F) ∧
      ¬ ∃ s : (E ⧸ Z) →* E, (QuotientGroup.mk' Z).comp s = MonoidHom.id _ := by
  let E := L.comap (QuotientGroup.mk' N)
  let Z := N.subgroupOf E
  have hNE : N ≤ E := by
    intro x hx
    change QuotientGroup.mk' N x ∈ L
    have hq : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hq]
    exact L.one_mem
  let eZ : Z ≃* N := Subgroup.subgroupOfEquivOfLe hNE
  have hZcyclic : IsCyclic Z := eZ.isCyclic.mpr hcyclic
  have hZne : Z ≠ ⊥ := by
    intro hbot
    apply hne
    apply le_antisymm _ bot_le
    intro x hx
    have hz : (⟨x, hNE hx⟩ : E) ∈ Z := hx
    have he : (⟨x, hNE hx⟩ : E) = 1 := Subgroup.mem_bot.mp (hbot ▸ hz)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val he)
  have hZcentral : Z ≤ Subgroup.center E := by
    intro x hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hcentral hx) y.1)
  have hNtwo : IsPGroup 2 N := by
    let e : Subgroup.center S ≃* N :=
      (Subgroup.equivMapOfInjective _ (S : Subgroup G).subtype
        (S : Subgroup G).subtype_injective).trans (MulEquiv.subgroupCongr hN.symm)
    exact IsPGroup.of_equiv (S.isPGroup'.to_subgroup (Subgroup.center S)) e
  have hZtwo : IsPGroup 2 Z := IsPGroup.of_equiv hNtwo eZ.symm
  let e : (E ⧸ Z) ≃* PSL2 F := (preimageQuotientEquiv N L).trans eL
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 (PSL2 F) := Classical.choice inferInstance
  obtain ⟨m, hm, ⟨eP⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hF P
  obtain ⟨W, _hWP, hW⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (P : Subgroup (PSL2 F)) hm eP
  have hW' := isKleinFour_map_of_injective W hW e.symm.toMonoidHom e.symm.injective
  exact ⟨inferInstance, hNE, hZcyclic, hZne, hZcentral, hZtwo, ⟨e⟩,
    no_section_preimage_sylow_center_of_four S hfour N hN hcentral E _ hW'⟩

public theorem psl2_preimage_central_cover_data
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S)
    (N : Subgroup G) [N.Normal]
    (hN : N = subgroupCenter (S : Subgroup G))
    (hcentral : N ≤ Subgroup.center G) (hcyclic : IsCyclic N) (hne : N ≠ ⊥)
    (F : Type*) [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (L : Subgroup (G ⧸ N)) [L.Normal] (eL : L ≃* PSL2 F) :
    let E := L.comap (QuotientGroup.mk' N)
    let Z := N.subgroupOf E
    E.Normal ∧ N ≤ E ∧ IsCyclic Z ∧ Z ≠ ⊥ ∧
      Z ≤ Subgroup.center E ∧ IsPGroup 2 Z ∧
      Nonempty ((E ⧸ Z) ≃* PSL2 F) ∧
      ¬ ∃ s : (E ⧸ Z) →* E, (QuotientGroup.mk' Z).comp s = MonoidHom.id _ :=
  psl2_preimage_central_cover_data_of_four S
    (fun V hV => four_subgroup_inf_center_ne_bot hS V hV)
    N hN hcentral hcyclic hne F hF L eL

end ABG
