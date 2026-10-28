module

public import Stellmacher.SectionThree.ResidualImageOddPGroup
public import Stellmacher.SectionThree.LemmaThreeSeven
public import Theory.GroupTheory.OddResidualCyclicCenter

/-!
# The Sylow image in a solvable P-set core quotient

Normal subgroups of the Sylow image lift to genuine normal subgroups of S.
Lemma (3.4) therefore makes every nontrivial such subgroup generate the
residual through commutators. Lemma (3.3) supplies its odd-prime structure,
and the unique maximal overgroup ensures that this residual is nontrivial.

The odd-layer commutator criterion then proves that the center of the Sylow
image is cyclic. This is the consequence used in Stellmacher (8.6), printed
p.42, between equations (5) and (6).
-/

namespace Stellmacher.SectionThree

universe u

public theorem sylow_quotient_normal_commutator
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P)
    (J : Subgroup (P ⧸ pCore 2 P))
    (hJS : J ≤ (S.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)))
    (hJn : (J.subgroupOf ((S.subgroupOf P).map
      (QuotientGroup.mk' (pCore 2 P)))).Normal)
    (hJne : J ≠ ⊥) :
    ⁅(twoResidualSubgroup P).map (QuotientGroup.mk' (pCore 2 P)), J⁆ =
      (twoResidualSubgroup P).map (QuotientGroup.mk' (pCore 2 P)) := by
  classical
  have hSP : S ≤ P := by
    obtain ⟨U, hU⟩ := hP.1.2.1
    rw [← hU]
    exact Subgroup.map_subtype_le _
  let q := QuotientGroup.mk' (pCore 2 P)
  let SP := S.subgroupOf P
  let L := SP ⊓ J.comap q
  let T := L.map P.subtype
  have hSPmap : SP.map P.subtype = S := Subgroup.map_subgroupOf_eq_of_le hSP
  have hTS : T ≤ S := by
    rw [← hSPmap]
    exact Subgroup.map_mono inf_le_left
  have hnormJ : SP.map q ≤ Subgroup.normalizer J :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJS).mp hJn
  have hnormL : SP ≤ Subgroup.normalizer L := by
    apply Subgroup.le_normalizer_iff.mpr
    intro s hs l hl
    refine ⟨SP.mul_mem (SP.mul_mem hs hl.1) (SP.inv_mem hs), ?_⟩
    change q (s * l * s⁻¹) ∈ J
    simpa only [map_mul, map_inv] using
      (Subgroup.le_normalizer_iff.mp hnormJ (q s) (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)
        (q l) hl.2)
  have hTnormal : (T.subgroupOf S).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hTS).mpr
    apply Subgroup.le_normalizer_iff.mpr
    intro s hs t ht
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp ht
    let sP : P := ⟨s, hSP hs⟩
    exact Subgroup.mem_map.mpr ⟨sP * l * sP⁻¹,
      Subgroup.le_normalizer_iff.mp hnormL sP hs l hl, rfl⟩
  have hLmap : L.map q = J := by
    apply le_antisymm
    · exact Subgroup.map_le_iff_le_comap.mpr inf_le_right
    · intro j hj
      obtain ⟨s, hs, rfl⟩ := hJS hj
      exact ⟨s, ⟨hs, hj⟩, rfl⟩
  have hTnot : ¬ T ≤ twoCoreAmbient P := by
    intro hTcore
    have hLcore : L ≤ pCore 2 P := by
      intro l hl
      obtain ⟨x, hx, hxl⟩ := hTcore (Subgroup.mem_map_of_mem P.subtype hl)
      exact P.subtype_injective hxl ▸ hx
    apply hJne
    rw [← hLmap]
    apply (Subgroup.map_eq_bot_iff (f := q) (H := L)).mpr
    simpa [q] using hLcore
  have hcommT := (lemma_three_four S h P hP T ⟨hTS, hTnormal⟩ hsolv).resolve_left hTnot
  have hcommL : ⁅twoResidualSubgroup P, L⁆ = twoResidualSubgroup P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator]
    exact hcommT
  have hmap := congrArg (Subgroup.map q) hcommL
  rw [Subgroup.map_commutator, hLmap] at hmap
  exact hmap

public theorem sylow_quotient_residual_data
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P) :
    let q := QuotientGroup.mk' (pCore 2 P)
    let R := (twoResidualSubgroup P).map q
    let A := (S.subgroupOf P).map q
    R.Normal ∧ R ≠ ⊥ ∧ IsPGroup 2 A ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p R := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q := QuotientGroup.mk' (pCore 2 P)
  let SP := S.subgroupOf P
  let R := twoResidualSubgroup P
  have hSP : S ≤ P := by
    obtain ⟨U, hU⟩ := hP.1.2.1
    rw [← hU]
    exact Subgroup.map_subtype_le _
  have hSPmap : SP.map P.subtype = S := Subgroup.map_subgroupOf_eq_of_le hSP
  obtain ⟨U, hU⟩ := hP.1.2.1
  have hUSP : (U : Subgroup P) = SP := by
    apply Subgroup.map_injective P.subtype_injective
    exact hU.trans hSPmap.symm
  have hSPtwo : IsPGroup 2 SP := hUSP ▸ U.isPGroup'
  have hcoreSP : pCore 2 P ≤ SP := by
    rw [← hUSP]
    exact IsPGroup.le_sylow_of_normal (pCore_isPGroup (G := P) (p := 2)) U
  have hRn : R.Normal := by
    dsimp [R]
    rw [twoResidualSubgroup_eq_hktPResidual']
    exact BenderSuzuki.External.hktPResidual_normal
  have hRne : R.map q ≠ ⊥ := by
    intro hbot
    have hRcore : R ≤ pCore 2 P := by
      have hh := (Subgroup.map_eq_bot_iff (f := q) (H := R)).mp hbot
      simpa [q] using hh
    have hgen : R ⊔ SP = ⊤ := by
      apply Subgroup.map_injective P.subtype_injective
      rw [Subgroup.map_sup, hSPmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact twoResidual_sup_sylowImage hP.1.2.1
    have hSPtop : SP = ⊤ := by
      rw [sup_eq_right.mpr (hRcore.trans hcoreSP)] at hgen
      exact hgen
    obtain ⟨B, hB, hSB, _⟩ := hP.2
    have hSPB : SP ≤ B := by
      intro s hs
      obtain ⟨b, hb, heq⟩ := hSB hs
      exact P.subtype_injective heq ▸ hb
    exact hB.ne_top (top_unique (hSPtop ▸ hSPB))
  refine ⟨hRn.map q (QuotientGroup.mk'_surjective _), hRne, hSPtwo.map q, ?_⟩
  exact pSet_residual_image_is_odd_pGroup S h P hP hsolv q (by simp [q])
public theorem sylow_quotient_center_isCyclic
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P) :
    IsCyclic (Subgroup.center ((S.subgroupOf P).map
      (QuotientGroup.mk' (pCore 2 P)))) := by
  obtain ⟨hRn, hRne, hA2, prime, hprime, hodd, hRp⟩ :=
    sylow_quotient_residual_data S h P hP hsolv
  let _ : Fact prime.Prime := ⟨hprime⟩
  exact Theory.GroupTheory.center_isCyclic_of_odd_pgroup_commutator
    hodd _ _ hRn hRp hRne hA2
    (sylow_quotient_normal_commutator S h P hP hsolv)

end Stellmacher.SectionThree
