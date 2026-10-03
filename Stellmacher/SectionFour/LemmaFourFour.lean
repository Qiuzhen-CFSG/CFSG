module

public import Stellmacher.SectionFour.LemmaFourThree

/-!
# Stellmacher's Lemma 4.4

Let `P ∈ PSet ⊤ S` lie outside `PSet (mSubgroup S) S`, and choose either
of the restricted families `pZero S` or `pOne S`.  This module proves that
some member `Pstar` of that family has trivial 2-core after joining it with
`P`; equivalently, `(P, Pstar)` belongs to `Lambda S`.

If every such join had nontrivial 2-core, Lemma 4.1(c) and the common Sylow
subgroup would put every join in `LSet ⊤ S`.  Lemma 4.2 then places
`dSubgroup S` below each join core.  Intersecting those cores and using the
appropriate equality from Lemma 4.3 identifies their intersection with
`dSubgroup S`.  Since `P` normalizes every join core, it normalizes this
intersection and hence lies in `mSubgroup S`, contradicting the hypothesis.

Source: `refs/latex/stellmacher-n-group.tex`, statement and proof (4.4),
journal page 25, lines 954--965.
-/

namespace Stellmacher.SectionFour

universe u

private theorem pSet_top_of_mem
    {G : Type u} [Group G]
    {S U P : Subgroup G}
    (hP : P ∈ SectionThree.PSet U S) :
    P ∈ SectionThree.PSet (⊤ : Subgroup G) S := by
  rcases hP with ⟨⟨_, hSyl, hcore, hproper⟩, hmax⟩
  exact ⟨⟨le_top, hSyl, hcore, hproper⟩, hmax⟩

private theorem pSet_mem_of_le
    {G : Type u} [Group G]
    {S U P : Subgroup G}
    (hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) S)
    (hPU : P ≤ U) :
    P ∈ SectionThree.PSet U S := by
  rcases hP with ⟨⟨_, hSyl, hcore, hproper⟩, hmax⟩
  exact ⟨⟨hPU, hSyl, hcore, hproper⟩, hmax⟩

private theorem sylow_le_of_pSet
    {G : Type u} [Group G]
    {S P : Subgroup G}
    (hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) S) : S ≤ P := by
  rcases hP.1.2.1 with ⟨T, hT⟩
  rw [← hT]
  exact Subgroup.map_subtype_le (T : Subgroup P)

private theorem pAt_subset_pSet
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (k : ℕ) :
    pAt S k ⊆ SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G) := by
  intro P hP
  unfold pAt at hP
  split at hP
  · rcases hP with hP | hP
    · exact pSet_top_of_mem hP.1
    · exact hP.1.1
  · rcases hP with hP | hP
    · exact pSet_top_of_mem hP.1
    · exact hP.1.1

/-- The 2-core of an intermediate subgroup containing a global Sylow
2-subgroup lies in that Sylow subgroup. -/
private theorem twoCoreAmbient_le_sylow
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (H : Subgroup G)
    (hSH : (S : Subgroup G) ≤ H) :
    twoCoreAmbient H ≤ (S : Subgroup G) := by
  let T : Sylow 2 H := S.subtype hSH
  have hsup_p : IsPGroup 2 ↥(pCore 2 H ⊔ (T : Subgroup H)) :=
    (pCore_isPGroup (p := 2) (G := H)).to_sup_of_normal_left T.isPGroup'
  have hsup : pCore 2 H ⊔ (T : Subgroup H) = (T : Subgroup H) :=
    T.is_maximal' hsup_p le_sup_right
  have hcore_le_T : pCore 2 H ≤ (T : Subgroup H) :=
    le_sup_left.trans_eq hsup
  change (pCore 2 H).map H.subtype ≤ (S : Subgroup G)
  have hmap := Subgroup.map_mono (f := H.subtype) hcore_le_T
  simpa [T, Sylow.coe_subtype,
    Subgroup.map_subgroupOf_eq_of_le hSH] using hmap

private theorem twoCoreAmbient_normal_subgroupOf
    {G : Type u} [Group G] (H : Subgroup G) :
    ((twoCoreAmbient H).subgroupOf H).Normal := by
  change ((pCore 2 H).map H.subtype).comap H.subtype |>.Normal
  rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  infer_instance

private theorem le_normalizer_twoCoreAmbient
    {G : Type u} [Group G] (H : Subgroup G) :
    H ≤ Subgroup.normalizer (twoCoreAmbient H : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hyH : y ∈ H := Subgroup.map_subtype_le (pCore 2 H) hy
    exact (twoCoreAmbient_normal_subgroupOf H).conj_mem
      ⟨y, hyH⟩ hy ⟨x, hx⟩
  · intro hyconj
    have hyconjH : x * y * x⁻¹ ∈ H :=
      Subgroup.map_subtype_le (pCore 2 H) hyconj
    have hback := (twoCoreAmbient_normal_subgroupOf H).conj_mem
      ⟨x * y * x⁻¹, hyconjH⟩ hyconj ⟨x⁻¹, H.inv_mem hx⟩
    change x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ ∈ twoCoreAmbient H at hback
    simpa [mul_assoc] using hback

/-- If the 2-core of `H` lies in `K ≤ H`, then it lies in the 2-core of `K`.
Normality is restricted from `H` to `K`. -/
private theorem twoCoreAmbient_le_twoCoreAmbient
    {G : Type u} [Group G] [Finite G]
    {H K : Subgroup G}
    (hKH : K ≤ H)
    (hcoreK : twoCoreAmbient H ≤ K) :
    twoCoreAmbient H ≤ twoCoreAmbient K := by
  let C : Subgroup K := (twoCoreAmbient H).subgroupOf K
  have hC_normal : C.Normal := by
    constructor
    intro n hn g
    change (g : G) * (n : G) * (g : G)⁻¹ ∈ twoCoreAmbient H
    have gH : (g : G) ∈ H := hKH g.property
    have nH : (n : G) ∈ H :=
      Subgroup.map_subtype_le (pCore 2 H) hn
    exact (twoCoreAmbient_normal_subgroupOf H).conj_mem
      ⟨n, nH⟩ hn ⟨g, gH⟩
  have hC_p : IsPGroup 2 C := by
    let f : C →* twoCoreAmbient H :=
      { toFun := fun x => ⟨(x : G), x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact IsPGroup.of_injective
      (IsPGroup.map (pCore_isPGroup (p := 2) (G := H)) H.subtype)
      f (by
        intro x y hxy
        change (⟨(x : G), x.property⟩ : twoCoreAmbient H) =
          (⟨(y : G), y.property⟩ : twoCoreAmbient H) at hxy
        have hxyG : (x : G) = (y : G) :=
          congrArg (fun z : twoCoreAmbient H => (z : G)) hxy
        exact Subtype.ext (Subtype.ext hxyG))
  have hC_le : C ≤ pCore 2 K := le_sSup ⟨hC_normal, hC_p⟩
  change (pCore 2 H).map H.subtype ≤ (pCore 2 K).map K.subtype
  have hC_map : C.map K.subtype = (pCore 2 H).map H.subtype := by
    exact Subgroup.map_subgroupOf_eq_of_le hcoreK
  rw [← hC_map]
  exact Subgroup.map_mono hC_le

/-- **Stellmacher (4.4).**  A global family member outside
`PSet (mSubgroup S) S` has a `Lambda`-partner in either restricted family. -/
public theorem lemma_four_four
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S)
    (P : Subgroup G)
    (hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G))
    (hPnot : P ∉ SectionThree.PSet (mSubgroup S) (S : Subgroup G))
    (k : ℕ) (hk : k = 0 ∨ k = 1) :
    ∃ Pstar : Subgroup G,
      Pstar ∈ pAt S k ∧ (P, Pstar) ∈ Lambda S := by
  classical
  have h41c : Subgroup.normalizer (S : Set G) ≤ mSubgroup S :=
    (lemma_four_one S h).part_c
  have h42 : ∀ L : Subgroup G,
      L ∈ SectionThree.LSet (⊤ : Subgroup G) (S : Subgroup G) →
        localD L (S : Subgroup G) = twoCoreAmbient L := by
    intro L hL
    exact (lemma_four_two S h L hL).2.1
  have h43 := lemma_four_three S h
  have hP_not_le_M : ¬ P ≤ mSubgroup S := by
    intro hPM
    exact hPnot (pSet_mem_of_le hP hPM)
  have hD_at : dSubgroup S =
      sInf {D : Subgroup G |
        ∃ Pstar : Subgroup G,
          Pstar ∈ pAt S k ∧ D = twoCoreAmbient Pstar} := by
    rcases hk with rfl | rfl
    · simpa [pAt] using h43.1
    · simpa [pAt] using h43.2
  by_contra hexists
  simp only [not_exists, not_and] at hexists
  have hjoin_core_ne (Pstar : Subgroup G) (hPstar : Pstar ∈ pAt S k) :
      twoCoreAmbient (P ⊔ Pstar) ≠ ⊥ := by
    intro hcore
    exact hexists Pstar hPstar
      ⟨hP, pAt_subset_pSet S k hPstar, hcore⟩
  have hjoin_L (Pstar : Subgroup G) (hPstar : Pstar ∈ pAt S k) :
      P ⊔ Pstar ∈
        SectionThree.LSet (⊤ : Subgroup G) (S : Subgroup G) := by
    have hSP : (S : Subgroup G) ≤ P := sylow_le_of_pSet hP
    have hSjoin : (S : Subgroup G) ≤ P ⊔ Pstar := hSP.trans le_sup_left
    refine ⟨le_top, ⟨S.subtype hSjoin, ?_⟩,
      hjoin_core_ne Pstar hPstar, ?_⟩
    · simpa [Sylow.coe_subtype] using
        (Subgroup.map_subgroupOf_eq_of_le hSjoin)
    · intro hSeq
      have hjoin_le_norm : P ⊔ Pstar ≤ Subgroup.normalizer (S : Set G) := by
        have hset : (S : Set G) = (twoCoreAmbient (P ⊔ Pstar) : Set G) :=
          congrArg (fun K : Subgroup G => (K : Set G)) hSeq
        rw [hset]
        exact le_normalizer_twoCoreAmbient (P ⊔ Pstar)
      exact hP_not_le_M (le_sup_left.trans (hjoin_le_norm.trans h41c))
  have hD_le_join_core (Pstar : Subgroup G) (hPstar : Pstar ∈ pAt S k) :
      dSubgroup S ≤ twoCoreAmbient (P ⊔ Pstar) := by
    rw [← h42 (P ⊔ Pstar) (hjoin_L Pstar hPstar)]
    unfold dSubgroup localD
    refine le_sInf ?_
    intro D hD
    rcases hD with ⟨Q, hQ, rfl⟩
    apply sInf_le
    exact ⟨Q, pSet_top_of_mem hQ, rfl⟩
  let E : Subgroup G :=
    sInf {D : Subgroup G |
      ∃ Pstar : Subgroup G,
        Pstar ∈ pAt S k ∧ D = twoCoreAmbient (P ⊔ Pstar)}
  have hE_le_join_core (Pstar : Subgroup G) (hPstar : Pstar ∈ pAt S k) :
      E ≤ twoCoreAmbient (P ⊔ Pstar) := by
    change sInf {D : Subgroup G |
      ∃ Pstar : Subgroup G,
        Pstar ∈ pAt S k ∧ D = twoCoreAmbient (P ⊔ Pstar)} ≤
      twoCoreAmbient (P ⊔ Pstar)
    exact sInf_le ⟨Pstar, hPstar, rfl⟩
  have hD_le_E : dSubgroup S ≤ E := by
    refine le_sInf ?_
    intro D hD
    rcases hD with ⟨Pstar, hPstar, rfl⟩
    exact hD_le_join_core Pstar hPstar
  have hE_le_D : E ≤ dSubgroup S := by
    rw [hD_at]
    refine le_sInf ?_
    intro D hD
    rcases hD with ⟨Pstar, hPstar, rfl⟩
    refine (hE_le_join_core Pstar hPstar).trans ?_
    apply twoCoreAmbient_le_twoCoreAmbient le_sup_right
    exact (twoCoreAmbient_le_sylow S (P ⊔ Pstar)
      ((sylow_le_of_pSet hP).trans le_sup_left)).trans
        (sylow_le_of_pSet (pAt_subset_pSet S k hPstar))
  have hE : E = dSubgroup S := le_antisymm hE_le_D hD_le_E
  apply hP_not_le_M
  change P ≤ Subgroup.normalizer (dSubgroup S : Set G)
  have hEset : (E : Set G) = (dSubgroup S : Set G) :=
    congrArg (fun K : Subgroup G => (K : Set G)) hE
  rw [← hEset]
  intro x hxP
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hyE
    change x * y * x⁻¹ ∈ sInf {D : Subgroup G |
      ∃ Pstar : Subgroup G,
        Pstar ∈ pAt S k ∧ D = twoCoreAmbient (P ⊔ Pstar)}
    rw [Subgroup.mem_sInf]
    intro D hD
    rcases hD with ⟨Pstar, hPstar, rfl⟩
    have hycore : y ∈ twoCoreAmbient (P ⊔ Pstar) :=
      hE_le_join_core Pstar hPstar hyE
    have hyjoin : y ∈ P ⊔ Pstar :=
      Subgroup.map_subtype_le (pCore 2 (↥(P ⊔ Pstar))) hycore
    have hxjoin : x ∈ P ⊔ Pstar :=
      (le_sup_left : P ≤ P ⊔ Pstar) hxP
    exact (twoCoreAmbient_normal_subgroupOf (P ⊔ Pstar)).conj_mem
      ⟨y, hyjoin⟩ hycore ⟨x, hxjoin⟩
  · intro hyconj
    change y ∈ sInf {D : Subgroup G |
      ∃ Pstar : Subgroup G,
        Pstar ∈ pAt S k ∧ D = twoCoreAmbient (P ⊔ Pstar)}
    rw [Subgroup.mem_sInf]
    intro D hD
    rcases hD with ⟨Pstar, hPstar, rfl⟩
    have hyconj_core : x * y * x⁻¹ ∈ twoCoreAmbient (P ⊔ Pstar) :=
      hE_le_join_core Pstar hPstar hyconj
    have hyconj_join : x * y * x⁻¹ ∈ P ⊔ Pstar :=
      Subgroup.map_subtype_le (pCore 2 (↥(P ⊔ Pstar))) hyconj_core
    have hxjoin : x ∈ P ⊔ Pstar :=
      (le_sup_left : P ≤ P ⊔ Pstar) hxP
    have := (twoCoreAmbient_normal_subgroupOf (P ⊔ Pstar)).conj_mem
      ⟨x * y * x⁻¹, hyconj_join⟩ hyconj_core
      ⟨x⁻¹, (P ⊔ Pstar).inv_mem hxjoin⟩
    change x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ ∈
      twoCoreAmbient (P ⊔ Pstar) at this
    simpa [mul_assoc] using this

end Stellmacher.SectionFour
