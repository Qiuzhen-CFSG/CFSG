module
public import Theory.GroupTheory.SolvableProductKernel
public import Theory.GroupTheory.ElementaryThompsonComponent
public import CFSG.Quasithin.ChapterB.Section02.Thompson

/-!
# The actor and odd line above the Thompson-factorization kernel

If the original maximum elementary Thompson subgroup lay in the maximal
normal product kernel, its Frattini normalizer would cover the quotient.
Thus an actual maximum elementary subgroup escapes the kernel. Combining
this with the odd chief-section construction selects a prime-order line
outside the second normalizer and a fixing hyperplane of the actor image.
The original quotient map is retained throughout.

Source: GLS, Number 2, G.26.18(a), printed pp.152–153. The second theorem
retains the proper-Sylow-overgroup induction premise; it is not the full
factorization theorem. Its literal XR application is in Chapter13's
FFContradiction.KernelSelection.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

/-- Frattini forces an actual maximum elementary subgroup outside the maximal
kernel, since otherwise the first normalizer covers the whole quotient. -/
theorem maximalProductKernel_exists_maximum_outside
    (P : Sylow 2 G) (U V S : Subgroup G)
    (h : IsMaximalProductKernel (P : Subgroup G) U V S) [S.Normal]
    (hPU : (P : Subgroup G) ≤ U)
    (hJU : normalizer (thompsonJ (P : Subgroup G) 0 : Set G) ≤ U)
    (hfail : ¬ NormalizerProductOn (P : Subgroup G) U V ⊤) :
    ∃ A : Subgroup G, A ∈ elementaryAbelianMaxSubgroups (P : Subgroup G) ∧ ¬ A ≤ S := by
  by_contra! hall
  have hJS : elementaryAbelianMaxJ (P : Subgroup G) ≤ S := sSup_le hall
  have hfr := elementaryAbelianMaxJ_frattini_of_le_normal P S hJS
  rw [←thompsonJ_zero] at hfr
  have hUS : U ⊔ S = ⊤ := top_unique (hfr ▸ sup_le_sup_right hJU S)
  let : Nontrivial (G ⧸ S) := QuotientGroup.nontrivial_iff.mpr (h.ne_top _ _ _ _ hfail)
  have hcover : (⊤ : Subgroup (G ⧸ S)) ≤ U.map (QuotientGroup.mk' S) := by
    have hh := congrArg (map (QuotientGroup.mk' S)) hUS
    simpa only [Subgroup.map_sup,QuotientGroup.map_mk'_self,sup_bot_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective S)] using hh.symm.le
  exact h.not_covering_left _ _ _ _ hPU ⊤ top_ne_bot hcover

/-- The odd-line and actor-hyperplane selection above the literal maximal
kernel. Only the proper-overgroup induction premise remains explicit. -/
theorem maximalProductKernel_odd_line [Group.IsSolvable G]
    (P : Sylow 2 G) (U V S : Subgroup G)
    (h : IsMaximalProductKernel (P : Subgroup G) U V S) [S.Normal]
    (hPU : (P : Subgroup G) ≤ U) (hPV : (P : Subgroup G) ≤ V)
    (hJU : normalizer (thompsonJ (P : Subgroup G) 0 : Set G) ≤ U)
    (hfail : ¬ NormalizerProductOn (P : Subgroup G) U V ⊤)
    (hproper : ∀ D : Subgroup G, D.Normal → D ⊔ (P : Subgroup G) ≠ ⊤ →
      NormalizerProductOn (P : Subgroup G) U V D) :
    ∃ (r : ℕ) (A : Subgroup G), r.Prime ∧ Odd r ∧
      A ∈ elementaryAbelianMaxSubgroups (P : Subgroup G) ∧ ¬ A ≤ S ∧
      ∃ (B : Subgroup (A.map (QuotientGroup.mk' S))) (D : Subgroup (G ⧸ S)),
        B.index = 2 ∧ Nat.card D = r ∧
        A.map (QuotientGroup.mk' S) ≤ normalizer (D : Set (G ⧸ S)) ∧
        ⁅D,A.map (QuotientGroup.mk' S)⁆ = D ∧
        D ≤ centralizer (B.map (A.map (QuotientGroup.mk' S)).subtype : Set (G ⧸ S)) ∧
        ¬ D ≤ V.map (QuotientGroup.mk' S) := by
  obtain ⟨r,Y,hr,ho,hYn,hYne,hYe,hmin,_,hYV⟩ := h.odd_chief P U V S hPU hPV hfail
  let := hYn
  let := hYe
  let : Fact r.Prime := ⟨hr⟩
  obtain ⟨A,hA,hAS⟩ := maximalProductKernel_exists_maximum_outside P U V S h hPU hJU hfail
  let : IsElementaryAbelian 2 A := hA.2.1
  let q := QuotientGroup.mk' S
  let Ab := A.map q
  let : IsElementaryAbelian 2 Ab := IsElementaryAbelian.map q
  have hAb : Ab ≠ ⊥ := by
    intro he
    apply hAS
    have hh := (map_eq_bot_iff A).mp he
    simpa only [q,QuotientGroup.ker_mk'] using hh
  obtain ⟨B,D,hB,_,hcard,hAD,hcomm,hfix,hout⟩ :=
    exists_odd_line_of_chief_noncoverage Y ((P : Subgroup G).map q) Ab (V.map q)
      ho hYne (map_mono hA.1) hAb
      (h.sup_sylow_eq_top _ _ _ _ hproper Y hYne)
      (h.pCore_quotient_eq_bot P U V S) (P.isPGroup'.map q) hmin (map_mono hPV) hYV
  exact ⟨r,A,hr,ho,hA,hAS,B,D,hB,hcard,hAD,hcomm,hfix,hout⟩
end CFSG.Quasithin.ChapterB

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- Pulling back an actor-image hyperplane gives the original near-maximum
Thompson subgroup, with the literal image and kernel retained. -/
theorem thompson_hyperplane_preimage (P A : Subgroup G)
    (hA : A ∈ elementaryAbelianMaxSubgroups P) (q : G →* H)
    (Bbar : Subgroup (A.map q)) (hBbar : Bbar.index = 2) :
    ∃ B : Subgroup G, B ∈ thompsonFamily P 1 ∧ B ≤ A ∧ B.relIndex A = 2 ∧
      A ⊓ q.ker ≤ B ∧ B.map q = Bbar.map (A.map q).subtype := by
  let f := q.subgroupMap A
  let F := Bbar.comap f
  let B := F.map A.subtype
  have hf : Function.Surjective f := q.subgroupMap_surjective A
  have hFi : F.index = 2 := (Bbar.index_comap_of_surjective hf).trans hBbar
  have hBA : B ≤ A := map_subtype_le _
  have hi : B.relIndex A = 2 := by
    change (B.comap A.subtype).index = 2
    rw [show B = F.map A.subtype from rfl,comap_map_eq,
      A.subtype.ker_eq_bot A.subtype_injective,sup_bot_eq]
    exact hFi
  have hc : Nat.card B * 2 = Nat.card A := by
    rw [show B = F.map A.subtype from rfl,card_map_of_injective A.subtype_injective,←hFi]
    exact F.card_mul_index
  have hAc : Nat.card A = 2 ^ twoRank P :=
    (elementaryAbelianMaxSubgroups_card_eq P A hA).trans (maxOrder_eq_two_pow_rank P)
  have hr : 1 ≤ twoRank P := by
    by_contra hh
    have hz : twoRank P = 0 := by omega
    rw [hAc,hz,pow_zero] at hc
    omega
  let : IsElementaryAbelian 2 A := hA.2.1
  have hB : B ∈ thompsonFamily P 1 := by
    refine ⟨hBA.trans hA.1,IsElementaryAbelian.of_le hBA,hr,?_⟩
    have hp : 2 ^ (twoRank P - 1) * 2 = 2 ^ twoRank P := by
      rw [←pow_succ,Nat.sub_add_cancel hr]
    rw [hAc,←hp] at hc
    omega
  have hk : A ⊓ q.ker ≤ B := by
    rintro x ⟨hx,hk⟩
    refine ⟨⟨x,hx⟩,?_,rfl⟩
    change f ⟨x,hx⟩ ∈ Bbar
    have he : f ⟨x,hx⟩ = 1 := Subtype.ext hk
    rw [he]
    exact Bbar.one_mem
  have hm : B.map q = Bbar.map (A.map q).subtype := by
    dsimp [B]
    rw [Subgroup.map_map]
    have he : q.comp A.subtype = (A.map q).subtype.comp f := rfl
    rw [he,←Subgroup.map_map]
    congr 1
    exact map_comap_eq_self_of_surjective hf Bbar
  exact ⟨B,hB,hBA,hi,hk,hm⟩
end CFSG.Quasithin.ChapterB
