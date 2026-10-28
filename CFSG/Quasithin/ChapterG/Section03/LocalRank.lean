module

public import CFSG.Quasithin.ChapterG.Section03.LocalRank.Core
public import CFSG.Quasithin.ChapterG.Section03.LocalRank.PointRadical
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# The local rank formula and dimension bound in G.3.1

Full action makes each orbit block the nonzero vectors in its span. The point
stabilizer normalizes the image of its root group and is transitive on the
nonidentity elements of the point radical; hence that image is full. Counting
forms that vanish on the center line gives image rank `dim - 1`, and the
image/kernel cardinality formula gives the asserted generator-rank equality.

For the dimension bound, the decomposition places the block kernels in the
normal binary radical of the total span, hence in the intrinsic `O₂(G)`.
Consequently the root image surjects onto the source quotient image. Its rank
is greater than one, so the block dimension is at least three.

This proves only the conditional local-structure helper: the source G.3.1
assembly must still construct `FullAction` and `Decomposition`.
Source: Aschbacher--Smith, G.3.1, printed pp. 337--338 (PDF pp. 348--349).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section03
namespace LocalRank
open scoped IsMulCommutative
open BinaryLinear BinaryTransvectionGroups

private theorem elementary_rank_eq_finrank {p : ℕ} [Fact p.Prime]
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian p E] :
    Group.rank E = Module.finrank (ZMod p) (Additive E) := by
  classical
  apply le_antisymm (IsElementaryAbelian.rank_le_finrank E)
  obtain ⟨S, hcard, hS⟩ := Group.rank_spec E
  let T := S.image Additive.ofMul
  let W := Submodule.span (ZMod p) (T : Set (Additive E))
  have htop : W.toAddSubgroup.toSubgroup' = (⊤ : Subgroup E) := by
    apply top_unique
    rw [← hS]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    change Additive.ofMul g ∈ W
    exact Submodule.subset_span (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  have hW : W = ⊤ := by
    apply top_unique
    intro a _
    exact (show Additive.toMul a ∈ W.toAddSubgroup.toSubgroup' from htop ▸ Subgroup.mem_top _)
  have hd := finrank_span_finset_le_card (R := ZMod p) (M := Additive E) T
  change Module.finrank (ZMod p) W ≤ T.card at hd
  rw [hW, finrank_top] at hd
  exact hd.trans ((Finset.card_image_le).trans_eq hcard)

private theorem elementary_card_eq_pow_rank {p : ℕ} [Fact p.Prime]
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian p E] :
    Nat.card E = p ^ Group.rank E := by
  rw [elementary_rank_eq_finrank (p := p) E, Nat.card_congr Additive.ofMul,
    Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]

private theorem rank_range_add_ker {E H : Type*} [Group E] [Group H] [Finite E]
    (f : E →* H) [IsElementaryAbelian 2 E]
    [IsElementaryAbelian 2 f.range] [IsElementaryAbelian 2 f.ker] :
    Group.rank E = Group.rank f.range + Group.rank f.ker := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  apply (Nat.pow_right_injective (by decide : 1 < 2))
  change 2 ^ Group.rank E = 2 ^ (Group.rank f.range + Group.rank f.ker)
  rw [← elementary_card_eq_pow_rank (p := 2) E, pow_add,
    ← elementary_card_eq_pow_rank (p := 2) f.range,
    ← elementary_card_eq_pow_rank (p := 2) f.ker]
  rw [← Subgroup.index_ker]
  exact f.ker.index_mul_card.symm

private theorem rank_range_le_of_ker_le {E H K : Type*} [Group E] [Group H] [Group K]
    [Finite E] (f : E →* H) (q : E →* K) (hker : f.ker ≤ q.ker) :
    Group.rank q.range ≤ Group.rank f.range := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let : Finite q.range := Finite.of_surjective q.rangeRestrict q.rangeRestrict_surjective
  have hk : f.ker ≤ q.rangeRestrict.ker := by rwa [MonoidHom.ker_rangeRestrict]
  let l := QuotientGroup.lift f.ker q.rangeRestrict hk
  have hl : Function.Surjective l :=
    QuotientGroup.lift_surjective_of_surjective _ _ q.rangeRestrict_surjective hk
  have hr := Group.rank_le_of_surjective l hl
  rw [Group.rank_congr (QuotientGroup.quotientKerEquivRange f)] at hr
  exact hr

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private def quotientRootMap (G : Subgroup (GL V)) (x : V) :
    rootGroup G x →* G ⧸ pCore 2 G :=
  (QuotientGroup.mk' (pCore 2 G)).comp (Subgroup.inclusion (rootGroup_le G x))

private theorem quotientRootMap_range (G : Subgroup (GL V)) (x : V) :
    (quotientRootMap G x).range = rootQuotientImage G x := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨⟨g.val, rootGroup_le G x g.property⟩, g.property, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g.val, hg⟩, rfl⟩

/-- The source quotient image is a quotient of the faithful root restriction image. -/
theorem quotient_rank_le_rootImage {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) (hdec : Decomposition G Δ) (i : OrbitBlock G Δ)
    {x : V} (hx : x ∈ i.val) :
    Group.rank (rootQuotientImage G x) ≤ Group.rank (rootAction i hx).range := by
  rw [← quotientRootMap_range]
  apply rank_range_le_of_ker_le
  intro g hg
  apply (QuotientGroup.eq_one_iff _).mpr
  exact root_kernel_mem_pCore h hdec i hx ⟨g, (rootAction_ker i hx) ▸ hg⟩

/-- The quotient-rank hypothesis guarantees a nontrivial restriction at every center. -/
theorem rootImage_ne_bot {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) (hdec : Decomposition G Δ) (i : OrbitBlock G Δ)
    {x : V} (hx : x ∈ i.val) : (rootAction i hx).range ≠ ⊥ := by
  intro he
  have hq := quotient_rank_le_rootImage h hdec i hx
  have hr := h.rank_gt_one x (block_subset h i hx)
  have hz : Group.rank (rootAction i hx).range = 0 :=
    (Subgroup.rank_congr he).trans (Group.rank_eq_zero _)
  rw [hz] at hq
  omega

/-- The faithful image of a root group has rank one less than the block dimension. -/
theorem rootImage_rank {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) (hfull : FullAction G Δ) (hdec : Decomposition G Δ)
    (i : OrbitBlock G Δ) {x : V} (hx : x ∈ i.val) :
    Group.rank (rootAction i hx).range = Module.finrank (ZMod 2) (blockSpace G Δ i) - 1 := by
  let : Finite (rootAction i hx).range :=
    Finite.of_surjective _ (rootAction i hx).rangeRestrict_surjective
  let : IsElementaryAbelian 2 (rootAction i hx).range :=
    elementaryAbelian_of_le_radical (rootAction i hx).range.subtype Subtype.val_injective
      (centerLine (⟨x, Submodule.subset_span hx⟩ : blockSpace G Δ i))
      (fun g => rootAction_range_le_radical i hx g.property)
  have hcard : Nat.card (rootAction i hx).range =
      2 ^ (Module.finrank (ZMod 2) (blockSpace G Δ i) - 1) := by
    rw [rootAction_range_eq_radical h hfull i hx (rootImage_ne_bot h hdec i hx)]
    exact point_radical_card
      (fun he => h.nonzero x (block_subset h i hx) (congrArg Subtype.val he))
  exact Nat.pow_right_injective (by decide : 1 < 2)
    ((elementary_card_eq_pow_rank (p := 2) (rootAction i hx).range).symm.trans hcard)

/-- Generator rank splits as image rank plus the rank of the actual fixing kernel. -/
theorem root_rank_formula {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) (hfull : FullAction G Δ) (hdec : Decomposition G Δ)
    (i : OrbitBlock G Δ) {x : V} (hx : x ∈ i.val) :
    Group.rank (rootGroup G x) = Module.finrank (ZMod 2) (blockSpace G Δ i) - 1 +
      Group.rank (fixingKernel (rootGroup G x) (blockSpace G Δ i)) := by
  let : IsElementaryAbelian 2 (rootGroup G x) := rootGroup_elementaryAbelian G x
  let : IsElementaryAbelian 2 (rootAction i hx).range :=
    elementaryAbelian_of_le_radical (rootAction i hx).range.subtype Subtype.val_injective
      (centerLine (⟨x, Submodule.subset_span hx⟩ : blockSpace G Δ i))
      (fun g => rootAction_range_le_radical i hx g.property)
  let : IsElementaryAbelian 2 (rootAction i hx).ker :=
    elementaryAbelian_of_le_radical
      ((rootGroup G x).subtype.comp (rootAction i hx).ker.subtype)
      (Subtype.val_injective.comp Subtype.val_injective) (centerLine x)
      (fun g => g.val.property.2)
  have hr := rank_range_add_ker (rootAction i hx)
  rw [rootImage_rank h hfull hdec i hx, rootAction_ker i hx] at hr
  exact hr

/-- The intrinsic quotient-rank hypothesis excludes dimensions zero, one, and two. -/
theorem dimension_ge_three {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) (hfull : FullAction G Δ) (hdec : Decomposition G Δ)
    (i : OrbitBlock G Δ) : 3 ≤ Module.finrank (ZMod 2) (blockSpace G Δ i) := by
  obtain ⟨x, hx, hi⟩ := i.property
  have hxi : x ∈ i.val := hi ▸ MulAction.mem_orbit_self x
  have hq := quotient_rank_le_rootImage h hdec i hxi
  have hr := h.rank_gt_one x hx
  rw [rootImage_rank h hfull hdec i hxi] at hq
  omega

end LocalRank

open BinaryLinear BinaryTransvectionGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- G.3.1's local assertions, conditional on its full-action and decomposition conclusions. -/
theorem localStructure_of_decomposition {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) (hfull : FullAction G Δ) (hdec : Decomposition G Δ) :
    LocalStructure G Δ where
  dimension_ge_three := LocalRank.dimension_ge_three h hfull hdec
  all_points := LocalRank.all_points h hfull
  kernel_elementary := block_kernel_elementaryAbelian G Δ
  rank_formula := fun i _x hx => LocalRank.root_rank_formula h hfull hdec i hx

end CFSG.Quasithin.ChapterG.Section03
