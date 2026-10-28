module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.ModelGeneration
/-!
# Generation in the permutation alternatives of 14.4.2

The two-residual of a product is the product of the two residuals. On the
cubic axis, a nontrivial elementary two-group cannot centralize A₃. On the
A₅ axis the centralizer in S₅ is trivial. The exact order eight forces both
projections to be nontrivial, and axis commutators give the full A₃ × A₅.
The S₃ × A₅ case uses its actual embedding in S₃ × S₅. The S₇ branch uses
its actual alternating residual and its trivial centralizer.

Source: Aschbacher–Smith, 14.4.2(4),(5) and 14.4.7, printed pp.1006,1009.
The application, including the literal quotient and source ranks, is in
`ModelGeneration.SourceCases`.
-/

public section
open Subgroup
open Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.ModelGeneration
variable {G H : Type*} [Group G] [Group H]
private theorem residual_prod (p : ℕ) : pResidual p (G × H) =
    (pResidual p G).prod (pResidual p H) := by
  apply le_antisymm
  · intro x hx
    exact ⟨map_pResidual_le p (MonoidHom.fst G H) (mem_map_of_mem _ hx),
      map_pResidual_le p (MonoidHom.snd G H) (mem_map_of_mem _ hx)⟩
  · exact prod_le_iff.mpr ⟨map_pResidual_le p (MonoidHom.inl G H),
      map_pResidual_le p (MonoidHom.inr G H)⟩
private theorem inl_commutator (A : Subgroup G) (X : Subgroup (G × H)) :
    ⁅A.map (MonoidHom.inl G H), X⁆ =
      (⁅A, X.map (MonoidHom.fst G H)⁆).map (MonoidHom.inl G H) := by
  apply le_antisymm
  · apply commutator_le.mpr
    rintro _ ⟨a,ha,rfl⟩ x hx
    refine ⟨⁅a,x.1⁆, commutator_mem_commutator ha (mem_map_of_mem _ hx), ?_⟩
    ext <;> simp [commutatorElement_def]
  · apply map_le_iff_le_comap.mpr
    apply commutator_le.mpr
    rintro a ha _ ⟨x,hx,rfl⟩
    have h := commutator_mem_commutator (mem_map_of_mem (MonoidHom.inl G H) ha) hx
    change (MonoidHom.inl G H) ⁅a,x.1⁆ ∈ ⁅A.map (MonoidHom.inl G H), X⁆
    have he : (MonoidHom.inl G H) ⁅a,x.1⁆ = ⁅(MonoidHom.inl G H) a,x⁆ := by
      ext <;> simp [commutatorElement_def]
    rwa [he]
private theorem inr_commutator (A : Subgroup H) (X : Subgroup (G × H)) :
    ⁅A.map (MonoidHom.inr G H), X⁆ =
      (⁅A, X.map (MonoidHom.snd G H)⁆).map (MonoidHom.inr G H) := by
  apply le_antisymm
  · apply commutator_le.mpr
    rintro _ ⟨a,ha,rfl⟩ x hx
    refine ⟨⁅a,x.2⁆, commutator_mem_commutator ha (mem_map_of_mem _ hx), ?_⟩
    ext <;> simp [commutatorElement_def]
  · apply map_le_iff_le_comap.mpr
    apply commutator_le.mpr
    rintro a ha _ ⟨x,hx,rfl⟩
    have h := commutator_mem_commutator (mem_map_of_mem (MonoidHom.inr G H) ha) hx
    change (MonoidHom.inr G H) ⁅a,x.2⁆ ∈ ⁅A.map (MonoidHom.inr G H), X⁆
    have he : (MonoidHom.inr G H) ⁅a,x.2⁆ = ⁅(MonoidHom.inr G H) a,x⁆ := by
      ext <;> simp [commutatorElement_def]
    rwa [he]
private theorem simple_normal_commutator (A X : Subgroup G) [A.Normal] [IsSimpleGroup A]
    (h : ¬ X ≤ centralizer (A : Set G)) : ⁅A,X⁆ = A := by
  have hle : ⁅A,X⁆ ≤ A := commutator_le_left A X
  let : (⁅A,X⁆.subgroupOf A).Normal :=
    (normal_subgroupOf_iff_le_normalizer hle).mpr (normalizer_commutator_ge_left A X)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅A,X⁆.subgroupOf A) inferInstance with hb | ht
  · have he := congrArg (Subgroup.map A.subtype) hb
    rw [map_subgroupOf_eq_of_le hle, Subgroup.map_bot, commutator_comm] at he
    exact (h (commutator_eq_bot_iff_le_centralizer.mp he)).elim
  · exact le_antisymm hle (subgroupOf_eq_top.mp ht)

local notation "S3" => Equiv.Perm (Fin 3)
local notation "S5" => Equiv.Perm (Fin 5)
local notation "A3" => alternatingGroup (Fin 3)
local notation "A5" => alternatingGroup (Fin 5)
private theorem three_involution (x : S3) (hx : x ^ 2 = 1)
    (hc : ∀ a : S3, a ∈ A3 → a*x=x*a) : x = 1 := by
  have h : ∀ x : S3, x ^ 2 = 1 →
      (∀ a : S3, Equiv.Perm.sign a = 1 → a*x=x*a) → x = 1 := by decide +kernel
  exact h x hx (by simpa only [Equiv.Perm.mem_alternatingGroup] using hc)
private theorem three_generation (X : Subgroup S3) (hn : X ≠ ⊥)
    (he : IsElementaryAbelian 2 X) : ⁅A3,X⁆ = A3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsSimpleGroup A3 := isSimpleGroup_of_prime_card (p := 3) (by
    rw [Nat.card_eq_fintype_card]; decide +kernel)
  apply simple_normal_commutator
  intro hc
  apply hn
  apply le_bot_iff.mp
  intro x hx
  exact three_involution x (elemPow_eq_one_of_isElementaryAbelian x hx)
    (mem_centralizer_iff.mp (hc hx))
private theorem five_generation (X : Subgroup S5) (hn : X ≠ ⊥) : ⁅A5,X⁆ = A5 := by
  let : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
  apply simple_normal_commutator
  intro hc
  rw [GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 5 (by decide)] at hc
  exact hn (le_bot_iff.mp hc)
private theorem product_generation (X : Subgroup (S3 × S5)) (hc : Nat.card X = 8)
    (he : IsElementaryAbelian 2 X) : ⁅(A3).prod A5,X⁆ = (A3).prod A5 := by
  apply le_antisymm (commutator_le_left _ _)
  apply prod_le_iff.mpr
  constructor
  · have hh := three_generation (X.map (MonoidHom.fst _ _))
      (CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.ProductModel.snd_nonbot_of_card_eight hc he) (he.map _)
    have hid : (A3).map (MonoidHom.inl S3 S5) = ⁅(A3).map (MonoidHom.inl S3 S5),X⁆ := by
      rw [inl_commutator,hh]
    calc
      _ = _ := hid
      _ ≤ _ := commutator_mono (by rintro _ ⟨x,hx,rfl⟩; exact ⟨hx,one_mem _⟩) le_rfl
  · have hh := five_generation (X.map (MonoidHom.snd _ _))
      (CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.ProductModel.fst_nonbot_of_card_eight hc he)
    have hid : (A5).map (MonoidHom.inr S3 S5) = ⁅(A5).map (MonoidHom.inr S3 S5),X⁆ := by
      rw [inr_commutator,hh]
    calc
      _ = _ := hid
      _ ≤ _ := commutator_mono (by rintro _ ⟨x,hx,rfl⟩; exact ⟨one_mem _,hx⟩) le_rfl
private theorem perfect_residual [Finite G] [Group.IsPerfect G] : pResidual 2 G = ⊤ := by
  apply (pResidual_eq_top_iff 2 G).mpr
  intro N hN hp
  let := hN
  have : Subsingleton (G ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent _ hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The order-eight elementary actor generates the actual residual of S₃ × S₅. -/
theorem symmetric_product_residual_generation (X : Subgroup (S3 × S5))
    (hc : Nat.card X = 8) (he : IsElementaryAbelian 2 X) :
    ⁅pResidual 2 (S3 × S5), X⁆ = pResidual 2 (S3 × S5) := by
  rw [residual_prod, Equiv.Perm.twoResidual_eq_alternating,
    Equiv.Perm.twoResidual_eq_alternating]
  exact product_generation X hc he

/-- The same calculation in the literal S₃ × A₅ carrier. -/
theorem alternating_product_residual_generation (X : Subgroup (S3 × A5))
    (hc : Nat.card X = 8) (he : IsElementaryAbelian 2 X) :
    ⁅pResidual 2 (S3 × A5), X⁆ = pResidual 2 (S3 × A5) := by
  let f : S3 × A5 →* S3 × S5 := (MonoidHom.id S3).prodMap (A5).subtype
  have hf : Function.Injective f := by
    rintro ⟨a,b⟩ ⟨c,d⟩ hh
    change (a,(b : S5)) = (c,(d : S5)) at hh
    exact Prod.ext (congrArg (fun x : S3 × S5 => x.1) hh)
      (Subtype.ext (congrArg (fun x : S3 × S5 => x.2) hh))
  let : Group.IsPerfect A5 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hres : (pResidual 2 (S3 × A5)).map f = (A3).prod A5 := by
    rw [residual_prod, Equiv.Perm.twoResidual_eq_alternating, perfect_residual]
    ext x
    constructor
    · rintro ⟨⟨a,b⟩,hab,rfl⟩
      exact ⟨hab.1,b.property⟩
    · intro hx
      exact ⟨(x.1,⟨x.2,hx.2⟩),⟨hx.1,mem_top _⟩,rfl⟩
  apply Subgroup.map_injective hf
  rw [map_commutator, hres]
  exact product_generation (X.map f)
    ((card_map_of_injective hf).trans hc) (he.map f)

/-- The actual residual of S₇ is generated by every subgroup of order eight. -/
theorem symmetric_seven_residual_generation (X : Subgroup (Equiv.Perm (Fin 7)))
    (hc : Nat.card X = 8) :
    ⁅pResidual 2 (Equiv.Perm (Fin 7)),X⁆ = pResidual 2 (Equiv.Perm (Fin 7)) := by
  rw [Equiv.Perm.twoResidual_eq_alternating]
  exact CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.symmetric_seven_generation
    _ X (MulEquiv.refl _) (GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 7 (by decide)) hc
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.ModelGeneration
