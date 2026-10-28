module

public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDecomposition
public import Theory.GroupAction.SaturatedSupportDisplacement
public import Theory.Comparator.Defs

/-!
# The unique transposition of canonical factors

Aschbacher--Smith, *The Classification of Quasithin Groups*, D.2.12(5),
`refs/quasithin.pdf`, printed p.184.

A moved canonical support has order four. Its difference map is injective,
so it exhausts the involution's full displacement, also of order four.
Independence separates this displacement from the sum of all supports other
than the chosen one. The involution exchanges the chosen factor with its
image and therefore fixes every remaining support pointwise. Mutual
fixedness of action supports and faithfulness then give centralization of
the remaining actors. No nonemptiness assumption is imposed on the family.
-/

open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD
variable {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V] [FaithfulSMul G V]

/-- D.2.12(5): an involution with displacement of order four either normalizes
all canonical rank-two factors, or its permutation exchanges precisely two
of them. In the latter case the whole displacement is generated on their
support sum, and every other factor and its support are centralized. -/
public theorem smallSupportFactors_normalized_or_single_transposition (t : G) (ht : IsInvolution t)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers t) V) = 4) :
    (∀ X ∈ smallSupportFactors G V 1, t ∈ Subgroup.normalizer (X : Set G)) ∨
    ∃ X Y : smallSupportFactors G V 1, X ≠ Y ∧
      smallSupportFactors_conjEquiv (V := V) 1 t X = Y ∧
      smallSupportFactors_conjEquiv (V := V) 1 t Y = X ∧
      (∀ Z : smallSupportFactors G V 1, Z ≠ X → Z ≠ Y →
        smallSupportFactors_conjEquiv (V := V) 1 t Z = Z ∧
        t ∈ Subgroup.centralizer (Z.val : Set G) ∧
        commutatorAction Z.val V ≤ FixedPoints.subgroup (Subgroup.zpowers t) V) ∧
      commutatorAction (Subgroup.zpowers t) V =
        commutatorSubgroup (Subgroup.zpowers t) V
          (commutatorAction X.val V ⊔ commutatorAction Y.val V) := by
  classical
  by_cases hnorm : ∀ X ∈ smallSupportFactors G V 1,
      t ∈ Subgroup.normalizer (X : Set G)
  · exact Or.inl hnorm
  right
  push Not at hnorm
  obtain ⟨X₀, hX₀, hmove⟩ := hnorm
  let X : smallSupportFactors G V 1 := ⟨X₀, hX₀⟩
  let σ := smallSupportFactors_conjEquiv (G := G) (V := V) 1 t
  let U := fun Z : smallSupportFactors G V 1 => commutatorAction Z.val V
  let Y := σ X
  have hinv (Z : smallSupportFactors G V 1) : σ (σ Z) = Z := by
    apply Subtype.ext
    change (Z.val.conjBy t).conjBy t = Z.val
    rw [← Subgroup.conjBy_mul, ← pow_two, ht.2, Subgroup.conjBy_one]
  have hXY : X ≠ Y := by
    intro heq
    apply hmove
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    exact (congrArg Subtype.val heq).symm
  have hYX : σ Y = X := hinv X
  have htransport (Z : smallSupportFactors G V 1) :
      (U Z).map (MulDistribMulAction.toMulAut G V t).toMonoidHom = U (σ Z) :=
    smallSupport_support_conjBy Z.val t
  have hmem (Z : smallSupportFactors G V 1) {v : V} (hv : v ∈ U Z) :
      t • v ∈ U (σ Z) := by
    rw [← htransport]
    exact Subgroup.mem_map_of_mem _ hv
  have hind : iSupIndep U := (smallSupportSupports_internalDirectSum
    (G := G) (V := V) (Or.inl rfl)).1
  have hdis : Disjoint (U X)
      ((U X).map (MulDistribMulAction.toMulAut G V t).toMonoidHom) := by
    rw [htransport]
    exact hind.pairwiseDisjoint hXY
  have hcardU : Nat.card (commutatorAction (Subgroup.zpowers t) V) = Nat.card (U X) := by
    rw [hcard]
    exact (show Nat.card (U X) = 4 from hX₀.2.2).symm
  have hrep (v : V) := commutatorAction_mem_iff_of_disjoint_moved_support_card_eq
    (Subgroup.zpowers t) (U X) t (Subgroup.mem_zpowers t) hdis hcardU v
  -- Independence isolates the chosen support from the sum of all the others.
  let R : Subgroup V := ⨆ (Z : smallSupportFactors G V 1) (_ : Z ≠ X), U Z
  have hUR : Disjoint (U X) R := hind X
  have hrest {Z : smallSupportFactors G V 1} (hZ : Z ≠ X) : U Z ≤ R :=
    le_iSup_of_le Z (le_iSup_of_le hZ le_rfl)
  -- The saturated difference image also meets that complementary sum trivially.
  have hfullR : Disjoint (commutatorAction (Subgroup.zpowers t) V) R := by
    rw [Subgroup.disjoint_def]
    intro v hv hvR
    obtain ⟨u, hu, rfl⟩ := (hrep v).mp hv
    have htu : t • u ∈ R := hrest hXY.symm (hmem X hu)
    have huR : u ∈ R := by
      have hh := R.mul_mem htu (R.inv_mem hvR)
      simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using hh
    have hu1 : u = 1 := hUR.le_bot ⟨hu, huR⟩
    simp [hu1]
  have hfull : commutatorAction (Subgroup.zpowers t) V ≤ U X ⊔ U Y := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := (hrep v).mp hv
    exact (U X ⊔ U Y).mul_mem
      ((le_sup_left : U X ≤ U X ⊔ U Y) ((U X).inv_mem hu))
      ((le_sup_right : U Y ≤ U X ⊔ U Y) (hmem X hu))
  refine ⟨X, Y, hXY, rfl, hYX, ?_, ?_⟩
  · intro Z hZX hZY
    have hσZX : σ Z ≠ X := by
      intro heq
      have hh := congrArg σ heq
      rw [hinv] at hh
      exact hZY hh
    have hfix : U Z ≤ FixedPoints.subgroup (Subgroup.zpowers t) V := by
      intro v hv a
      have hd : v⁻¹ * (t • v) ∈ commutatorAction (Subgroup.zpowers t) V := by
        rw [commutatorAction_eq_closure]
        exact Subgroup.subset_closure ⟨⟨t, Subgroup.mem_zpowers t⟩, v, rfl⟩
      have hdR : v⁻¹ * (t • v) ∈ R :=
        R.mul_mem (R.inv_mem (hrest hZX hv)) (hrest hσZX (hmem Z hv))
      have hvfix : t • v = v := (inv_mul_eq_one.mp (hfullR.le_bot ⟨hd, hdR⟩)).symm
      exact smul_eq_self_of_mem_zpowers a.property hvfix
    have hZfull : commutatorAction (Subgroup.zpowers t) V ≤ FixedPoints.subgroup Z.val V :=
      hfull.trans (sup_le
        (smallSupportFactors_cross_fixed (Or.inl rfl) Z.property X.property
          (fun he => hZX (Subtype.ext he)))
        (smallSupportFactors_cross_fixed (Or.inl rfl) Z.property Y.property
          (fun he => hZY (Subtype.ext he))))
    have hcent : t ∈ Subgroup.centralizer (Z.val : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (ActionSupport.commute_of_cross_fixed (Subgroup.zpowers t) Z.val
        hfix hZfull ⟨t, Subgroup.mem_zpowers t⟩ ⟨z, hz⟩).symm.eq
    refine ⟨?_, hcent, hfix⟩
    apply Subtype.ext
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer _ hcent)
  · apply le_antisymm
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := (hrep v).mp hv
      exact Subgroup.subset_closure ⟨⟨t, Subgroup.mem_zpowers t⟩, u,
        (le_sup_left : U X ≤ U X ⊔ U Y) hu, rfl⟩
    · rw [commutatorSubgroup, Subgroup.closure_le]
      rintro v ⟨a, u, _, rfl⟩
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨a, u, rfl⟩
end CFSG.Quasithin.ChapterD
