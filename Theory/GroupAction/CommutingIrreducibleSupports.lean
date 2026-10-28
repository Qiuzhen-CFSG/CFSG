module
public import Theory.GroupAction.IndependentCoprimeSupports
public import Theory.GroupAction.NormalizingActor
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Commuting irreducible coprime supports

If the support of X is irreducible and Y commutes with X, its Y-fixed
subgroup is either full or trivial. In the second case coprime splitting
places the support of X inside that of Y. Equal support cardinalities
therefore give a dichotomy: equal supports or pointwise fixedness.
A faithful group commuting with an irreducible action acts freely on the
nonidentity points, giving an order divisibility bound.
This is the support comparison in Aschbacher--Smith D.2.12, pp.183–184.
-/

open scoped IsMulCommutative
namespace ActionSupport

public theorem support_eq_or_le_fixed_of_commuting_irreducible
    {G V : Type*} [Group G] [Group V] [Finite V] [IsMulCommutative V]
    [MulDistribMulAction G V]
    (X Y : Subgroup G) [Finite Y]
    [IsInvariant X V (commutatorAction X V)]
    (hcomm : Y ≤ Subgroup.centralizer (X : Set G))
    (hcop : Nat.Coprime (Nat.card Y) (Nat.card V))
    (hcard : Nat.card (commutatorAction X V) = Nat.card (commutatorAction Y V))
    (hirred : ∀ D : Subgroup (commutatorAction X V),
      IsInvariant X (commutatorAction X V) D → D = ⊥ ∨ D = ⊤) :
    commutatorAction X V = commutatorAction Y V ∨
      commutatorAction X V ≤ FixedPoints.subgroup Y V := by
  let W := commutatorAction X V
  let _ : IsInvariant Y V W := commutatorAction_isInvariant_of_normalizing_actor Y X
    (hcomm.trans (Subgroup.centralizer_le_normalizer _))
  have hxy (x : X) (y : Y) (v : W) : x • (y • v) = y • (x • v) := by
    apply Subtype.ext
    change (x : G) • ((y : G) • (v : V)) = (y : G) • ((x : G) • (v : V))
    rw [← mul_smul, ← mul_smul,
      (Subgroup.mem_centralizer_iff.mp (hcomm y.property)) x x.property]
  let D := FixedPoints.subgroup Y W
  have hinv : IsInvariant X W D := by
    constructor
    intro x v
    constructor
    · intro hv y
      rw [← hxy, hv y]
    · intro hv y
      apply (smul_left_cancel_iff x).mp
      rw [hxy]
      exact hv y
  rcases hirred D hinv with hbot | htop
  · left
    have hcopW : Nat.Coprime (Nat.card Y) (Nat.card W) :=
      hcop.of_dvd_right W.card_subgroup_dvd_card
    have hsplit :=
      isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        (A := Y) (G := W)
        (Group.isSolvable_of_comm (fun x y : W => IsMulCommutative.is_comm.comm x y))
        hcopW inferInstance
    have hfull : commutatorAction Y W = ⊤ := by
      have hh := hsplit.sup_eq_top
      change D ⊔ commutatorAction Y W = ⊤ at hh
      simpa [hbot] using hh
    have hle : W ≤ commutatorAction Y V := by
      have hm : commutatorAction Y W ≤ (commutatorAction Y V).comap W.subtype := by
        rw [commutatorAction_eq_closure]
        refine (Subgroup.closure_le _).mpr ?_
        rintro _ ⟨y, v, rfl⟩
        change (v : V)⁻¹ * (y : G) • (v : V) ∈ commutatorAction Y V
        rw [commutatorAction_eq_closure]
        exact Subgroup.subset_closure ⟨y, (v : V), rfl⟩
      intro v hv
      exact hm (hfull ▸ (show (⟨v, hv⟩ : W) ∈ (⊤ : Subgroup W) from trivial))
    exact Subgroup.eq_of_le_of_card_ge hle hcard.ge
  · right
    intro v hv y
    exact congrArg Subtype.val (show y • (⟨v, hv⟩ : W) = ⟨v, hv⟩ from
      (htop ▸ (show (⟨v, hv⟩ : W) ∈ (⊤ : Subgroup W) from trivial)) y)

/-- A commuting join whose second support lies in the first is faithful on
that support whenever the ambient action is faithful. -/
public theorem eq_one_of_fixes_support_of_commuting_join
    {G V : Type*} [Group G] [Group V] [Finite V] [IsMulCommutative V]
    [MulDistribMulAction G V] [FaithfulSMul G V]
    (X Y : Subgroup G) [Finite X]
    (hcomm : Y ≤ Subgroup.centralizer (X : Set G))
    (hcop : Nat.Coprime (Nat.card X) (Nat.card V))
    (hsupport : commutatorAction Y V ≤ commutatorAction X V)
    (g : ↥(X ⊔ Y)) (hfix : ∀ v ∈ commutatorAction X V, (g : G) • v = v) :
    (g : G) = 1 := by
  let C := FixedPoints.subgroup X V
  let W := commutatorAction X V
  have hcompl := fixed_support_isCompl X hcop
  have hYfix (y : Y) (c : V) (hc : c ∈ C) : (y : G) • c = c := by
    have hdW : c⁻¹ * (y : G) • c ∈ W := by
      apply hsupport
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨y, c, rfl⟩
    have hdC : c⁻¹ * (y : G) • c ∈ C := by
      intro x
      have hxc : (x : G) • c = c := hc x
      have hxyc : (x : G) • ((y : G) • c) = (y : G) • c := by
        rw [← mul_smul, (Subgroup.mem_centralizer_iff.mp (hcomm y.property)) x x.property,
          mul_smul, hxc]
      change (x : G) • (c⁻¹ * (y : G) • c) = _
      rw [smul_mul', smul_inv', hxc, hxyc]
    exact (inv_mul_eq_one.mp (hcompl.disjoint.le_bot ⟨hdC, hdW⟩)).symm
  have hjoin : X ⊔ Y ≤ fixingSubgroup G (C : Set V) := by
    apply sup_le
    · intro x hx
      rw [mem_fixingSubgroup_iff]
      intro c hc
      exact hc ⟨x, hx⟩
    · intro y hy
      rw [mem_fixingSubgroup_iff]
      exact hYfix ⟨y, hy⟩
  apply eq_of_smul_eq_smul (α := V)
  intro v
  have hv : v ∈ C ⊔ W := by rw [hcompl.sup_eq_top]; trivial
  let _ : C.Normal := Subgroup.normal_of_isMulCommutative _
  obtain ⟨c, hc, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hv
  have hgc := (mem_fixingSubgroup_iff (M := G)).mp (hjoin g.property) c hc
  simp only [smul_mul', hgc, hfix w hw, one_smul]

/-- A faithful group commuting with an irreducible action acts freely away from
the identity, so its order divides the number of nonidentity points. -/
public theorem card_dvd_card_sub_one_of_commuting_irreducible
    {A H W : Type*} [Group A] [Group H] [Finite H] [Group W] [Finite W]
    [MulDistribMulAction A W] [MulDistribMulAction H W] [FaithfulSMul H W]
    (hcomm : ∀ a : A, ∀ h : H, ∀ w : W, a • (h • w) = h • (a • w))
    (hirred : ∀ D : Subgroup W, IsInvariant A W D → D = ⊥ ∨ D = ⊤) :
    Nat.card H ∣ Nat.card W - 1 := by
  classical
  have hfree (h : H) (v : W) (hv : v ≠ 1) (hhv : h • v = v) : h = 1 := by
    let D : Subgroup W := FixedPoints.subgroup (Subgroup.zpowers h) W
    have hD (w : W) : w ∈ D ↔ h • w = w := by
      constructor
      · intro hw
        exact hw ⟨h, Subgroup.mem_zpowers h⟩
      · intro hw k
        exact smul_eq_self_of_mem_zpowers k.property hw
    have hinv : IsInvariant A W D := by
      constructor
      intro a w
      rw [hD, hD, ← hcomm]
      exact (smul_left_cancel_iff a).symm
    rcases hirred D hinv with hbot | htop
    · exact (hv (Subgroup.mem_bot.mp (hbot ▸ (hD v).mpr hhv))).elim
    · apply eq_of_smul_eq_smul (α := W)
      intro w
      simpa only [one_smul] using (hD w).mp (htop ▸ Subgroup.mem_top w)
  let P := {v : W // v ≠ 1}
  let _ : MulAction H P := {
    smul h v := ⟨h • (v : W), by
      intro heq
      apply v.property
      apply (MulDistribMulAction.toMulAut H W h).injective
      simpa using heq⟩
    one_smul v := by apply Subtype.ext; exact one_smul H (v : W)
    mul_smul h k v := by apply Subtype.ext; exact mul_smul h k (v : W) }
  have hstab (v : P) : MulAction.stabilizer H v = ⊥ := by
    apply bot_unique
    intro h hh
    exact Subgroup.mem_bot.mpr (hfree h v v.property (congrArg Subtype.val hh))
  have hcount := Nat.card_congr
    (MulAction.selfEquivOrbitsQuotientProd (G := H) (X := P) hstab)
  rw [Nat.card_prod] at hcount
  have hP : Nat.card P = Nat.card W - 1 := by
    let _ : Fintype W := Fintype.ofFinite W
    change Nat.card {v : W // ¬v = 1} = Nat.card W - 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp [Nat.card_eq_fintype_card]
  rw [hP] at hcount
  exact ⟨Nat.card (Quotient (MulAction.orbitRel H P)), by
    simpa only [Nat.mul_comm] using hcount⟩

end ActionSupport
