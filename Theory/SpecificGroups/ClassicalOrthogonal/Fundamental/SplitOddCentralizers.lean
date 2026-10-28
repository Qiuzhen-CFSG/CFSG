module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.ResidualContainment
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.ResidualEquality
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.IsometryQuotients
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# Odd and split orthogonal fundamental blocks

The first four coordinates carry the marked left determinant-space SL₂.
Extension by the identity on the actual complement gives a proper injective
subgroup of the literal projective Omega carrier. The commuting right SL₂
and complementary Omega embed before projectivization; their exact projective
kernel consists of a common square-one scalar on both natural spaces.

The ternary and split-four cubic witnesses extend to every required complement.
Siegel and SL₂ transvection generation put the whole right block image inside
O^{p′}(C(K)), including over F₃. Thus the literal nested residual contains an
actual elementary abelian group of order nine in odd ranks at least three
and split ranks at least four. These conclusions have no structural premises.

For finite fields of odd characteristic the complementary full-isometry
quotient has prime-to-characteristic order. The lifted centralizer calculation
therefore proves exact residual-image equality. The resulting unconditional
central-product equivalences retain the literal common-scalar kernel and the
original quotient maps. The earlier conditional equivalences remain available.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, A.2.17, printed p.39. The ranks here correspond to
natural dimensions 2n+1 and 2n, with complements of ranks n-2.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Fundamental

open Matrix
namespace SplitOddBlocks
variable {F : Type*} [Field F]

/-- Every positive odd rank contains the original ternary cubic. -/
theorem odd_exists_cubic {n : ℕ} (hn : 1 ≤ n) : ∃ b : OmegaOdd n F, orderOf b = 3 := by
  obtain ⟨b, hb⟩ := oddRankOne_exists_cubic (F := F)
  have heq : n = (n - 1) + 1 := by omega
  rw [heq]
  let f : OmegaOdd 1 F →* OmegaOdd ((n - 1) + 1) F :=
    (oddBlocks (n - 1) 1).comp (MonoidHom.inr _ _)
  have hf : Function.Injective f := by
    intro a b hab
    exact congrArg Prod.snd (oddBlocks_injective (n - 1) 1 hab)
  exact ⟨f b, (orderOf_injective f hf b).trans hb⟩

/-- Every split rank at least two contains the marked four-space cubic. -/
theorem plus_exists_cubic {n : ℕ} (hn : 2 ≤ n) : ∃ b : OmegaPlus n F, orderOf b = 3 := by
  obtain ⟨b, hb⟩ := plusRankTwo_exists_cubic (F := F)
  have heq : n = 2 + (n - 2) := by omega
  rw [heq]
  let f : OmegaPlus 2 F →* OmegaPlus (2 + (n - 2)) F :=
    (plusBlocks 2 (n - 2)).comp (MonoidHom.inl _ _)
  have hf : Function.Injective f := by
    intro a b hab
    exact congrArg Prod.fst (plusBlocks_injective 2 (n - 2) hab)
  exact ⟨f b, (orderOf_injective f hf b).trans hb⟩

end SplitOddBlocks

namespace SplitOddCentralizers
open Matrix SplitOddBlocks
variable {F : Type*} [Field F]

def rankCastD {a b : ℕ} (h : a = b) : (formD a F).IsometryEquiv (formD b F) := by
  subst b
  exact QuadraticMap.IsometryEquiv.refl _

def rankCastB {a b : ℕ} (h : a = b) : (formB a F).IsometryEquiv (formB b F) := by
  subst b
  exact QuadraticMap.IsometryEquiv.refl _

/-- The first four coordinates and the literal split complement. -/
def plusCoordinates (n : ℕ) (hn : 2 ≤ n) :
    ((formD 2 F).prod (formD (n - 2) F)).IsometryEquiv (formD n F) :=
  (splitDIsometry 2 (n - 2)).symm.trans (rankCastD (by omega))

/-- The first four coordinates and the literal odd complement. -/
def oddCoordinates (n : ℕ) (hn : 2 ≤ n) :
    ((formD 2 F).prod (formB (n - 2) F)).IsometryEquiv (formB n F) :=
  (splitBIsometry 2 (n - 2)).symm.trans (rankCastB (by omega))

def plusLeft (n : ℕ) (hn : 2 ≤ n) : Matrix.SpecialLinearGroup (Fin 2) F →* POmegaPlus n F :=
  leftProjective _ _ (plusCoordinates (F := F) n hn)

def oddLeft (n : ℕ) (hn : 2 ≤ n) : Matrix.SpecialLinearGroup (Fin 2) F →* POmegaOdd n F :=
  leftProjective _ _ (oddCoordinates (F := F) n hn)

/-- The marked fundamental subgroup in the split projective carrier. -/
def plusFundamental (n : ℕ) (hn : 2 ≤ n) : Subgroup (POmegaPlus n F) := (plusLeft (F := F) n hn).range

/-- The marked fundamental subgroup in the odd projective carrier. -/
def oddFundamental (n : ℕ) (hn : 2 ≤ n) : Subgroup (POmegaOdd n F) := (oddLeft (F := F) n hn).range

/-- The literal right-factor/complement covering homomorphism. -/
def plusCover (n : ℕ) (hn : 2 ≤ n) :
    Matrix.SpecialLinearGroup (Fin 2) F × OmegaPlus (n - 2) F →* OmegaPlus n F :=
  rightCover _ _ (plusCoordinates (F := F) n hn)

/-- The literal right-factor/complement covering homomorphism. -/
def oddCover (n : ℕ) (hn : 2 ≤ n) :
    Matrix.SpecialLinearGroup (Fin 2) F × OmegaOdd (n - 2) F →* OmegaOdd n F :=
  rightCover _ _ (oddCoordinates (F := F) n hn)

theorem plusCover_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (plusCover (F := F) n hn) := rightCover_injective _ _ _

theorem oddCover_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (oddCover (F := F) n hn) := rightCover_injective _ _ _

private theorem plusSpace_nontrivial {k : ℕ} (hk : 0 < k) : Nontrivial (VectorD k F) := by
  let : Nonempty (Index k) := ⟨Sum.inl ⟨0, hk⟩⟩
  infer_instance

theorem plusLeft_injective {n : ℕ} (hn : 4 ≤ n) :
    Function.Injective (plusLeft (F := F) n (by omega)) := by
  let := plusSpace_nontrivial (F := F) (k := n - 2) (by omega)
  exact leftProjective_injective _ _ _

theorem oddLeft_injective {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective (oddLeft (F := F) n (by omega)) := leftProjective_injective _ _ _

theorem plusFundamental_proper {n : ℕ} (hn : 4 ≤ n) :
    plusFundamental (F := F) n (by omega) ≠ ⊤ := by
  let := plusSpace_nontrivial (F := F) (k := n - 2) (by omega)
  exact leftProjective_proper _ _ _

theorem oddFundamental_proper {n : ℕ} (hn : 3 ≤ n) :
    oddFundamental (F := F) n (by omega) ≠ ⊤ := leftProjective_proper _ _ _

/-- Exact scalar membership in the split complement is kept in this test. -/
theorem plusCover_projective_kernel (n : ℕ) (hn : 2 ≤ n)
    (g : Matrix.SpecialLinearGroup (Fin 2) F × OmegaPlus (n - 2) F) :
    projectiveElementaryMap (formD n F) (plusCover (F := F) n hn g) = 1 ↔
      ∃ c : F, c ^ 2 = 1 ∧ g.1.val = Matrix.scalar (Fin 2) c ∧
        ∀ v, g.2.val.val v = c • v := rightProjective_kernel _ _ _ _

/-- Exact scalar membership in the odd complement is kept in this test. -/
theorem oddCover_projective_kernel (n : ℕ) (hn : 2 ≤ n)
    (g : Matrix.SpecialLinearGroup (Fin 2) F × OmegaOdd (n - 2) F) :
    projectiveElementaryMap (formB n F) (oddCover (F := F) n hn g) = 1 ↔
      ∃ c : F, c ^ 2 = 1 ∧ g.1.val = Matrix.scalar (Fin 2) c ∧
        ∀ v, g.2.val.val v = c • v := rightProjective_kernel _ _ _ _

theorem odd_complement_cubic {n : ℕ} (hn : 3 ≤ n) :
    ∃ b : OmegaOdd (n - 2) F, orderOf b = 3 := odd_exists_cubic (by omega)

theorem plus_complement_cubic {n : ℕ} (hn : 4 ≤ n) :
    ∃ b : OmegaPlus (n - 2) F, orderOf b = 3 := plus_exists_cubic (by omega)

end SplitOddCentralizers

namespace SplitOddCentralizers
open Matrix SplitOddBlocks
variable {F : Type*} [Field F]

/-- The actual odd right-product image lies in the centralizer of the marked K. -/
theorem oddCover_range_le_centralizer (n : ℕ) (hn : 2 ≤ n) :
    ((projectiveElementaryMap (formB n F)).comp (oddCover (F := F) n hn)).range ≤
      Subgroup.centralizer (oddFundamental (F := F) n hn : Set (POmegaOdd n F)) :=
  rightProjective_range_le_centralizer _ _ _

/-- The actual split right-product image lies in the centralizer of the marked K. -/
theorem plusCover_range_le_centralizer (n : ℕ) (hn : 2 ≤ n) :
    ((projectiveElementaryMap (formD n F)).comp (plusCover (F := F) n hn)).range ≤
      Subgroup.centralizer (plusFundamental (F := F) n hn : Set (POmegaPlus n F)) :=
  rightProjective_range_le_centralizer _ _ _

/-- A nine-subgroup in the literal odd right-product image, in every source rank. -/
theorem oddCover_contains_nine {n : ℕ} (hn : 3 ≤ n) :
    ∃ E : Subgroup (POmegaOdd n F),
      E ≤ ((projectiveElementaryMap (formB n F)).comp (oddCover (F := F) n (by omega))).range ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨b, hb⟩ := odd_complement_cubic (F := F) hn
  exact elementaryProjective_contains_nine (formB n F) (oddCover (F := F) n (by omega))
    (oddCover_injective (F := F) n (by omega)) b hb

/-- A nine-subgroup in the literal split right-product image, in every source rank. -/
theorem plusCover_contains_nine {n : ℕ} (hn : 4 ≤ n) :
    ∃ E : Subgroup (POmegaPlus n F),
      E ≤ ((projectiveElementaryMap (formD n F)).comp (plusCover (F := F) n (by omega))).range ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨b, hb⟩ := plus_complement_cubic (F := F) hn
  exact elementaryProjective_contains_nine (formD n F) (plusCover (F := F) n (by omega))
    (plusCover_injective (F := F) n (by omega)) b hb

section Residual
variable {G A : Type*} [Group G] [Group A]

/-- The literal nested prime-to-p residual, with its relative centralizer type. -/
def centralizerResidual (p : ℕ) (K : Subgroup G) :
    Subgroup (Subgroup.centralizer (K : Set G)) :=
  Subgroup.primeToResidual p (Subgroup.centralizer (K : Set G))

/-- Its image under the actual centralizer inclusion. -/
def residualImage (p : ℕ) (K : Subgroup G) : Subgroup G :=
  (centralizerResidual p K).map (Subgroup.centralizer (K : Set G)).subtype

/-- Inclusion identifies the nested residual with its actual ambient image. -/
def residualEquivImage (p : ℕ) (K : Subgroup G) :
    centralizerResidual p K ≃* residualImage p K :=
  (centralizerResidual p K).equivMapOfInjective _ Subtype.val_injective

/-- The exact covering kernel gives the literal residual once its range is identified.
The range identity is a separate structural premise, not asserted here. -/
def quotientEquivResidual (p : ℕ) (K : Subgroup G) (f : A →* G)
    (hJ : f.range = residualImage p K) : A ⧸ f.ker ≃* centralizerResidual p K :=
  (QuotientGroup.quotientKerEquivRange f).trans
    ((MulEquiv.subgroupCongr hJ).trans (residualEquivImage p K).symm)

/-- The quotient identification preserves the original ambient covering map. -/
@[simp] theorem quotientEquivResidual_apply_mk (p : ℕ) (K : Subgroup G) (f : A →* G)
    (hJ : f.range = residualImage p K) (a : A) :
    (quotientEquivResidual p K f hJ (QuotientGroup.mk' _ a)).val.val = f a := by
  exact congrArg Subtype.val ((residualEquivImage p K).apply_symm_apply
    ((MulEquiv.subgroupCongr hJ) ((QuotientGroup.quotientKerEquivRange f) (QuotientGroup.mk' _ a))))

end Residual

/-- Conditional source central-product identification in the odd branch.
Its kernel is calculated by `oddCover_projective_kernel`. -/
def oddQuotientEquivResidual (n p : ℕ) (hn : 2 ≤ n)
    (hJ : ((projectiveElementaryMap (formB n F)).comp (oddCover (F := F) n hn)).range =
      residualImage p (oddFundamental (F := F) n hn)) :
    (Matrix.SpecialLinearGroup (Fin 2) F × OmegaOdd (n - 2) F) ⧸
      ((projectiveElementaryMap (formB n F)).comp (oddCover (F := F) n hn)).ker ≃*
      centralizerResidual p (oddFundamental (F := F) n hn) :=
  quotientEquivResidual _ _ _ hJ

/-- Conditional source central-product identification in the split branch.
Its kernel is calculated by `plusCover_projective_kernel`. -/
def plusQuotientEquivResidual (n p : ℕ) (hn : 2 ≤ n)
    (hJ : ((projectiveElementaryMap (formD n F)).comp (plusCover (F := F) n hn)).range =
      residualImage p (plusFundamental (F := F) n hn)) :
    (Matrix.SpecialLinearGroup (Fin 2) F × OmegaPlus (n - 2) F) ⧸
      ((projectiveElementaryMap (formD n F)).comp (plusCover (F := F) n hn)).ker ≃*
      centralizerResidual p (plusFundamental (F := F) n hn) :=
  quotientEquivResidual _ _ _ hJ

/-- Residual containment required by the odd source rank adapter. -/
theorem oddCover_range_le_residual (p : ℕ) [CharP F p] (n : ℕ) (hn : 2 ≤ n) :
    ((projectiveElementaryMap (formB n F)).comp (oddCover (F := F) n hn)).range ≤
      residualImage p (oddFundamental (F := F) n hn) := rightProjective_range_le_residual p _ _ _

/-- Residual containment required by the split source rank adapter. -/
theorem plusCover_range_le_residual (p : ℕ) [CharP F p] (n : ℕ) (hn : 2 ≤ n) :
    ((projectiveElementaryMap (formD n F)).comp (plusCover (F := F) n hn)).range ≤
      residualImage p (plusFundamental (F := F) n hn) := rightProjective_range_le_residual p _ _ _

/-- The odd cover has central kernel with precisely the common scalars calculated
by `oddCover_projective_kernel`. -/
theorem oddCover_projective_kernel_le_center (n : ℕ) (hn : 2 ≤ n) :
    ((projectiveElementaryMap (formB n F)).comp (oddCover (F := F) n hn)).ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F × OmegaOdd (n - 2) F) :=
  rightProjective_kernel_le_center _ _ _

/-- The split cover has central kernel with the actual complementary scalar
membership retained by `plusCover_projective_kernel`. -/
theorem plusCover_projective_kernel_le_center (n : ℕ) (hn : 2 ≤ n) :
    ((projectiveElementaryMap (formD n F)).comp (plusCover (F := F) n hn)).ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F × OmegaPlus (n - 2) F) :=
  rightProjective_kernel_le_center _ _ _

section OddCharacteristic
variable [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] (hp : p ≠ 2)

include hp in
/-- Exact residual image in odd natural dimension at least seven, including F₃.
The complementary full-isometry index discharges the reverse inclusion. -/
theorem oddCover_range_eq_residual {n : ℕ} (hn : 3 ≤ n) :
    ((projectiveElementaryMap (formB n F)).comp (oddCover (F := F) n (by omega))).range =
      residualImage p (oddFundamental (F := F) n (by omega)) :=
  rightProjective_range_eq_residual_of_index p hp _ _ _
    (IsometryQuotients.elementary_index_coprime_formB p hp (n - 2) (by omega))

include hp in
/-- Exact residual image in split natural dimension at least eight, including F₃.
The rank-two complementary isometry quotient is included. -/
theorem plusCover_range_eq_residual {n : ℕ} (hn : 4 ≤ n) :
    ((projectiveElementaryMap (formD n F)).comp (plusCover (F := F) n (by omega))).range =
      residualImage p (plusFundamental (F := F) n (by omega)) :=
  rightProjective_range_eq_residual_of_index p hp _ _ _
    (IsometryQuotients.elementary_index_coprime_formD p hp (n - 2) (by omega))

/-- The source odd central product is the literal nested residual. Its common
square-one scalar kernel is exactly `oddCover_projective_kernel`; no residual
equality or perfectness premise remains. -/
def oddCentralProductEquivResidual {n : ℕ} (hn : 3 ≤ n) :
    (Matrix.SpecialLinearGroup (Fin 2) F × OmegaOdd (n - 2) F) ⧸
      ((projectiveElementaryMap (formB n F)).comp (oddCover (F := F) n (by omega))).ker ≃*
      centralizerResidual p (oddFundamental (F := F) n (by omega)) :=
  oddQuotientEquivResidual n p (by omega) (oddCover_range_eq_residual p hp hn)

/-- The source split central product is the literal nested residual, with the
actual common-scalar membership test `plusCover_projective_kernel`. -/
def plusCentralProductEquivResidual {n : ℕ} (hn : 4 ≤ n) :
    (Matrix.SpecialLinearGroup (Fin 2) F × OmegaPlus (n - 2) F) ⧸
      ((projectiveElementaryMap (formD n F)).comp (plusCover (F := F) n (by omega))).ker ≃*
      centralizerResidual p (plusFundamental (F := F) n (by omega)) :=
  plusQuotientEquivResidual n p (by omega) (plusCover_range_eq_residual p hp hn)

/-- The odd central-product equivalence uses the original block and scalar maps. -/
@[simp] theorem oddCentralProductEquivResidual_apply_mk {n : ℕ} (hn : 3 ≤ n)
    (g : Matrix.SpecialLinearGroup (Fin 2) F × OmegaOdd (n - 2) F) :
    (oddCentralProductEquivResidual (F := F) p hp hn (QuotientGroup.mk' _ g)).val.val =
      projectiveElementaryMap (formB n F) (oddCover (F := F) n (by omega) g) := by
  exact quotientEquivResidual_apply_mk p _ _ _ g

/-- The split central-product equivalence uses the original block and scalar maps. -/
@[simp] theorem plusCentralProductEquivResidual_apply_mk {n : ℕ} (hn : 4 ≤ n)
    (g : Matrix.SpecialLinearGroup (Fin 2) F × OmegaPlus (n - 2) F) :
    (plusCentralProductEquivResidual (F := F) p hp hn (QuotientGroup.mk' _ g)).val.val =
      projectiveElementaryMap (formD n F) (plusCover (F := F) n (by omega) g) := by
  exact quotientEquivResidual_apply_mk p _ _ _ g

end OddCharacteristic


private theorem nine_in_residual {G A B : Type*} [Group G] [Group A] [Group B]
    (p : ℕ) (K : Subgroup G) (f : A × B →* G)
    (hker : ∀ g, f g = 1 → g ^ 2 = 1)
    (hJ : f.range ≤ residualImage p K)
    (a : A) (b : B) (ha : orderOf a = 3) (hb : orderOf b = 3) :
    ∃ E : Subgroup (centralizerResidual p K), IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  let fJ : A × B →* residualImage p K := f.codRestrict _ (fun g => hJ ⟨g, rfl⟩)
  obtain ⟨E, _, hE, hc⟩ := CubicProductQuotient.exists_nine fJ
    (fun g hg => hker g (congrArg Subtype.val hg)) a b ha hb
  let := hE
  let e := residualEquivImage p K
  refine ⟨E.map e.symm.toMonoidHom, IsElementaryAbelian.map _, ?_⟩
  rw [Subgroup.card_map_of_injective e.symm.injective]
  exact hc

/-- The odd source residual contains an actual elementary abelian group of order nine.
All block-map, scalar-kernel, residual-containment and cubic premises are discharged. -/
theorem odd_residual_contains_nine (p : ℕ) [CharP F p] {n : ℕ} (hn : 3 ≤ n) :
    ∃ E : Subgroup (centralizerResidual p (oddFundamental (F := F) n (by omega))),
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨b, hb⟩ := odd_complement_cubic (F := F) hn
  exact nine_in_residual p _ ((projectiveElementaryMap (formB n F)).comp (oddCover (F := F) n (by omega)))
    (elementaryProjective_kernel_square _ _ (oddCover_injective (F := F) n (by omega)))
    (oddCover_range_le_residual p _ _) cubicSL b cubicSL_order hb

/-- The split source residual contains an actual elementary abelian group of order nine.
This includes every finite odd field and the rank-four endpoint. -/
theorem plus_residual_contains_nine (p : ℕ) [CharP F p] {n : ℕ} (hn : 4 ≤ n) :
    ∃ E : Subgroup (centralizerResidual p (plusFundamental (F := F) n (by omega))),
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨b, hb⟩ := plus_complement_cubic (F := F) hn
  exact nine_in_residual p _ ((projectiveElementaryMap (formD n F)).comp (plusCover (F := F) n (by omega)))
    (elementaryProjective_kernel_square _ _ (plusCover_injective (F := F) n (by omega)))
    (plusCover_range_le_residual p _ _) cubicSL b cubicSL_order hb

end SplitOddCentralizers

end ClassicalOrthogonal.Fundamental
