module

public import Theory.SpecificGroups.G2.DefiningRank
public import Theory.SpecificGroups.SL2.PrimeToResidual
public import Theory.AtlasPort.LinearGroups.G2.WeylMaps

/-!
# Fundamental SL₂ and its residual centralizer in odd G₂

The second factor of the split-quaternion action is the fundamental subgroup:
its lower transvections are Wilson's long-root group E, and its upper
transvections are the opposite root group obtained by the Weyl map R.
These two root groups generate the faithful, proper SL₂ subgroup K.

An automorphism centralizing K preserves the two quaternion summands because
it commutes with the central scalar. On the second summand, commuting with
the transvections forces right multiplication by a matrix C. Preservation of
octonion multiplication forces det C = 1 and determines the first summand's
action. Hence C_G(K) is exactly the first quaternion SL₂ factor. Its
prime-to-p residual is the whole centralizer, by generation by p-elements;
this includes SL₂(3), with no perfectness assumption. The common scalar
intersection and the inclusion of the residual are retained explicitly.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, A.2.17, printed p.39,
and its fundamental-subgroup reference: Aschbacher, *On finite groups of
Lie type and odd characteristic*, J. Algebra 66 (1980), pp.401–402,
Theorem 1. This is a direct calculation in the actual ATLAS octonion model;
the imported coordinates retain LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups
namespace Atlas.G2.OddFundamentalCentralizer
open Atlas.SplitOctonion
open MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne
variable {F : Type*} [Field F]

/-- The long-root SL₂ acting by left multiplication on the second quaternion coordinate. -/
def fundamentalHom : SL(2,F) →* Model F := productHom.comp (MonoidHom.inr _ _)
/-- The first quaternion factor, commuting with the fundamental SL₂. -/
abbrev complementHom : SL(2,F) →* Model F := orthogonalLeftHom
/-- The actual marked subgroup of octonion automorphisms. -/
def fundamental : Subgroup (Model F) := fundamentalHom.range

/-- The diagonal scalar kernel meets the second factor trivially. -/
theorem fundamentalHom_injective : Function.Injective (fundamentalHom (F := F)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro A hA
  exact (kernel_scalar 1 A hA).1

/-- The two quaternion factors centralize one another elementwise. -/
theorem factors_commute (A B : SL(2,F)) :
    Commute (complementHom A) (fundamentalHom B) := by
  change productHom (A,1) * productHom (1,B) = productHom (1,B) * productHom (A,1)
  rw [← map_mul, ← map_mul]
  simp

private def pairAction (g : Model F) : (Mat F × Mat F) ≃ₗ[F] (Mat F × Mat F) :=
  coordinates.symm.trans (g.val.trans coordinates)

private theorem pairAction_preserves (g : Model F) (x y : Mat F × Mat F) :
    pairAction g (pairMul x y) = pairMul (pairAction g x) (pairAction g y) := by
  have hc (z w : Mat F × Mat F) :
      coordinates.symm (pairMul z w) = mul (coordinates.symm z) (coordinates.symm w) := by
    apply coordinates.injective
    simp [coordinates_mul]
  simp only [pairAction, LinearEquiv.trans_apply, hc, automorphism_mul, coordinates_mul]

private theorem pairAction_one (g : Model F) : pairAction g (1,0) = (1,0) := by
  have hc : coordinates.symm (1,0) = (unit : Carrier F) := by
    ext i
    fin_cases i <;> simp [coordinates, unit]
  change coordinates (g.val (coordinates.symm (1,0))) = (1,0)
  rw [hc, automorphism_unit]
  apply coordinates.symm.injective
  rw [LinearEquiv.symm_apply_apply, hc]

private theorem pairAction_commutes {g : Model F}
    (hg : g ∈ Subgroup.centralizer (fundamental (F := F) : Set (Model F)))
    (B : SL(2,F)) (a b : Mat F) :
    pairAction g (a, B.val*b) =
      ((pairAction g (a,b)).1, B.val*(pairAction g (a,b)).2) := by
  have h := Subgroup.mem_centralizer_iff.mp hg (fundamentalHom B) ⟨B,rfl⟩
  have he := congrArg (fun k : Model F => coordinates (k.val (coordinates.symm (a,b)))) h
  change coordinates (octonionEquiv 1 B (g.val (coordinates.symm (a,b)))) =
    coordinates (g.val (octonionEquiv 1 B (coordinates.symm (a,b)))) at he
  simpa [octonionEquiv, pairEquiv, pairLinear, bar_one, pairAction] using he.symm

private theorem matrix_eq_zero_of_eq_neg (h2 : (2 : F) ≠ 0) (a : Mat F)
    (ha : a = -a) : a = 0 := by
  ext i j
  have h := congrArg (fun M : Mat F => M i j) ha
  have hz : (2 : F) * a i j = 0 := by
    change a i j = -a i j at h
    linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left h2

private theorem pairAction_split (h2 : (2 : F) ≠ 0) {g : Model F}
    (hg : g ∈ Subgroup.centralizer (fundamental (F := F) : Set (Model F)))
    (a b : Mat F) :
    pairAction g (a,b) = ((pairAction g (a,0)).1, (pairAction g (0,b)).2) := by
  have hb : (pairAction g (a,0)).2 = 0 := by
    apply matrix_eq_zero_of_eq_neg h2
    have h := congrArg Prod.snd (pairAction_commutes hg (-1) a 0)
    simpa using h
  have ha : (pairAction g (0,b)).1 = 0 := by
    apply matrix_eq_zero_of_eq_neg h2
    have h := congrArg Prod.fst (pairAction_commutes hg (-1) 0 b)
    have hn : ((0 : Mat F),-b) = -(0,b) := by simp
    simpa only [SpecialLinearGroup.coe_neg, SpecialLinearGroup.coe_one,
      neg_mul, one_mul, hn, map_neg, Prod.fst_neg] using h.symm
  have hab : (a,b) = (a,0) + (0,b) := by simp
  rw [hab, map_add]
  exact Prod.ext (by simp [ha]) (by simp [hb])

private def rightAction (g : Model F) : Mat F →ₗ[F] Mat F :=
  (LinearMap.snd F (Mat F) (Mat F)).comp
    ((pairAction g).toLinearMap.comp (LinearMap.inr F (Mat F) (Mat F)))

private theorem rightAction_commutes {g : Model F}
    (hg : g ∈ Subgroup.centralizer (fundamental (F := F) : Set (Model F)))
    (B : SL(2,F)) (b : Mat F) :
    rightAction g (B.val*b) = B.val*rightAction g b :=
  congrArg Prod.snd (pairAction_commutes hg B 0 b)

private theorem matrix_commutant (L : Mat F →ₗ[F] Mat F)
    (hL : ∀ (A : SL(2,F)) (b : Mat F), L (A.val*b) = A.val*L b) (b : Mat F) :
    L b = b * L 1 := by
  have hs (i j : Fin 2) (hij : i ≠ j) (b : Mat F) :
      L (Matrix.single i j 1 * b) = Matrix.single i j 1 * L b := by
    have h := hL (SpecialLinearGroup.transvection hij 1) b
    simp only [SpecialLinearGroup.transvection_coe,
      _root_.add_mul, one_mul, map_add] at h
    exact add_left_cancel h
  have he (i j : Fin 2) (b : Mat F) :
      L (Matrix.single i j 1 * b) = Matrix.single i j 1 * L b := by
    by_cases hij : i = j
    · subst j
      obtain ⟨j, hji⟩ := exists_ne i
      have h := hs i j hji.symm (Matrix.single j i 1 * b)
      rw [hs j i hji] at h
      simpa only [← mul_assoc, Matrix.single_mul_single_same, one_mul] using h
    · exact hs i j hij b
  have hb : b = ∑ i : Fin 2, ∑ j : Fin 2, b i j • Matrix.single i j 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.single]
  rw [hb, map_sum, Finset.sum_mul]
  congr 1
  funext i
  rw [map_sum, Finset.sum_mul]
  congr 1
  funext j
  rw [map_smul, smul_mul_assoc]
  congr 1
  simpa only [mul_one] using he i j 1

private theorem centralizer_le_complement (h2 : (2 : F) ≠ 0) :
    Subgroup.centralizer (fundamental (F := F) : Set (Model F)) ≤ complementHom.range := by
  intro g hg
  have hb0 : bar (0 : Mat F) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [bar]
  let C : Mat F := rightAction g 1
  have hright (b : Mat F) : pairAction g (0,b) = (0,b*C) := by
    rw [pairAction_split h2 hg]
    change ((pairAction g (0,0)).1, rightAction g b) = _
    have hz : pairAction g (0,0) = 0 := (pairAction g).map_zero
    rw [hz, matrix_commutant _ (rightAction_commutes hg)]
    rfl
  have hnorm : bar C * C = 1 := by
    have h := pairAction_preserves g (0,1) (0,1)
    have hm : pairMul ((0 : Mat F),1) (0,1) = -(1,0) := by
      simp [pairMul, bar_one, hb0]
    rw [hm, map_neg, pairAction_one, hright, one_mul] at h
    simpa [pairMul] using (congrArg Prod.fst h).symm
  have hdet : C.det = 1 := by
    have h := congrArg (fun M : Mat F => M 0 0) hnorm
    simpa [Matrix.det_fin_two, bar, Matrix.mul_apply, Fin.sum_univ_two,
      sub_eq_add_neg, mul_comm] using h
  let A : SL(2,F) := ⟨bar C, by
    simpa [Matrix.det_fin_two, bar, mul_comm] using hdet⟩
  have hleft (a : Mat F) : (pairAction g (a,0)).1 = bar C * a * C := by
    have h := pairAction_preserves g (a,0) (0,1)
    have hm : pairMul (a,0) (0,1) = (0,a) := by simp [pairMul]
    rw [hm, hright, hright, one_mul] at h
    have hs := congrArg Prod.snd h
    simp only [pairMul, hb0, mul_zero, add_zero] at hs
    have hh := congrArg (fun M : Mat F => bar C * M) hs
    simpa only [← mul_assoc, hnorm, one_mul] using hh.symm
  refine ⟨A, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply coordinates.injective
  change coordinates (octonionEquiv A 1 x) = coordinates (g.val x)
  have ht := pairAction_split h2 hg (coordinates x).1 (coordinates x).2
  rw [hleft] at ht
  change pairAction g (coordinates x) = (_,rightAction g (coordinates x).2) at ht
  rw [matrix_commutant _ (rightAction_commutes hg)] at ht
  simpa [pairAction, octonionEquiv, pairEquiv, pairLinear, A, bar_bar] using ht.symm

/-- The full centralizer of K is the first factor; this is not the centralizer of its involution. -/
theorem centralizer_eq_complement (h2 : (2 : F) ≠ 0) :
    Subgroup.centralizer (fundamental (F := F) : Set (Model F)) = complementHom.range := by
  apply le_antisymm (centralizer_le_complement h2)
  rintro _ ⟨A,rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  rintro _ ⟨B,rfl⟩
  exact (factors_commute A B).eq.symm

/-- The lower transvections are precisely the existing long-root group E. -/
theorem fundamental_lower (c : F) :
    fundamentalHom (SpecialLinearGroup.transvection one_ne_zero c) = rootE c := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change octonionEquiv 1 (SpecialLinearGroup.transvection one_ne_zero c) x =
    Explicit.rootEEquiv c x
  ext i
  fin_cases i <;>
    simp [octonionEquiv, coordinates, pairEquiv, pairLinear, bar_one,
      SpecialLinearGroup.transvection_coe, Matrix.single, Matrix.mul_apply,
      Fin.sum_univ_two, Explicit.rootEEquiv, Explicit.rootELinear, Explicit.rootEApply] <;> ring

/-- The upper transvections are the opposite long-root group, with the literal Weyl conjugation. -/
theorem fundamental_upper (c : F) :
    fundamentalHom (SpecialLinearGroup.transvection zero_ne_one c) =
      weylR * rootE c * weylR⁻¹ := by
  have hr : (weylR : Model F)⁻¹ = weylR := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using (weylR_sq (K := F))
  rw [hr]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change octonionEquiv 1 (SpecialLinearGroup.transvection zero_ne_one c) x =
    weylREquiv (Explicit.rootEEquiv c (weylREquiv x))
  ext i
  fin_cases i <;>
    simp [octonionEquiv, coordinates, pairEquiv, pairLinear, bar_one,
      SpecialLinearGroup.transvection_coe, Matrix.single, Matrix.mul_apply,
      Fin.sum_univ_two, Explicit.rootEEquiv, Explicit.rootELinear, Explicit.rootEApply,
      weylREquiv, weylRLinear, weylRApply]
  all_goals ring

/-- The fundamental marking: K is generated by the displayed opposite long-root groups. -/
theorem fundamental_eq_root_generated : fundamental (F := F) =
    Subgroup.closure (Set.range rootE ∪
      Set.range (fun c : F => weylR * rootE c * weylR⁻¹)) := by
  apply le_antisymm
  · rintro _ ⟨A,rfl⟩
    apply Matrix.SL2.transvection_induction
      (fun A => fundamentalHom A ∈ Subgroup.closure _) ?_ ?_ A
    · intro i j hij c
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · rw [fundamental_upper]
        exact Subgroup.subset_closure (Or.inr ⟨c,rfl⟩)
      · rw [fundamental_lower]
        exact Subgroup.subset_closure (Or.inl ⟨c,rfl⟩)
      · exact (hij rfl).elim
    · intro A B hA hB
      rw [map_mul]
      exact Subgroup.mul_mem _ hA hB
  · rw [Subgroup.closure_le]
    rintro _ (⟨c,rfl⟩ | ⟨c,rfl⟩)
    · rw [← fundamental_lower]
      exact ⟨_,rfl⟩
    · change weylR * rootE c * weylR⁻¹ ∈ fundamental
      rw [← fundamental_upper]
      exact ⟨_,rfl⟩

/-- A highest-root element moves a coordinate fixed by the entire fundamental subgroup. -/
theorem fundamental_proper : fundamental (F := F) ≠ ⊤ := by
  intro h
  have hm : rootA (1 : F) ∈ fundamental := h ▸ Subgroup.mem_top _
  obtain ⟨A, hA⟩ := hm
  have he := congrArg (fun g : Model F => g.val (basisVector 6) 0) hA
  change octonionEquiv 1 A (basisVector 6) 0 = Explicit.rootAEquiv 1 (basisVector 6) 0 at he
  simp [octonionEquiv, coordinates, pairEquiv, pairLinear, bar_one,
    Explicit.rootAEquiv, Explicit.rootALinear, Explicit.rootAApply, basisVector] at he

/-- The first factor with its actual inclusion in the centralizer of K. -/
def complementToCentralizer : SL(2,F) →*
    Subgroup.centralizer (fundamental (F := F) : Set (Model F)) :=
  complementHom.codRestrict _ fun A => by
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨B,rfl⟩
    exact (factors_commute A B).eq.symm

/-- Transvection generation includes the first factor in the literal prime-to-p residual. -/
def residualHom (p : ℕ) [CharP F p] : SL(2,F) →*
    Subgroup.primeToResidual p (Subgroup.centralizer (fundamental (F := F) : Set (Model F))) :=
  complementToCentralizer.codRestrict _ (Matrix.SL2.map_mem_primeToResidual p _)

/-- The residual inclusion preserves faithfulness of the first factor. -/
theorem residualHom_injective (p : ℕ) [CharP F p] :
    Function.Injective (residualHom (F := F) p) := by
  intro A B h
  exact orthogonalLeftHom_injective (congrArg (fun x => x.val.val) h)

/-- Every element of the residual comes from the first quaternion factor. -/
theorem residualHom_surjective (p : ℕ) [CharP F p] (h2 : (2 : F) ≠ 0) :
    Function.Surjective (residualHom (F := F) p) := by
  intro g
  obtain ⟨A,hA⟩ := centralizer_le_complement h2 g.val.property
  exact ⟨A, Subtype.ext (Subtype.ext hA)⟩

/-- The exact residual-centralizer isomorphism, also for the field of three elements. -/
noncomputable def residualEquivSL2 (p : ℕ) [CharP F p] (h2 : (2 : F) ≠ 0) :
    Subgroup.primeToResidual p
      (Subgroup.centralizer (fundamental (F := F) : Set (Model F))) ≃* SL(2,F) :=
  (MulEquiv.ofBijective (residualHom p)
    ⟨residualHom_injective p, residualHom_surjective p h2⟩).symm

/-- The residual map is the original octonion action after both subgroup inclusions. -/
theorem residualHom_coe (p : ℕ) [CharP F p] (A : SL(2,F)) :
    ((residualHom p A).val : Model F) = complementHom A := rfl

/-- Upper transvections witness field-degree rank inside the literal residual centralizer. -/
theorem fieldExponent_le_residualRank [Finite F] {p e : ℕ}
    [Fact p.Prime] [CharP F p] (hcard : Nat.card F = p^e) :
    e ≤ primeRank p (Subgroup.primeToResidual p
      (Subgroup.centralizer (fundamental (F := F) : Set (Model F)))) :=
  SpecialLinearGroup.fieldExponent_le_primeRank_of_injective hcard
    (residualHom p) (residualHom_injective p)

/-- The two central minus identities have the same image. -/
theorem scalar_agreement : complementHom (-1 : SL(2,F)) = fundamentalHom (-1) := by
  have h := productHom_neg_one (F := F)
  have hm : productHom (-1,-1) = complementHom (-1 : SL(2,F)) * fundamentalHom (-1) := by
    change productHom (-1,-1) = productHom (-1,1) * productHom (1,-1)
    rw [← map_mul]
    simp
  rw [hm] at h
  have he := mul_eq_one_iff_eq_inv.mp h
  simpa only [← map_inv, inv_neg, inv_one] using he

/-- Equality between the two factors occurs exactly at the common scalar signs. -/
theorem factors_equal_iff (A B : SL(2,F)) :
    complementHom A = fundamentalHom B ↔
      (A = 1 ∧ B = 1) ∨ (A = -1 ∧ B = -1) := by
  constructor
  · intro h
    have hk : productHom (A,B⁻¹) = (1 : Model F) := by
      have hm : productHom (A,B⁻¹) = complementHom A * fundamentalHom B⁻¹ := by
        change productHom (A,B⁻¹) = productHom (A,1) * productHom (1,B⁻¹)
        rw [← map_mul]
        simp
      rw [hm, h, map_inv, mul_inv_cancel]
    rcases (productHom_eq_one_iff _).mp hk with hh | hh
    · left
      have hA := congrArg Prod.fst hh
      have hB := congrArg Prod.snd hh
      exact ⟨hA, by simpa using hB⟩
    · right
      have hA := congrArg Prod.fst hh
      have hB := congrArg Prod.snd hh
      exact ⟨hA, by simpa only [inv_eq_iff_eq_inv, inv_neg, inv_one] using hB⟩
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · simp
    · exact scalar_agreement

/-- The central intersection consists exactly of the identity and common minus identity. -/
theorem mem_factor_intersection (x : Model F) :
    x ∈ fundamental (F := F) ⊓ complementHom.range ↔
      x = 1 ∨ x = fundamentalHom (-1 : SL(2,F)) := by
  constructor
  · rintro ⟨⟨B,hB⟩,⟨A,hA⟩⟩
    rcases (factors_equal_iff A B).mp (hA.trans hB.symm) with ⟨_,h⟩ | ⟨_,h⟩
    · left
      simpa [h] using hB.symm
    · right
      simpa [h] using hB.symm
  · rintro (rfl | rfl)
    · exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
    · exact ⟨⟨-1,rfl⟩, ⟨-1,scalar_agreement⟩⟩

/-- In odd characteristic the common scalar is a genuine involution. -/
theorem fundamental_involution {p : ℕ} [Fact p.Prime] [CharP F p] (hp : p ≠ 2) :
    fundamentalHom (-1 : SL(2,F)) ≠ 1 ∧ fundamentalHom (-1 : SL(2,F)) ^ 2 = 1 :=
  SpecialLinearGroup.map_neg_one_isInvolution hp fundamentalHom fundamentalHom_injective

/-- The residual, mapped along the actual centralizer inclusion, is the first factor. -/
theorem residual_map_eq_complement (p : ℕ) [CharP F p] (h2 : (2 : F) ≠ 0) :
    (Subgroup.primeToResidual p
      (Subgroup.centralizer (fundamental (F := F) : Set (Model F)))).map
        (Subgroup.centralizer (fundamental (F := F) : Set (Model F))).subtype =
      complementHom.range := by
  apply le_antisymm
  · rintro _ ⟨x,_,rfl⟩
    exact centralizer_le_complement h2 x.property
  · rintro _ ⟨A,rfl⟩
    exact ⟨complementToCentralizer A, Matrix.SL2.map_mem_primeToResidual p _ A, rfl⟩

/-- The full centralizer is generated by defining-characteristic elements. -/
theorem residual_eq_top (p : ℕ) [CharP F p] (h2 : (2 : F) ≠ 0) :
    Subgroup.primeToResidual p
      (Subgroup.centralizer (fundamental (F := F) : Set (Model F))) = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨A,hA⟩ := centralizer_le_complement h2 g.property
  have he : complementToCentralizer A = g := Subtype.ext hA
  rw [← he]
  exact Matrix.SL2.map_mem_primeToResidual p _ A

/-- The marked fundamental subgroup with its faithful SL₂ parametrization. -/
noncomputable def fundamentalEquivSL2 : fundamental (F := F) ≃* SL(2,F) :=
  (MonoidHom.ofInjective fundamentalHom_injective).symm

/-- The fundamental subgroup has exactly the two central scalar signs. -/
theorem mem_fundamental_center (h2 : (2 : F) ≠ 0) (x : fundamental (F := F)) :
    x ∈ Subgroup.center (fundamental (F := F)) ↔
      x.val = 1 ∨ x.val = fundamentalHom (-1 : SL(2,F)) := by
  have hc : x ∈ Subgroup.center (fundamental (F := F)) ↔
      x.val ∈ Subgroup.centralizer (fundamental (F := F) : Set (Model F)) := by
    constructor
    · intro hx
      apply Subgroup.mem_centralizer_iff.mpr
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨y,hy⟩)
    · intro hx
      apply Subgroup.mem_center_iff.mpr
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hx y.val y.property
  rw [hc, centralizer_eq_complement h2]
  constructor
  · intro hx
    exact (mem_factor_intersection x.val).mp ⟨x.property,hx⟩
  · intro hx
    exact ((mem_factor_intersection x.val).mpr hx).2

end Atlas.G2.OddFundamentalCentralizer
