module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.Geometry
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.Affine
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.TensorSection.Irreducibility
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators.Planes
public import Theory.Representation.MathieuCodeRestriction.Construction
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineCoordinates

/-!
# First moments on the native trio cocode

The first moment of a binary word on each of the three affine octads gives a
linear map to the tensor model. Literal Golay rows have equal moments on all
three octads, so the sum-zero three-coordinate core kills the Golay code. On
the standard pair space, two-point words calibrate the map on pure tensors;
this proves surjectivity of the descended map and identifies its three-space
kernel with the explicit affine-plane range. Even parity in each octad kills
the affine translation terms, so the map intertwines the native cocode action
with the tensor action pulled back through `standardAffineHom`.

Source: Aschbacher–Smith H.15.6(3), printed p.401, with H.14.1(3), printed
p.396. The printed `V₉/V` means `V₉/V₃`. The native row and affine coordinate
tables give a direct cocode proof of the tensor identification.
-/

@[expose] public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode
open scoped BigOperators TensorProduct
namespace MathieuCode.TrioCalculation
noncomputable section

abbrev F := ZMod 2
abbrev A := QuotientConstruction.Vector
abbrev N := BinaryPermutation.core (Fin 3)
abbrev NT := NaturalTensor
def beta (i : Fin 3) : N :=
  ⟨BinaryPermutation.allOne (Fin 3) + Pi.single i 1, by
    rw [BinaryPermutation.mem_core]
    classical
    simp [Fin.sum_univ_three]
    fin_cases i <;> decide +kernel⟩
lemma beta_apply (i j : Fin 3) : (beta i).val j = if i = j then 0 else 1 := by
  revert i j
  decide +kernel
lemma beta_sum : ∑ i : Fin 3, beta i = 0 := by
  apply Subtype.ext
  funext j
  rw [Fin.sum_univ_three]
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  fin_cases j <;> simp [beta_apply, h11]
noncomputable def moment : Full →ₗ[F] (Fin 3 → A) where
  toFun w i := ∑ x : A, w (point (i,x)) • x
  map_add' w z := by
    funext i
    change (∑ x : A, (w (point (i,x)) + z (point (i,x))) • x) =
      (∑ x : A, w (point (i,x)) • x) + ∑ x : A, z (point (i,x)) • x
    simp_rw [add_smul]
    rw [Finset.sum_add_distrib]
  map_smul' c w := by
    funext i
    change (∑ x : A, (c • w (point (i,x))) • x) = c • (∑ x : A, w (point (i,x)) • x)
    calc
      (∑ x : A, (c • w (point (i,x))) • x) =
          ∑ x : A, c • (w (point (i,x)) • x) := by
            apply Finset.sum_congr rfl
            intro x hx
            simp only [smul_eq_mul, mul_smul]
      _ = c • (∑ x : A, w (point (i,x)) • x) := by
            rw [Finset.smul_sum]


noncomputable def tensorAssembly : (Fin 3 → A) →ₗ[F] NT where
  toFun m := ∑ i : Fin 3, m i ⊗ₜ[F] beta i
  map_add' x y := by
    change (∑ i : Fin 3, (x i + y i) ⊗ₜ[F] beta i) = _
    simp_rw [TensorProduct.add_tmul]
    rw [Finset.sum_add_distrib]
  map_smul' c x := by
    change (∑ i : Fin 3, (c • x i) ⊗ₜ[F] beta i) = c • (∑ i : Fin 3, x i ⊗ₜ[F] beta i)
    calc
      (∑ i : Fin 3, (c • x i) ⊗ₜ[F] beta i) =
          ∑ i : Fin 3, c • (x i ⊗ₜ[F] beta i) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [TensorProduct.smul_tmul']
      _ = c • (∑ i : Fin 3, x i ⊗ₜ[F] beta i) := by
            rw [Finset.smul_sum]


noncomputable def momentTensor : Full →ₗ[F] NT := tensorAssembly.comp moment
@[simp] lemma momentTensor_apply (w : Full) : momentTensor w = ∑ i : Fin 3, (moment w i) ⊗ₜ[F] beta i := by
  rfl
lemma row_moment_const (r : Fin 12) :
    ∀ i : Fin 3, moment (row r) i = moment (row r) 0 := by
  fin_cases r <;> intro i <;> fin_cases i <;> decide +kernel
lemma momentTensor_row (r : Fin 12) : momentTensor (row r) = 0 := by
  rw [momentTensor_apply]
  let d := moment (row r) 0
  have hc : ∀ i : Fin 3, moment (row r) i = d := by
    intro i
    exact row_moment_const r i
  simp_rw [hc]
  rw [← TensorProduct.tmul_sum, beta_sum]
  simp
lemma golay_le_momentTensor_ker : golay ≤ momentTensor.ker := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨r, rfl⟩ := hv
      exact momentTensor_row r
  | zero => exact map_zero momentTensor
  | add x y hx hy hx' hy' =>
      change momentTensor (x + y) = 0
      rw [map_add, hx', hy', add_zero]
  | smul c x hx hx' =>
      change momentTensor (c • x) = 0
      rw [map_smul, hx', smul_zero]

lemma codeInCore_le_momentTensor_ker :
    codeInCore ≤ (momentTensor.comp Core.subtype).ker := by
  intro v hv
  change momentTensor v.val = 0
  exact golay_le_momentTensor_ker hv
noncomputable def cocodeMoment : Cocode →ₗ[F] NT :=
  codeInCore.liftQ (momentTensor.comp Core.subtype) codeInCore_le_momentTensor_ker
@[simp] lemma cocodeMoment_mk (v : Core) : cocodeMoment (codeInCore.mkQ v) = momentTensor v.val := by
  rfl
def pairWord (i : Fin 3) (a : A) : Core :=
  ⟨Pi.single (point (i,0)) 1 + Pi.single (point (i,a)) 1, by
    rw [BinaryPermutation.mem_core]
    revert i a
    decide +kernel⟩
lemma pairWord_moment (i k : Fin 3) (a : A) :
    moment (pairWord i a).val k = if k = i then a else 0 := by
  revert i k a
  decide +kernel

lemma pairWord_momentTensor (i : Fin 3) (a : A) :
    momentTensor (pairWord i a).val = a ⊗ₜ[F] beta i := by
  rw [momentTensor_apply]
  have hm : ∀ k : Fin 3, moment (pairWord i a).val k = if k = i then a else 0 := by
    intro k
    exact pairWord_moment i k a
  simp_rw [hm]
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [hbi]
  · simp

lemma pairWord_mem_pairCore (i : Fin 3) (a : A) :
    (pairWord i a) ∈ pairCore standardTrio := by
  rw [mem_pairCore_iff]
  intro B hB
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hB
  have hsum (p : Fin 24) :
      (∑ x ∈ standardTrioOctad j, Pi.single p 1 x) =
        if p ∈ standardTrioOctad j then 1 else 0 := by
    classical
    by_cases hp : p ∈ standardTrioOctad j
    · simp only [if_pos hp]
      rw [Finset.sum_eq_single p]
      · simp [Pi.single_eq_same]
      · intro b hb hbp
        simp [hbp]
      · intro hnp
        exact (hnp hp).elim
    · simp only [if_neg hp]
      apply Finset.sum_eq_zero
      intro b hb
      rw [Pi.single_apply]
      rw [if_neg]
      intro hbp
      exact hp (hbp ▸ hb)
  rw [show (pairWord i a).val = Pi.single (point (i,0)) 1 + Pi.single (point (i,a)) 1 by rfl]
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib]
  have h0 := point_mem_octad_iff i j 0
  have ha := point_mem_octad_iff i j a
  have hh := congrArg₂ (· + ·) (hsum (point (i,0))) (hsum (point (i,a)))
  simp [h0, ha] at hh ⊢

lemma beta_decomposition (n : N) : ∑ i : Fin 3, n.val i • beta i = n := by
  apply Subtype.ext
  funext j
  rw [Fin.sum_univ_three]
  have hn := n.property
  rw [BinaryPermutation.mem_core, Fin.sum_univ_three] at hn
  fin_cases j
  · change n.val 0 • (beta 0).val 0 + n.val 1 • (beta 1).val 0 + n.val 2 • (beta 2).val 0 = n.val 0
    rw [beta_apply, beta_apply, beta_apply]
    simp [Fin.reduceEq, smul_eq_mul]
    have h2 : (2 : ZMod 2) = 0 := by decide
    calc
      _ = (n.val 0 + n.val 1 + n.val 2) + n.val 0 := by ring_nf; simp [h2]
      _ = n.val 0 := by rw [hn]; simp
  · change n.val 0 • (beta 0).val 1 + n.val 1 • (beta 1).val 1 + n.val 2 • (beta 2).val 1 = n.val 1
    rw [beta_apply, beta_apply, beta_apply]
    simp [Fin.reduceEq, smul_eq_mul]
    have h2 : (2 : ZMod 2) = 0 := by decide
    calc
      _ = (n.val 0 + n.val 1 + n.val 2) + n.val 1 := by ring_nf; simp [h2]
      _ = n.val 1 := by rw [hn]; simp
  · change n.val 0 • (beta 0).val 2 + n.val 1 • (beta 1).val 2 + n.val 2 • (beta 2).val 2 = n.val 2
    rw [beta_apply, beta_apply, beta_apply]
    simp [Fin.reduceEq, smul_eq_mul]
    have h2 : (2 : ZMod 2) = 0 := by decide
    calc
      _ = (n.val 0 + n.val 1 + n.val 2) + n.val 2 := by ring_nf; simp [h2]
      _ = n.val 2 := by rw [hn]; simp

abbrev standardPairSpace : Submodule F Cocode := ⨆ B ∈ standardTrio.parts, supportedPairSpace B
noncomputable def pairMoment : standardPairSpace →ₗ[F] NT :=
  cocodeMoment.comp standardPairSpace.subtype
lemma pairClass_mem (i : Fin 3) (a : A) :
    codeInCore.mkQ (pairWord i a) ∈ standardPairSpace := by
  have heq : standardPairSpace = (pairCore standardTrio).map codeInCore.mkQ :=
    (pairCore_quotient_image standardTrio).symm
  rw [heq]
  exact ⟨pairWord i a, pairWord_mem_pairCore i a, rfl⟩
lemma pairMoment_class (i : Fin 3) (a : A) :
    pairMoment ⟨codeInCore.mkQ (pairWord i a), pairClass_mem i a⟩ = a ⊗ₜ[F] beta i := by
  change cocodeMoment (codeInCore.mkQ (pairWord i a)) = _
  rw [cocodeMoment_mk, pairWord_momentTensor]
lemma pairMoment_surjective : Function.Surjective pairMoment := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a n =>
      rw [← beta_decomposition n]
      simp_rw [TensorProduct.tmul_sum]
      exact ⟨∑ i : Fin 3, n.val i • ⟨codeInCore.mkQ (pairWord i a), pairClass_mem i a⟩, by
        simp only [map_sum, map_smul, pairMoment_class, TensorProduct.tmul_smul, TensorProduct.smul_tmul']⟩
  | add x y hx hy =>
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      exact ⟨u + v, by simp⟩
lemma standardPlane_moment_zero (a : A) :
    moment (standardPlaneWord a) = 0 := by
  revert a
  decide +kernel
lemma standardPlane_cocodeMoment_zero (a : A) :
    cocodeMoment (standardPlaneMap a) = 0 := by
  change cocodeMoment (codeInCore.mkQ (standardPlaneCore a)) = 0
  rw [cocodeMoment_mk]
  change momentTensor (standardPlaneWord a) = 0
  rw [momentTensor_apply, standardPlane_moment_zero]
  simp
noncomputable def standardPlanePairMap : A →ₗ[F] standardPairSpace :=
  standardPlaneMap.codRestrict standardPairSpace (fun a => standardPlaneMap_range_le_pairSpace ⟨a, rfl⟩)
lemma standardPlanePairMap_moment_zero (a : A) :
    pairMoment (standardPlanePairMap a) = 0 := by
  change cocodeMoment (standardPlaneMap a) = 0
  exact standardPlane_cocodeMoment_zero a
lemma standardPlanePairMap_range_le_pairMoment_ker :
    standardPlanePairMap.range ≤ pairMoment.ker := by
  rintro _ ⟨a, rfl⟩
  exact standardPlanePairMap_moment_zero a

lemma standardPlanePairMap_injective : Function.Injective standardPlanePairMap := by
  intro a b hab
  apply standardPlaneMap_injective
  exact congrArg Subtype.val hab
lemma finrank_standardPlanePairMap_range :
    Module.finrank F standardPlanePairMap.range = 3 := by
  rw [LinearMap.finrank_range_of_inj standardPlanePairMap_injective]
  simp
lemma finrank_pairMoment_ker :
    Module.finrank F pairMoment.ker = 3 := by
  have hr : pairMoment.range = ⊤ := LinearMap.range_eq_top.mpr pairMoment_surjective
  have hd := pairMoment.finrank_range_add_finrank_ker
  rw [hr, finrank_pairSpace, finrank_top, Module.finrank_tensorProduct,
    Module.finrank_fin_fun, BinaryPermutation.finrank_core] at hd
  norm_num at hd
  omega
lemma pairMoment_ker_eq_standardPlanePairMap_range :
    pairMoment.ker = standardPlanePairMap.range := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq standardPlanePairMap_range_le_pairMoment_ker
  rw [finrank_standardPlanePairMap_range, finrank_pairMoment_ker]
noncomputable def pairMomentQuotient :
    (standardPairSpace ⧸ standardPlanePairMap.range) →ₗ[F] NT :=
  standardPlanePairMap.range.liftQ pairMoment (by
    rw [pairMoment_ker_eq_standardPlanePairMap_range])
lemma pairMomentQuotient_surjective : Function.Surjective pairMomentQuotient := by
  intro z
  obtain ⟨v, hv⟩ := pairMoment_surjective z
  exact ⟨standardPlanePairMap.range.mkQ v, hv⟩
lemma pairMomentQuotient_injective : Function.Injective pairMomentQuotient := by
  apply LinearMap.ker_eq_bot.mp
  unfold pairMomentQuotient
  rw [Submodule.ker_liftQ]
  rw [pairMoment_ker_eq_standardPlanePairMap_range]
  simp
noncomputable def pairMomentQuotientEquiv :
    (standardPairSpace ⧸ standardPlanePairMap.range) ≃ₗ[F] NT :=
  LinearEquiv.ofBijective pairMomentQuotient
    ⟨pairMomentQuotient_injective, pairMomentQuotient_surjective⟩

lemma beta_equivariant (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    BinaryPermutation.coreRepresentation (Fin 3) σ (beta i) = beta (σ i) := by
  apply Subtype.ext
  funext j
  simp only [BinaryPermutation.coreRepresentation_apply, BinaryPermutation.representation_apply,
    beta_apply, Equiv.eq_symm_apply]

lemma moment_affine (g : trioStabilizer standardTrio) (q : QuotientModel)
    (t : Fin 3 → A) (hg : HasAffineForm g q t) (w : Full) (i : Fin 3) :
    moment (BinaryPermutation.representation (Fin 24) g.val.val w) (q.1 i) =
      Matrix.SpecialLinearGroup.toLin' q.2 (moment w i) +
        (∑ x : A, w (point (i,x))) • t i := by
  let L := Matrix.SpecialLinearGroup.toLin' q.2
  let e : A ≃ A := L.toEquiv.trans (Equiv.addRight (t i))
  change (∑ y : A, (BinaryPermutation.representation (Fin 24) g.val.val w)
    (point (q.1 i,y)) • y) = _
  calc
    _ = ∑ x : A, w (point (i,x)) • (L x + t i) := by
      symm
      apply Fintype.sum_equiv e
      intro x
      have he : e x = L x + t i := rfl
      rw [he, ← hg i x, BinaryPermutation.representation_apply]
      simp
    _ = L (∑ x : A, w (point (i,x)) • x) +
        (∑ x : A, w (point (i,x))) • t i := by
      simp only [smul_add, Finset.sum_add_distrib, map_sum, map_smul,
        Finset.sum_smul]
    _ = _ := rfl

lemma pairCore_parity (w : Core) (hw : w ∈ pairCore standardTrio) (i : Fin 3) :
    ∑ x : A, w.val (point (i,x)) = 0 := by
  have h := (mem_pairCore_iff standardTrio w).mp hw (standardTrioOctad i)
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  rw [← point_image i, Finset.sum_image] at h
  · exact h
  · intro a _ b _ hab
    exact (Prod.mk.inj (point.injective hab)).2

lemma momentTensor_equivariant (g : trioStabilizer standardTrio)
    (w : Core) (hw : w ∈ pairCore standardTrio) :
    momentTensor (coreRepresentation g.val w).val =
      standardTensorRepresentation g (momentTensor w.val) := by
  obtain ⟨t, ht⟩ := affineQuotient_spec affineCoverage g
  change HasAffineForm g (standardAffineHom g) t at ht
  let q := standardAffineHom g
  have hm (i : Fin 3) :
      moment (coreRepresentation g.val w).val (q.1 i) =
        Matrix.SpecialLinearGroup.toLin' q.2 (moment w.val i) := by
    have h := moment_affine g q t ht w.val i
    rw [pairCore_parity w hw i, zero_smul, add_zero] at h
    exact h
  rw [momentTensor_apply, momentTensor_apply, map_sum]
  calc
    _ = ∑ i : Fin 3, moment (coreRepresentation g.val w).val (q.1 i) ⊗ₜ[F] beta (q.1 i) :=
      (Equiv.sum_comp q.1 _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hm]
      change _ = Matrix.SpecialLinearGroup.toLin' q.2 (moment w.val i) ⊗ₜ[F]
        BinaryPermutation.coreRepresentation (Fin 3) q.1 (beta i)
      rw [beta_equivariant]

lemma cocodeMoment_equivariant (g : trioStabilizer standardTrio)
    (v : Cocode) (hv : v ∈ standardPairSpace) :
    cocodeMoment (cocodeRepresentation g.val v) =
      standardTensorRepresentation g (cocodeMoment v) := by
  change v ∈ ⨆ B ∈ standardTrio.parts, supportedPairSpace B at hv
  rw [← pairCore_quotient_image standardTrio] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  rw [cocodeRepresentation_mk, cocodeMoment_mk, cocodeMoment_mk]
  exact momentTensor_equivariant g w hw
end
end MathieuCode.TrioCalculation
