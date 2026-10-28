module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.Factor
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.RootQuotient
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.OddCore
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.QuotientRecognition
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.NoncommCoprod

/-!
# Splitting Held's central extension of A7

An actual A7 identification of the root quotient makes the subgroup
`⟨uv⟩ × A6` have index seven in the full root centralizer. Transfer of the
projection onto the central subgroup of order three is a retraction: on
that subgroup it is the seventh-power map, hence the identity. Its kernel
is the required complement, and the quotient identification identifies that
complement with A7. Mapping it back into the ambient group gives all four
fields of `RootFactor`.

The final `exists_rootFactor` discharges the quotient identification from
the finite simple local hypotheses and the corrected six-point data.
The local dihedral geometry supplies the order-72 intersection, the quotient
Sylow group and its actual involution centralizer. The intersection order
feeds the odd-core calculation; recognition then identifies the quotient
as A7. Thus the final construction has no additional geometry, odd-core,
recognition or splitting premise. The conditional splitting theorem remains
available independently of these source hypotheses.

Source: D. Held, *A Characterization of some multiply transitive permutation
groups, I*, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 5.4, pp.236–237. The transfer argument
supplies the central-extension splitting used at the end of its proof.
-/

open Subgroup
open scoped IsMulCommutative

noncomputable section

private def centralSupEquiv {B : Type*} [Group B]
    (R A : Subgroup B) (hc : R ≤ center B) (hd : Disjoint R A) :
    R × A ≃* (R ⊔ A : Subgroup B) := by
  let f : R × A →* B := R.subtype.noncommCoprod A.subtype
    (fun r a => (mem_center_iff.mp (hc r.property) a).symm)
  have hf : Function.Injective f := mul_injective_of_disjoint hd
  have hr : f.range = R ⊔ A :=
    (MonoidHom.noncommCoprod_range R.subtype A.subtype _).trans (by simp only [range_subtype])
  exact (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)

private theorem centralSupEquiv_apply {B : Type*} [Group B]
    (R A : Subgroup B) (hc : R ≤ center B) (hd : Disjoint R A) (x : R × A) :
    (centralSupEquiv R A hc hd x : B) = x.1 * x.2 := rfl

private theorem exists_central_complement_of_index_seven
    {B : Type*} [Group B] [Finite B]
    (R A : Subgroup B) [IsMulCommutative R]
    (hc : R ≤ center B) (hd : Disjoint R A)
    (hindex : (R ⊔ A).index = 7)
    (hpow : ∀ r : R, r ^ 7 = r) :
    ∃ W : Subgroup B, W.IsComplement' R := by
  let H := R ⊔ A
  let s : R × A ≃* H := centralSupEquiv R A hc hd
  let phi : H →* R := (MonoidHom.fst R A).comp s.symm.toMonoidHom
  have hphi (r : R) : phi ⟨r, (show R ≤ H from le_sup_left) r.property⟩ = r := by
    have hs : s (r, 1) = ⟨r, (show R ≤ H from le_sup_left) r.property⟩ := by
      apply Subtype.ext
      change (centralSupEquiv R A hc hd (r, 1) : B) = r
      rw [centralSupEquiv_apply, coe_one, mul_one]
    change (s.symm ⟨r, _⟩).1 = r
    rw [← hs, s.symm_apply_apply]
  let f : B →* R := MonoidHom.transfer phi
  have hf (r : R) : f r = r := by
    have hkey : ∀ (k : ℕ) (g : B), g⁻¹ * (r : B) ^ k * g ∈ H →
        g⁻¹ * (r : B) ^ k * g = (r : B) ^ k := by
      intro k g _
      have hk := mem_center_iff.mp ((center B).pow_mem (hc r.property) k) g
      rw [mul_assoc, hk.symm, inv_mul_cancel_left]
    have hformula := MonoidHom.transfer_eq_pow phi (r : B) hkey
    have heq : (⟨(r : B) ^ H.index,
        MonoidHom.transfer_eq_pow_aux (r : B) hkey⟩ : H) =
        ⟨r, (show R ≤ H from le_sup_left) r.property⟩ := by
      apply Subtype.ext
      change (r : B) ^ (R ⊔ A).index = r
      rw [hindex]
      exact congrArg Subtype.val (hpow r)
    exact hformula.trans (heq ▸ hphi r)
  refine ⟨f.ker, ?_⟩
  have hdis : Disjoint f.ker R := by
    apply Subgroup.disjoint_def.mpr
    intro x hx hr
    have h1 : f x = 1 := hx
    rw [hf ⟨x, hr⟩] at h1
    exact congrArg Subtype.val h1
  refine ⟨mul_injective_of_disjoint hdis, ?_⟩
  intro x
  let w : f.ker := ⟨x * (f x : B)⁻¹, by
    change f (x * (f x : B)⁻¹) = 1
    rw [map_mul, map_inv, hf, mul_inv_cancel]⟩
  exact ⟨(w, f x), inv_mul_cancel_right x (f x : B)⟩

namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction

open SplitFactor

variable {G : Type*} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e)

/-- An actual quotient equivalence suffices to split the full ambient root
centralizer. Recognition of that quotient is an explicit premise. -/
public theorem exists_rootFactor_of_quotient
    (q : rootQuotient D e L ≃* alternatingGroup (Fin 7)) :
    Nonempty (RootFactor D e L) := by
  let B := rootCentralizer D e L
  let R := rootKernel D e L
  let A := rootSix D e L
  have hc : R ≤ center B := rootKernel_le_center D e L
  have hd : Disjoint R A := rootKernel_disjoint_six D e L
  have hQ : Nat.card (rootQuotient D e L) = 2520 := by
    rw [Nat.card_congr q.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hB : Nat.card B = 7560 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup R, hQ, rootKernel_card D e L]
  have hH : Nat.card (R ⊔ A : Subgroup B) = 1080 := by
    rw [← Nat.card_congr (centralSupEquiv R A hc hd).toEquiv, Nat.card_prod,
      rootKernel_card D e L, rootSix_card D e L]
  have hindex : (R ⊔ A).index = 7 := by
    have h := (R ⊔ A).card_mul_index
    rw [hH, hB] at h
    omega
  have hpow (r : R) : r ^ 7 = r := by
    have hr3 : r ^ 3 = 1 := by
      rw [← rootKernel_card D e L]
      exact pow_card_eq_one'
    calc
      r ^ 7 = (r ^ 3) ^ 2 * r := by group
      _ = r := by rw [hr3, one_pow, one_mul]
  obtain ⟨W, hW⟩ := exists_central_complement_of_index_seven R A hc hd hindex hpow
  let f : W ≃* alternatingGroup (Fin 7) := hW.QuotientMulEquiv.symm.trans q
  refine ⟨{
    W := W.map B.subtype
    alternatingEquiv := (Subgroup.equivMapOfInjective W B.subtype Subtype.val_injective).symm.trans f
    centralizer_root := ?_
    root_disjoint := ?_
  }⟩
  · have h := congrArg (Subgroup.map B.subtype) hW.sup_eq_top
    rw [Subgroup.map_sup, rootKernel_map D e L, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    exact (sup_comm _ _).trans h |>.symm
  · have h := Subgroup.disjoint_map B.subtype_injective hW.disjoint.symm
    rwa [rootKernel_map D e L] at h

/-- Held 5.4: the full ambient centralizer of the root splits as its
central order-three subgroup and an actual A7 factor. The local geometry,
odd-core calculation and quotient recognition are all discharged from the
source hypotheses. Containment of the given A6 follows from `RootFactor.A_le`. -/
public theorem exists_rootFactor [IsSimpleGroup G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hcentralizer : Nat.card (centralizer
      ({D.a10NoncentralInvolution e} : Set G)) = 2880) :
    Nonempty (RootFactor D e L) := by
  obtain ⟨hY, hSylow, hC⟩ :=
    LocalDihedralGeometry.local_geometry_of_source D e L hfusion hcentralizer
  have hO := rootQuotient_oddCore_eq_bot D e L hfusion hcentralizer hY
  obtain ⟨q⟩ := rootQuotient_equiv_seven_of_local_geometry D e L hO hSylow hC
  exact exists_rootFactor_of_quotient D e L q

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction
