module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.Contracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.Descent
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.QuotientRecognition.Model
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Sylow maximality and local quotient recognition from marked coordinates

A marked product decomposition of the actual intersection gives its order 72
and an embedded dihedral eight with central involution pi*mu. The normalizer
of that eight fixes its characteristic central involution. If the full root
centralizer had order divisible by 16, its dihedral normalizer would too,
contradicting containment in the intersection. This proves full Sylow
maximality, after which the central odd quotient preserves the Sylow type.

The second product projection has exactly the root kernel, by containment
and cardinality. Its first-isomorphism equivalence, combined with exact
centralizer descent, identifies the actual quotient involution centralizer.
The local product remains an explicit premise, to be supplied by the two
marked-model constructions; this is not unconditional source recognition.
Only the finite centralizer cardinality is used from QuotientRecognition.Model.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 5.4, pp.236–237.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry

private theorem sylow_of_dihedral_centralizer {H : Type*} [Group H] [Finite H]
    (f : DihedralGroup 4 →* H) (hf : Function.Injective f)
    (t : H) (ht : orderOf t = 2) (hft : f (.r 2) = t)
    (hC : Nat.card (centralizer ({t} : Set H)) = 72) :
    ∃ S : Sylow 2 H, Nonempty (S ≃* DihedralGroup 4) := by
  let T := f.range
  let e := MonoidHom.ofInjective hf
  have hT : Nat.card T = 2 ^ 3 := by
    rw [← Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    rfl
  have heZ : (center (DihedralGroup 4)).map e.toMonoidHom = center T := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (centerCongr e ⟨y, hy⟩).property
    · intro hx
      exact ⟨e.symm x, (centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩
  have hZ : (center T).map T.subtype = zpowers t := by
    rw [← heZ, map_map, dihedral_center, MonoidHom.map_zpowers]
    change zpowers (f (.r 2)) = zpowers t
    rw [hft]
  have hN : normalizer (T : Set H) ≤ centralizer ({t} : Set H) :=
    normalizer_le_centralizer_of_characteristic_involution T (center T) t ht hZ
  have hn16 : ¬ 2 ^ 4 ∣ Nat.card H := by
    intro hd
    have hdN := Sylow.prime_pow_dvd_card_normalizer (p := 2) (n := 3) hd hT
    have hdC := hdN.trans (card_dvd_of_le hN)
    rw [hC] at hdC
    norm_num at hdC
  have hi : ¬ 2 ∣ T.index := by
    intro hi
    apply hn16
    rw [← card_mul_index T, hT]
    exact Nat.mul_dvd_mul (dvd_refl (2 ^ 3)) hi
  let S : Sylow 2 H := (IsPGroup.of_card hT).toSylow hi
  exact ⟨S, ⟨e.symm⟩⟩

noncomputable section
variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer) (L : Source.SixLocalData D e)
  (P : LocalProduct D e L)

include P

public theorem LocalProduct.card : Nat.card (intersection D e L) = 72 := by
  rw [Nat.card_congr P.equiv.toEquiv, Nat.card_prod,
    QuotientRecognition.Model.centralizer_card]
  norm_num

private def intersectionIntoRoot : intersection D e L →* rootCentralizer D e L where
  toFun x := ⟨x, x.property.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

public def LocalProduct.dihedralIntoRoot : DihedralGroup 4 →* rootCentralizer D e L :=
  (intersectionIntoRoot D e L).comp (P.equiv.symm.toMonoidHom.comp
    ((MonoidHom.inr (Multiplicative (ZMod 3)) sevenInvolutionCentralizer).comp dihedralEmbedding))

public theorem LocalProduct.dihedralIntoRoot_injective : Function.Injective (P.dihedralIntoRoot D e L) := by
  intro x y h
  apply dihedralEmbedding_injective
  have hY : P.equiv.symm (1, dihedralEmbedding x) = P.equiv.symm (1, dihedralEmbedding y) :=
    Subtype.ext (congrArg (fun a : rootCentralizer D e L => (a : G)) h)
  have hp := congrArg P.equiv hY
  simpa only [P.equiv.apply_symm_apply, Prod.mk.injEq, true_and] using hp

public theorem LocalProduct.dihedralIntoRoot_central :
    P.dihedralIntoRoot D e L (.r 2) = LocalDihedralGeometry.involution D e L := by
  apply Subtype.ext
  change ((P.equiv.symm (1, dihedralEmbedding (.r 2)) : intersection D e L) : G) = _
  rw [dihedralEmbedding_central, ← P.involution, P.equiv.symm_apply_apply]
  rfl

public theorem LocalProduct.root_sylow [Finite G] :
    ∃ S : Sylow 2 (rootCentralizer D e L), Nonempty (S ≃* DihedralGroup 4) := by
  apply sylow_of_dihedral_centralizer (P.dihedralIntoRoot D e L)
    (P.dihedralIntoRoot_injective D e L) (LocalDihedralGeometry.involution D e L) (involution_order D e L)
    (P.dihedralIntoRoot_central D e L)
  rw [Nat.card_congr (centralizerInRootEquiv D e L).toEquiv]
  exact P.card D e L

public theorem LocalProduct.quotient_sylow [Finite G] :
    ∃ S : Sylow 2 (rootQuotient D e L), Nonempty (S ≃* DihedralGroup 4) := by
  obtain ⟨S, hS⟩ := P.root_sylow D e L
  exact quotient_sylow_of_root_sylow D e L S hS

private def projection : centralizerInRoot D e L →* sevenInvolutionCentralizer :=
  (MonoidHom.snd (Multiplicative (ZMod 3)) sevenInvolutionCentralizer).comp
    (P.equiv.toMonoidHom.comp (centralizerInRootEquiv D e L).toMonoidHom)

private theorem projection_surjective : Function.Surjective (projection D e L P) := by
  intro y
  refine ⟨(centralizerInRootEquiv D e L).symm (P.equiv.symm (1, y)), ?_⟩
  change (P.equiv (centralizerInRootEquiv D e L
    ((centralizerInRootEquiv D e L).symm (P.equiv.symm (1, y))))).2 = y
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

private theorem localKernel_le_projection_ker : localKernel D e L ≤ (projection D e L P).ker := by
  let r := (centralizerInRootEquiv D e L).symm (intersectionRoot D e L)
  have hr : projection D e L P r = 1 := P.root
  have hk : localKernel D e L = zpowers r := by
    apply map_subtype_inj.mp
    rw [map_subgroupOf_eq_of_le (rootKernel_le_centralizerInRoot D e L), MonoidHom.map_zpowers]
    rfl
  rw [hk]
  exact zpowers_le.mpr hr

private theorem projection_ker [Finite G] : (projection D e L P).ker = localKernel D e L := by
  have hc := card_eq_card_quotient_mul_card_subgroup (projection D e L P).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (projection_surjective D e L P)).toEquiv, QuotientRecognition.Model.centralizer_card,
    Nat.card_congr (centralizerInRootEquiv D e L).toEquiv, P.card D e L] at hc
  have hkcard : Nat.card (projection D e L P).ker = 3 := by omega
  apply (eq_of_le_of_card_ge (localKernel_le_projection_ker D e L P) ?_).symm
  rw [localKernel_card, hkcard]

public def LocalProduct.quotientCentralizerEquiv [Finite G] :
    centralizer ({quotientInvolution D e L} : Set (rootQuotient D e L)) ≃*
      sevenInvolutionCentralizer :=
  (localQuotientEquiv D e L).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (projection_ker D e L P).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (projection_surjective D e L P)))

end
end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry
