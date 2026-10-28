module
public import Theory.Representation.RankOne.QuadraticRecognition.CentralQuotientBounds
public import Theory.Representation.Suzuki.BinaryDegree
public import Theory.ElementaryAbelian.Injective
public import Theory.SpecificGroups.Suzuki.TwoConjugateWitness.Witness
public import Theory.SpecificGroups.Suzuki.TwoRank
public import Theory.SpecificGroups.Suzuki.InvolutionFusion
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import Theory.Representation.BinaryOffender.FaithfulRankOne
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic

/-!
# Quadratic actors in nondegenerate Suzuki groups

For Sz(2^(2m+1)), m>0, every faithful binary action satisfies
|A|² ≤ |V/C_V(A)| for every elementary two-subgroup A. For |A|>2, two
conjugates generate an actual smaller Suzuki subgroup. Its faithful central
quotient has degree at least four times that subgroup's field degree, while
the generating pair bounds this degree by twice the original fixed codimension.

Involution conjugacy handles |A|=2: two independent root involutions would
span an actor of fixed codimension at most two if an involution moved only one
dimension, contradicting the preceding square bound. Faithful quadratic actors
are elementary, so this excludes the strict branch of DGS85 (5.12)(b) and
proves (a) for every nondegenerate Suzuki group. Source: Groups and Graphs,
printed pp.109,113–114. The separate Sz(2) case is not asserted here.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender BenderSuzuki.MatrixGroups
namespace Representation.RankOne.QuadraticRecognition
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
local instance finiteSuzukiActorQuotient (C : Submodule (ZMod 2) V) : Finite (V ⧸ C) :=
  Finite.of_surjective _ C.mkQ_surjective

private theorem suzuki_twoCore_trivial {m : ℕ} (hm : 0 < m) :
    pCore 2 (SuzukiMatrixGroup m) = ⊥ := by
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  rcases (inferInstance : (pCore 2 (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hp : IsPGroup 2 (⊤ : Subgroup (SuzukiMatrixGroup m)) := h ▸ pCore_isPGroup
    let : Group.IsNilpotent (SuzukiMatrixGroup m) := (hp.of_equiv Subgroup.topEquiv).isNilpotent
    exact False.elim (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm inferInstance)

/-- The actual two-conjugate subgroup proves the square bound for noncyclic actors. -/
theorem suzuki_noncyclic_square_bound {m : ℕ} (hm : 0 < m)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V) (hf : Function.Injective ρ)
    (S : Sylow 2 (SuzukiMatrixGroup m)) (A : Subgroup (SuzukiMatrixGroup m))
    [IsElementaryAbelian 2 A] (hAS : A ≤ S) (hA : 2 < Nat.card A) :
    Nat.card A ^ 2 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
  obtain ⟨w⟩ := suzuki_twoConjugateWitness hm S A hAS hA
  let I := w.subgroup
  let B := A.subgroupOf I
  let σ := ρ.comp I.subtype
  let τ := globalFixedQuotient σ
  have hfσ : Function.Injective σ := hf.comp I.subtype_injective
  have hc : pCore 2 I = ⊥ := by
    apply Subgroup.map_injective (f := w.equiv.toMonoidHom) w.equiv.injective
    rw [pCore_map_iso, suzuki_twoCore_trivial w.positive, Subgroup.map_bot]
  have hfτ := globalFixedQuotient_faithful σ hfσ hc
  have hlow := Representation.Suzuki.finrank_ge w.positive
    (τ.comp w.equiv.symm.toMonoidHom) (hfτ.comp w.equiv.symm.injective)
  change 4 * (2*w.parameter+1) ≤ Module.finrank (ZMod 2) (V ⧸ fixedSpace σ ⊤) at hlow
  have hu := central_quotient_degree_le_pair σ B w.conjugator w.generate
  have he : fixedCodim σ B = fixedCodim ρ A := by
    unfold fixedCodim
    rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le w.le]
  rw [he] at hu
  have hd : 2 * (2*w.parameter+1) ≤ fixedCodim ρ A := by omega
  let E := B.map w.equiv.toMonoidHom
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf w.le
  let := hB
  have hE : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hcard : Nat.card A ≤ 2^(2*w.parameter+1) := by
    have hr := (primeRank_le_iff_elementary_card_le (SuzukiMatrixGroup w.parameter)).mp
      (suzuki_two_rank w.parameter w.positive).le E hE
    have hEC : Nat.card E = Nat.card A :=
      (Subgroup.card_map_of_injective w.equiv.injective).trans
        (Nat.card_congr (subgroupOfEquivOfLe w.le).toEquiv)
    rwa [hEC] at hr
  calc
    Nat.card A ^ 2 ≤ (2^(2*w.parameter+1))^2 := Nat.pow_le_pow_left hcard 2
    _ = 2^(2*(2*w.parameter+1)) := by rw [← pow_mul, Nat.mul_comm (2*w.parameter+1) 2]
    _ ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
      exact Nat.pow_le_pow_right (by decide) hd

private theorem fixedCodim_sup_le {m : ℕ} (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V)
    (A B : Subgroup (SuzukiMatrixGroup m)) :
    fixedCodim ρ (A ⊔ B) ≤ fixedCodim ρ A + fixedCodim ρ B := by
  have hi : fixedSpace ρ (A ⊔ B) = fixedSpace ρ A ⊓ fixedSpace ρ B :=
    ρ.invariants_comp_sup A B
  have hd := (fixedSpace ρ A).finrank_sup_add_finrank_inf_eq (fixedSpace ρ B)
  have ht := (fixedSpace ρ A ⊔ fixedSpace ρ B).finrank_le
  have hA := fixedCodim_add_finrank ρ A
  have hB := fixedCodim_add_finrank ρ B
  have hAB := fixedCodim_add_finrank ρ (A ⊔ B)
  rw [hi] at hAB
  omega

/-- No involution acts as a binary transvection in a faithful Suzuki action. -/
theorem suzuki_involution_fixedCodim_ge_two {m : ℕ} (hm : 0 < m)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V) (hf : Function.Injective ρ)
    (a : SuzukiMatrixGroup m) (ha : orderOf a = 2) :
    2 ≤ fixedCodim ρ (zpowers a) := by
  obtain ⟨S,hS⟩ := suzukiRootSubgroup_isSylow m hm
  let C := omegaOneAmbient (SuzukiRootSubgroup m)
  let : IsElementaryAbelian 2 C := suzukiRootSubgroup_omega_elementary m hm
  have hc : 2 < Nat.card C := by
    rw [suzukiRootSubgroup_omega_card m hm]
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ 2*m+1)
    norm_num at hh
    omega
  have hC : C ≠ ⊥ := by intro he; rw [he,card_bot] at hc; omega
  obtain ⟨x,hx,hx1⟩ := C.bot_or_exists_ne_one.resolve_left hC
  have hx2 : orderOf x = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian x hx) hx1
  have hxcard : Nat.card (zpowers x) = 2 := by rw [Nat.card_zpowers,hx2]
  have hnot : ¬ C ≤ zpowers x := by
    intro hh
    have hh' := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hh)
    rw [hxcard] at hh'
    omega
  obtain ⟨y,hy,hyx⟩ := SetLike.not_le_iff_exists.mp hnot
  have hy1 : y ≠ 1 := by intro he; exact hyx (he ▸ one_mem _)
  have hy2 : orderOf y = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian y hy) hy1
  let E := zpowers x ⊔ zpowers y
  have hEC : E ≤ C := sup_le (zpowers_le.mpr hx) (zpowers_le.mpr hy)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective
    (Subgroup.inclusion hEC) (Subgroup.inclusion_injective hEC)
  have hES : E ≤ S := by
    rw [hS]
    exact hEC.trans (omegaOneAmbient_le _)
  have hE : 2 < Nat.card E := by
    by_contra! hh
    have he : zpowers x = E := eq_of_le_of_card_ge le_sup_left (by omega)
    exact hyx (he.symm ▸ (mem_sup_right (mem_zpowers y) : y ∈ E))
  have heq (z : SuzukiMatrixGroup m) (hz : orderOf z = 2) :
      fixedCodim ρ (zpowers z) = fixedCodim ρ (zpowers a) := by
    obtain ⟨g,hg⟩ := isConj_iff.mp (suzuki_involutions_isConj m hm a z ha hz)
    have he : (zpowers a).map (MulAut.conj g).toMonoidHom = zpowers z := by
      rw [MonoidHom.map_zpowers]
      exact congrArg zpowers hg
    rw [←he,fixedCodim_map_conj]
  have hd := fixedCodim_sup_le ρ (zpowers x) (zpowers y)
  rw [heq x hx2,heq y hy2] at hd
  have hbound := suzuki_noncyclic_square_bound hm ρ hf S E hES hE
  by_contra! hsmall
  have hdim : fixedCodim ρ E ≤ 2 := by change fixedCodim ρ E ≤ _ at hd; omega
  have hcard : Nat.card (V ⧸ fixedSpace ρ E) ≤ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide) hdim
  nlinarith

/-- Every faithful quadratic actor excludes the strict DGS recognition inequality. -/
theorem suzuki_square_bound {m : ℕ} (hm : 0 < m)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V) (hf : Function.Injective ρ)
    (S : Sylow 2 (SuzukiMatrixGroup m)) (A : Subgroup (SuzukiMatrixGroup m))
    (hAS : A ≤ S) (hq : IsQuadratic ρ A) :
    Nat.card A ^ 2 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
  let : IsElementaryAbelian 2 A := elementary_of_faithful_quadratic ρ hf A hq
  by_cases hA : 2 < Nat.card A
  · exact suzuki_noncyclic_square_bound hm ρ hf S A hAS hA
  by_cases hbot : A = ⊥
  · rw [hbot,card_bot,one_pow]
    exact Nat.card_pos
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hbot
  have ha2 : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  have hd := (suzuki_involution_fixedCodim_ge_two hm ρ hf a ha2).trans
    (NaturalTensor.fixedCodim_mono ρ (zpowers_le.mpr ha))
  have hc : 4 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    change (2 : ℕ)^2 ≤ 2^(fixedCodim ρ A)
    exact Nat.pow_le_pow_right (by decide) hd
  nlinarith

/-- The DGS non-strict size estimate for every nondegenerate Suzuki group. -/
theorem suzuki_actor_bound {m : ℕ} (hm : 0 < m)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V) (hf : Function.Injective ρ)
    (S : Sylow 2 (SuzukiMatrixGroup m)) (A : Subgroup (SuzukiMatrixGroup m))
    (hAS : A ≤ S) (hq : IsQuadratic ρ A) :
    Nat.card A ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
  exact (Nat.le_self_pow (by decide) _).trans (suzuki_square_bound hm ρ hf S A hAS hq)

end Representation.RankOne.QuadraticRecognition
