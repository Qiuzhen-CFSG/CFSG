module

public import Theory.Representation.BinaryIrreducibleCentralizer
public import GorensteinWalter.PGammaL2OuterProduct
public import GorensteinWalter.PSL2Center
public import Theory.FieldTheory.FiniteAutomorphismOrder
/-!
# The actual outer action of disjoint binary actors

Conjugation on a centerless component is transported through its given PSL₂
isomorphism and the concrete semilinear automorphism equivalence. An involution
whose action is inner belongs to the component: its remaining centralizing
factor is an involution, hence trivial by faithful binary irreducibility.
Thus a disjoint elementary actor embeds in the actual diagonal--field quotient,
which has order twice the field degree. No embedding of the entire ambient
quotient into the outer automorphism group is assumed.

This is the outer-rank step in Guralnick--Malle, Classification of 2F-modules I,
Proposition 4.1, manuscript pp.8--9, used in Aschbacher--Smith K.2, printed p.453.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration
open Subgroup Representation

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

private lemma inner_involution_mem (ρ : Representation (ZMod 2) G V)
    (L : Subgroup G) [L.Normal] [IsIrreducible (ρ.comp L.subtype)]
    (hf : Function.Injective ρ) (hc : center L = ⊥)
    {t : G} (ht : t ^ 2 = 1) (l : L)
    (hi : MulAut.conjNormal (H := L) t = MulAut.conj l) : t ∈ L := by
  have hlsq : l ^ 2 = 1 := by
    have hh : MulAut.conj (l ^ 2) = 1 := by
      rw [map_pow, ← hi, ← map_pow, ht, map_one]
    have hz : l ^ 2 ∈ center L := by
      rw [mem_center_iff]
      intro x
      have he := congrArg (fun a : MulAut L => a x) hh
      change l ^ 2 * x * (l ^ 2)⁻¹ = x at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    exact (show l ^ 2 ∈ (⊥ : Subgroup L) from hc ▸ hz)
  have htl : t * (l : G) = (l : G) * t := by
    have hh := congrArg (fun a : MulAut L => ((a l : L) : G)) hi
    change t * (l : G) * t⁻¹ = (l : G) * (l : G) * (l : G)⁻¹ at hh
    simpa only [mul_inv_cancel_right, mul_inv_eq_iff_eq_mul] using hh
  have hcent : t * (l : G)⁻¹ ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    have hh := congrArg (fun a : MulAut L => ((a ⟨x, hx⟩ : L) : G)) hi
    change t * x * t⁻¹ = (l : G) * x * (l : G)⁻¹ at hh
    have hcomm : t * (l : G)⁻¹ = (l : G)⁻¹ * t :=
      (Commute.inv_right (show Commute t (l : G) from htl)).eq
    calc
      x * (t * (l : G)⁻¹) = x * ((l : G)⁻¹ * t) := by rw [hcomm]
      _ = (l : G)⁻¹ * (t * x * t⁻¹) * t := by rw [hh]; group
      _ = (t * (l : G)⁻¹) * x := by rw [hcomm]; group
  have hsq : (t * (l : G)⁻¹) ^ 2 = 1 := by
    rw [(Commute.inv_right (show Commute t (l : G) from htl)).mul_pow, ht, inv_pow]
    have hl : (l : G) ^ 2 = 1 := congrArg Subtype.val hlsq
    rw [hl, inv_one, mul_one]
  have he := BinaryIrreducibleCentralizer.centralizing_square_one_eq_one ρ L hf hsq hcent
  have heq : t = (l : G) := mul_inv_eq_one.mp he
  exact heq ▸ l.property

open GorensteinWalter
open scoped MatrixGroups

noncomputable def semilinearEquiv (F : Type*) [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (hlarge : 3 < Nat.card F) :
    PGammaL2 F ≃* MulAut (PSL2 F) :=
  MulEquiv.ofBijective (pGammaL2ToMulAutPSL2 F hF hlarge)
    ⟨pGammaL2ToMulAutPSL2_injective F hF hlarge,
      by obtain ⟨p, n, hp, ho, hn, hc⟩ := hF
         let : Fact p.Prime := ⟨hp⟩
         have hF : IsOddPrimePower (Nat.card F) := ⟨p, n, hp, ho, hn, hc⟩
         exact pGammaL2ToMulAutPSL2_surjective F hc hF hlarge⟩

noncomputable def semilinearAction {F : Type*} [Field F] [Finite F]
    (L : Subgroup G) [L.Normal] (eL : L ≃* PSL2 F)
    (hF : IsOddPrimePower (Nat.card F)) (hlarge : 3 < Nat.card F) : G →* PGammaL2 F :=
  (semilinearEquiv F hF hlarge).symm.toMonoidHom.comp
    ((MulAut.congr eL).toMonoidHom.comp (MulAut.conjNormal (H := L)))

lemma semilinearAction_coe {F : Type*} [Field F] [Finite F]
    (L : Subgroup G) [L.Normal] (eL : L ≃* PSL2 F)
    (hF : IsOddPrimePower (Nat.card F)) (hlarge : 3 < Nat.card F) (l : L) :
    semilinearAction L eL hF hlarge (l : G) =
      SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (eL l)) := by
  apply (semilinearEquiv F hF hlarge).injective
  simp only [semilinearAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  change (MulAut.congr eL) (MulAut.conjNormal (H := L) (l : G)) =
    pGammaL2ToMulAutPSL2 F hF hlarge _
  rw [MulAut.conjNormal_val, pGammaL2ToMulAutPSL2_inl,
    pgl2InnerAutPSL2_toPGL]
  ext x
  simp [MulAut.congr, MulAut.conj_apply]

lemma involution_mem_inner_iff {F : Type*} [Field F] [Finite F]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    [IsIrreducible (ρ.comp L.subtype)] (hf : Function.Injective ρ)
    (eL : L ≃* PSL2 F) (hF : IsOddPrimePower (Nat.card F))
    (hlarge : 3 < Nat.card F) {t : G} (ht : t ^ 2 = 1) :
    semilinearAction L eL hF hlarge t ∈ pGammaL2PSLRange F ↔ t ∈ L := by
  constructor
  · rintro ⟨x, hx⟩
    let l : L := eL.symm x
    have heq : semilinearAction L eL hF hlarge t = semilinearAction L eL hF hlarge (l : G) := by
      rw [semilinearAction_coe]
      simpa only [l, MulEquiv.apply_symm_apply, MonoidHom.comp_apply] using hx.symm
    have hi : MulAut.conjNormal (H := L) t = MulAut.conj l := by
      have hh := (semilinearEquiv F hF hlarge).symm.injective heq
      have hh' := (MulAut.congr eL).injective hh
      exact hh'.trans MulAut.conjNormal_val
    have hc : center L = ⊥ := by
      apply le_bot_iff.mp
      intro l hl
      have hcl := (Subgroup.centerCongr eL ⟨l, hl⟩).property
      change eL l ∈ center (PSL2 F) at hcl
      rw [psl2_center_eq_bot] at hcl
      exact eL.injective (hcl.trans (map_one eL).symm)
    exact inner_involution_mem ρ L hf hc ht l hi
  · intro htL
    rw [semilinearAction_coe L eL hF hlarge ⟨t, htL⟩]
    exact ⟨eL ⟨t, htL⟩, rfl⟩

lemma disjoint_actor_card_le {F : Type*} [Field F] [Finite F]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    [IsIrreducible (ρ.comp L.subtype)] (hf : Function.Injective ρ)
    (eL : L ≃* PSL2 F) {p n : ℕ} (hp : p.Prime) (ho : Odd p)
    (hc : Nat.card F = p ^ n) (hn : 0 < n) (hlarge : 3 < Nat.card F)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hdis : A ⊓ L = ⊥) :
    Nat.card A ≤ 2 * n := by
  let hF : IsOddPrimePower (Nat.card F) := ⟨p, n, hp, ho, hn, hc⟩
  let : Fact (IsOddPrimePower (Nat.card F)) := ⟨hF⟩
  let f := (pGammaL2OuterProduct F).comp ((semilinearAction L eL hF hlarge).comp A.subtype)
  have hf' : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro a ha
    have hi : semilinearAction L eL hF hlarge a ∈ pGammaL2PSLRange F := by
      rw [← pGammaL2OuterProduct_ker]
      exact ha
    have haL := (involution_mem_inner_iff ρ L hf eL hF hlarge
      (elemPow_eq_one_of_isElementaryAbelian (a : G) a.property)).mp hi
    apply Subtype.ext
    exact (show (a : G) ∈ (⊥ : Subgroup G) from hdis ▸ ⟨a.property, haL⟩)
  let : Finite (PGL2 F) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  have hcard := Nat.card_le_card_of_injective f hf'
  rw [Nat.card_prod, show Nat.card (PGL2 F ⧸
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) = 2 from
    pgl2_psl2Range_index_eq_two F hF,
    FiniteField.card_ringAut_of_card_prime_pow hp hc] at hcard
  exact hcard

lemma semilinearAction_component_injective {F : Type*} [Field F] [Finite F]
    (L : Subgroup G) [L.Normal] (eL : L ≃* PSL2 F)
    (hF : IsOddPrimePower (Nat.card F)) (hlarge : 3 < Nat.card F) :
    Function.Injective ((semilinearAction L eL hF hlarge).comp L.subtype) := by
  intro x y hxy
  change semilinearAction L eL hF hlarge (x : G) = semilinearAction L eL hF hlarge (y : G) at hxy
  rw [semilinearAction_coe, semilinearAction_coe] at hxy
  exact eL.injective (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    (SemidirectProduct.inl_injective hxy))

lemma semilinearAction_map_component {F : Type*} [Field F] [Finite F]
    (L : Subgroup G) [L.Normal] (eL : L ≃* PSL2 F)
    (hF : IsOddPrimePower (Nat.card F)) (hlarge : 3 < Nat.card F) :
    L.map (semilinearAction L eL hF hlarge) = pGammaL2PSLRange F := by
  ext y
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [semilinearAction_coe L eL hF hlarge ⟨l, hl⟩]
    exact ⟨eL ⟨l, hl⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨(eL.symm x : G), (eL.symm x).property, ?_⟩
    rw [semilinearAction_coe]
    simp only [MulEquiv.apply_symm_apply, MonoidHom.comp_apply]

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration
