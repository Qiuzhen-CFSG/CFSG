module
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.PairOrthogonal
public import Theory.GroupTheory.ExtraspecialSquareFixed

/-!
# Fixed spaces of the two original pair generators

An element outside the index-two seed generates the module modulo that
seed. Inner automorphisms from the seed act trivially on the central
quotient. A fixed vector in the opposite seed is therefore fixed by the
whole module, and F.9.5(5)'s separation makes it zero. This identifies the
fixed spaces of both original generators, retaining the chosen element
and its literal conjugate.

Extraspeciality and the central-point identification are supplied by the
original pair geometry in NaturalSource.PairFixed. Source: Aschbacher--Smith
F.9.5(5--6.ii), printed pp.319--320, applied in 12.6.26, p.831.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G]

private theorem generator_separates_opposite
    (I P V W B Z : Subgroup G) [IsExtraspecial 2 P]
    (n : I ≤ normalizer (P : Set G))
    (hVI : V ≤ I) (hWP : W ≤ P)
    (hWV : W ≤ V) (hi : W.relIndex V = 2)
    (hBZ : B ≤ normalizer (Z : Set G))
    (hcent : (center P).map P.subtype = Z)
    (hsep : commutatorPreimage B V Z = Z)
    (v : G) (hv : v ∈ V) (hvw : v ∉ W) :
    ∀ y ∈ B.subgroupOf P,
      seedConjugation I P n ⟨v,hVI hv⟩ y / y ∈ center P → y ∈ center P := by
  let β := (quotientAut (center P)).comp (seedConjugation I P n)
  let : MulAction I (P ⧸ center P) := MulAction.compHom _ β
  intro y hy hfixed
  let C := MulAction.stabilizer I (QuotientGroup.mk' (center P) y)
  have hWC : W.subgroupOf I ≤ C := by
    intro w hw
    change quotientAut (center P) (seedConjugation I P n w) (QuotientGroup.mk' (center P) y) =
      QuotientGroup.mk' (center P) y
    rw [quotientAut_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    have he : seedConjugation I P n w y / y = ⁅(⟨w.val,hWP hw⟩ : P),y⁆ := by
      apply Subtype.ext
      simp only [seedConjugation_apply,commutatorElement_def,
        Subgroup.coe_mul,Subgroup.coe_inv,div_eq_mul_inv]
    rw [he]
    exact ExtraspecialSquare.commutator_mem_center P _ _
  have hvC : (⟨v,hVI hv⟩ : I) ∈ C := by
    change quotientAut (center P) (seedConjugation I P n ⟨v,hVI hv⟩) (QuotientGroup.mk' (center P) y) =
      QuotientGroup.mk' (center P) y
    rw [quotientAut_apply_mk]
    exact QuotientGroup.eq_iff_div_mem.mpr hfixed
  have hgen := sup_zpowers_eq_of_relIndex_prime
    (subgroupOf_mono I hWV) Nat.prime_two
    (show (W.subgroupOf I).relIndex (V.subgroupOf I) = 2 by rw [relIndex_subgroupOf hVI]; exact hi)
    (show (⟨v,hVI hv⟩ : I) ∈ V.subgroupOf I from hv)
    (show (⟨v,hVI hv⟩ : I) ∉ W.subgroupOf I from hvw)
  have hVC : V.subgroupOf I ≤ C := by
    rw [←hgen]
    exact sup_le hWC (zpowers_le.mpr hvC)
  have hyZ : y.val ∈ Z := by
    rw [←hsep]
    apply (mem_commutatorPreimage_iff B V Z hBZ y.val).mpr
    refine ⟨hy,fun u hu => ?_⟩
    have huC := hVC (show (⟨u,hVI hu⟩ : I) ∈ V.subgroupOf I from hu)
    change quotientAut (center P) (seedConjugation I P n ⟨u,hVI hu⟩) (QuotientGroup.mk' (center P) y) =
      QuotientGroup.mk' (center P) y at huC
    rw [quotientAut_apply_mk] at huC
    have hc : seedConjugation I P n ⟨u,hVI hu⟩ y / y ∈ center P :=
      QuotientGroup.eq_iff_div_mem.mp huC
    have hm := hcent.le (mem_map_of_mem P.subtype hc)
    have hm : ⁅u,y.val⁆ ∈ Z := by
      simpa only [subtype_apply,div_eq_mul_inv,Subgroup.coe_mul,Subgroup.coe_inv,seedConjugation_apply,commutatorElement_def] using hm
    rw [←commutatorElement_inv]
    exact Z.inv_mem hm
  have : y.val ∈ (center P).map P.subtype := hcent.symm ▸ hyZ
  rcases this with ⟨x,hx,he⟩
  exact (Subtype.ext he : x=y) ▸ hx

private theorem generator_fixed_ker
    (I P V W B Z : Subgroup G) [IsExtraspecial 2 P] [IsMulCommutative V]
    (n : I ≤ normalizer (P : Set G))
    (hVI : V ≤ I) (hWP : W ≤ P) (hBP : B ≤ P) (hP : W ⊔ B = P)
    (hWV : W ≤ V) (hi : W.relIndex V = 2)
    (hBZ : B ≤ normalizer (Z : Set G))
    (hcent : (center P).map P.subtype = Z)
    (hsep : commutatorPreimage B V Z = Z)
    (v : G) (hv : v ∈ V) (hvw : v ∉ W) :
    LinearMap.ker ((ExtraspecialSquare.linearAction P
      (seedConjugation I P n ⟨v,hVI hv⟩)).toLinearMap - LinearMap.id) =
      ExtraspecialSquare.imageSpace P (W.subgroupOf P) := by
  apply ExtraspecialSquare.fixed_ker_eq_imageSpace _ _ (B.subgroupOf P)
  · rw [←subgroupOf_sup hWP hBP,hP,subgroupOf_self]
  · intro x hx
    have hcomm : Commute v x.val := by
      open scoped IsMulCommutative in
      exact congrArg Subtype.val (mul_comm (⟨v,hv⟩ : V) ⟨x.val,hWV hx⟩)
    have he : seedConjugation I P n ⟨v,hVI hv⟩ x / x = 1 := by
      apply Subtype.ext
      change v * x.val * v⁻¹ / x.val = 1
      rw [hcomm.eq,mul_assoc,mul_inv_cancel,mul_one,div_self']
    rw [he]
    exact (center P).one_mem
  · exact generator_separates_opposite I P V W B Z n hVI hWP hWV hi hBZ hcent hsep v hv hvw

variable [Finite G] {D : ChapterF.Section09.Setup G}

/-- Each original outside element fixes exactly its own seed image on the
central quotient, as does its specified conjugate on the opposite seed. -/
theorem pair_square_fixed_spaces (h : D.Hypothesis)
    (hi : D.Vplus.relIndex D.V = 2)
    (hp : ∀ t ∈ D.H, D.V₁ < D.V ⊓ D.V.map (MulAut.conj t).toMonoidHom →
      IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj t).toMonoidHom : Subgroup G))
    (g : G) (hg : g ∈ D.H)
    (hn : ¬ IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G))
    (hs : IsExtraspecial 2 (D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom : Subgroup G))
    (hz : (center (D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom : Subgroup G)).map
      (D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom).subtype = D.V₁)
    (n : (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom) ≤
      normalizer (((D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom) : Subgroup G) : Set G))
    (v : D.V) (hvw : v.val ∉ D.Vplus) :
    let I := D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom
    let P := D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom
    letI := hs
    let α := (ExtraspecialSquare.isometryAction P).comp (seedConjugation I P n)
    LinearMap.ker ((α ⟨v.val,mem_sup_left v.property⟩).val.toLinearMap - LinearMap.id) =
      ExtraspecialSquare.imageSpace P (D.Vplus.subgroupOf P) ∧
    LinearMap.ker ((α ⟨(MulAut.conj g) v.val,
      mem_sup_right (mem_map_of_mem (MulAut.conj g).toMonoidHom v.property)⟩).val.toLinearMap - LinearMap.id) =
      ExtraspecialSquare.imageSpace P ((D.Vplus.map (MulAut.conj g).toMonoidHom).subgroupOf P) := by
  let := h.elementary
  let f := (MulAut.conj g).toMonoidHom
  let I := D.V ⊔ D.V.map f
  let P := D.Vplus ⊔ D.Vplus.map f
  let : IsExtraspecial 2 P := hs
  let : IsElementaryAbelian 2 (D.V.map f) := IsElementaryAbelian.map f
  have hBZ : D.Vplus.map f ≤ normalizer (D.V₁ : Set G) :=
    (pair_seed_conjugate_le_closure (D := D) g hg).trans
      (h.UH_le_H.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))
  have hWZ : D.Vplus ≤ normalizer (D.V₁ : Set G) :=
    h.plus_le_H.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  have hvgn : f v.val ∉ D.Vplus.map f := by
    rintro ⟨w,hw,he⟩
    exact hvw ((MulAut.conj g).injective he ▸ hw)
  refine ⟨?_,?_⟩
  · exact generator_fixed_ker I P D.V D.Vplus (D.Vplus.map f) D.V₁ n
      le_sup_left le_sup_left le_sup_right rfl h.plus_le hi hBZ hz
      (h.pair_conjugate_seed_fixed_eq_point hp g hg hn) v.val v.property hvw
  · exact generator_fixed_ker I P (D.V.map f) (D.Vplus.map f) D.Vplus D.V₁ n
      le_sup_right le_sup_right le_sup_left (sup_comm _ _) (map_mono h.plus_le)
      (by rw [relIndex_map_map_of_injective _ _ (MulAut.conj g).injective];exact hi)
      hWZ hz (h.pair_seed_fixed_eq_point hp g hg hn) (f v.val) (mem_map_of_mem f v.property) hvgn

end CFSG.Quasithin.Chapter12.Section06.Nonabelian
