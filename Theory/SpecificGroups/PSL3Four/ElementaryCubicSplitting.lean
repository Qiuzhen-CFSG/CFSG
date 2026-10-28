module
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.SpecificGroups.PSL3Four.InnerInvolutionCentralizers
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# Splitting an elementary actor across PSL₃(4) and its centralizer

An elementary two-subgroup in K C_G(K), normalized by an order-three
subgroup B of K ≅ PSL₃(4), is the direct product of its intersections
with K and C_G(K). Its B-fixed subgroup is exactly the centralizer
intersection, and its B-commutator is exactly the K-intersection.

The model input is the actual order-64 centralizer of an inner
involution: no nonidentity inner involution commutes with a cubic of K.
Apply this through the literal conjugation homomorphism and then use
coprime decomposition. No faithfulness of the ambient action is assumed.

Source: Aschbacher--Smith E.2.7, printed p.219; applied to the original
Cartan and opposite actor in 5.1.23, printed pp.645--646, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Matrix.PSL3Four.ElementaryCubicSplitting

private theorem inner_eq_one_of_commutes_cubic (a b : MulAut PSL)
    (ha : a ∈ MulAut.innerSubgroup PSL) (ha2 : a ^ 2 = 1)
    (hb : b ∈ MulAut.innerSubgroup PSL) (hb3 : b ^ 3 = 1)
    (hbn : b ≠ 1) (hc : Commute a b) : a = 1 := by
  by_contra han
  let Q := InnerInvolutionCentralizers.innerCentralizer a
  have hcard : Nat.card Q = 64 :=
    InnerInvolutionCentralizers.card_innerCentralizer a ha han ha2
  let bQ : Q := ⟨b,hb,mem_centralizer_singleton_iff.mpr hc.eq.symm⟩
  have h64 : orderOf bQ ∣ 64 := by
    rw [← hcard]
    exact _root_.orderOf_dvd_natCard bQ
  have h3 : orderOf bQ ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext hb3)
  have he : bQ = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 64 3) h64 h3)
  exact hbn (congrArg Subtype.val he)

variable {X : Type*} [Group X] [Finite X]

/-- The original cubic separates the component and centralizer factors. -/
theorem elementary_split (K E B : Subgroup X) [K.Normal]
    [IsElementaryAbelian 2 E] (e : K ≃* PSL)
    (hBE : B ≤ normalizer (E : Set X)) (hBK : B ≤ K)
    (hB : Nat.card B = 3) (hE : E ≤ K ⊔ centralizer (K : Set X)) :
    E = (E ⊓ K) ⊔ (E ⊓ centralizer (K : Set X)) ∧
      E ⊓ centralizer (B : Set X) = E ⊓ centralizer (K : Set X) ∧
      ⁅E,B⁆ = E ⊓ K ∧ Disjoint (E ⊓ K) (E ⊓ centralizer (K : Set X)) := by
  let f : X →* MulAut PSL := (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
  have hf (k : K) : f (k : X) = MulAut.conj (e k) := by
    ext y
    change e (k * e.symm y * k⁻¹) = e k * y * (e k)⁻¹
    simp only [map_mul,map_inv,e.apply_symm_apply]
  have hz : center PSL = ⊥ := by
    let := Atlas.sl_perfect (F := F) 3 (by decide)
    exact Group.IsPerfect.center_quotient_center_eq_bot SL
  have hfi : Function.Injective (f.comp K.subtype) := by
    intro k l he
    change f (k : X) = f (l : X) at he
    rw [hf,hf] at he
    exact e.injective (MulAut.conj_injective_of_center_eq_bot hz he)
  have hk : f.ker = centralizer (K : Set X) := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.congr e).injective,
      MulAut.conjNormal_ker_eq_centralizer]
  have hEi : E ≤ (MulAut.innerSubgroup PSL).comap f := by
    apply hE.trans
    refine sup_le ?_ ?_
    · intro k hk
      change f k ∈ MulAut.innerSubgroup PSL
      rw [hf ⟨k,hk⟩]
      exact ⟨e ⟨k,hk⟩,rfl⟩
    · rw [← hk]
      exact ker_le_comap f _
  have hBn : B ≠ ⊥ := by
    intro he
    have hc := card_eq_one.mpr he
    omega
  obtain ⟨b,hbn⟩ := ne_bot_iff_exists_ne_one.mp hBn
  let bK : K := ⟨b,hBK b.property⟩
  have hbfn : f b ≠ 1 := by
    intro he
    have hh : bK = 1 := hfi (by
      change f (b : X) = f 1
      rwa [map_one])
    apply hbn
    apply Subtype.ext
    exact congrArg (fun k : K => (k : X)) hh
  have hbf3 : f b ^ 3 = 1 := by
    rw [← map_pow]
    have hh : (b : X) ^ 3 = 1 := congrArg Subtype.val
      (hB ▸ pow_card_eq_one' (x := b))
    rw [hh,map_one]
  have hbi : f b ∈ MulAut.innerSubgroup PSL := by
    rw [hf bK]
    exact ⟨e bK,rfl⟩
  have hfix : E ⊓ centralizer (B : Set X) ≤ centralizer (K : Set X) := by
    rintro x ⟨hx,hc⟩
    rw [← hk]
    refine inner_eq_one_of_commutes_cubic (f x) (f b) (hEi hx) ?_ hbi hbf3 hbfn ?_
    · rw [← map_pow,elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx,map_one]
    · exact (show Commute x (b : X) from
        (mem_centralizer_iff.mp hc b b.property).symm).map f
  have hfixeq : E ⊓ centralizer (B : Set X) = E ⊓ centralizer (K : Set X) :=
    le_antisymm (le_inf inf_le_left hfix)
      (inf_le_inf_left E (centralizer_le hBK))
  have hcop : Nat.Coprime (Nat.card B) (Nat.card E) := by
    obtain ⟨m,hm⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
    rw [hB,hm]
    exact (by decide : Nat.Coprime 3 2).pow_right m
  have hs := eq_commutator_sup_centralizer_of_solvable_coprime E B hBE inferInstance hcop
  rw [hfixeq] at hs
  have hcomm : ⁅E,B⁆ ≤ E ⊓ K := le_inf
    (le_normalizer_iff_commutator_le_left.mp hBE)
    ((commutator_mono le_top hBK).trans (commutator_top_left_le_iff.mpr inferInstance))
  have hdis : Disjoint K (centralizer (K : Set X)) := by
    rw [disjoint_iff]
    apply bot_unique
    rintro x ⟨hx,hc⟩
    have he : f x = 1 := by change x ∈ f.ker; rwa [hk]
    have hh : (⟨x,hx⟩ : K) = 1 := hfi (by
      change f x = f 1
      rwa [map_one])
    exact congrArg (fun k : K => (k : X)) hh
  have hcopK : Nat.Coprime (Nat.card B) (Nat.card (E ⊓ K : Subgroup X)) :=
    hcop.coprime_dvd_right (card_dvd_of_le inf_le_left)
  have hnormK : B ≤ normalizer ((E ⊓ K : Subgroup X) : Set X) :=
    (le_inf hBE (hBK.trans K.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  let : IsElementaryAbelian 2 (E ⊓ K : Subgroup X) := IsElementaryAbelian.of_injective
    (inclusion (show E ⊓ K ≤ E from inf_le_left)) (inclusion_injective _)
  have hfixK : (E ⊓ K) ⊓ centralizer (B : Set X) = ⊥ := by
    apply bot_unique
    exact (le_inf (inf_le_left.trans inf_le_right)
      ((le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans hfix)).trans
        hdis.le_bot
  have hsK := eq_commutator_sup_centralizer_of_solvable_coprime
    (E ⊓ K) B hnormK inferInstance hcopK
  rw [hfixK,sup_bot_eq] at hsK
  have hcommEq : ⁅E,B⁆ = E ⊓ K := le_antisymm hcomm
    (hsK.le.trans (commutator_mono inf_le_left le_rfl))
  exact ⟨le_antisymm (hs.le.trans (sup_le_sup_right hcomm _))
    (sup_le inf_le_left inf_le_left),hfixeq,hcommEq,
      hdis.mono inf_le_right inf_le_right⟩

end Matrix.PSL3Four.ElementaryCubicSplitting
