module
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The Frattini normalizer of a kernel-hyperplane Sylow subgroup

Let P be Sylow, S normal, and B a hyperplane of an elementary A <= P,
containing A ∩ S. For an odd section D centralized by the image of B, set
H = preimage(D Abar), I = SB, Q = (P ∩ S)B and N = N_H(Q). Then I is
normal in H, Q is Sylow in I, A normalizes Q, A is not contained in I,
and H = NI. All embeddings and the original quotient map are retained.

Source: GLS, Number 2, G.26.18(a), printed pp.152–153. The prime-order and
inversion properties of D are not needed for these Frattini deductions.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Relative Frattini with the intersection normalizer retained. -/
theorem sylow_relative_frattini_join (I H Q : Subgroup G) (hIH : I ≤ H)
    (hHI : H ≤ normalizer (I : Set G))
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = Q) :
    (H ⊓ normalizer (Q : Set G)) ⊔ I = H := by
  let I' := I.subgroupOf H
  let : I'.Normal := normal_subgroupOf_of_le_normalizer hHI
  let e : I ≃* I' := (subgroupOfEquivOfLe hIH).symm
  let P' : Sylow 2 I' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hm : ((P' : Subgroup I').map I'.subtype).map H.subtype = Q := by
    change (((P : Subgroup I).map e.toMonoidHom).map I'.subtype).map H.subtype = Q
    rw [Subgroup.map_map,Subgroup.map_map]
    exact hP
  have hfr := congrArg (map H.subtype) P'.normalizer_sup_eq_top
  rw [Subgroup.map_sup] at hfr
  have hn : (normalizer ((P' : Subgroup I').map I'.subtype : Set H)).map H.subtype ≤
      H ⊓ normalizer (Q : Set G) := by
    refine le_inf (map_subtype_le _) ?_
    have hh := ((P' : Subgroup I').map I'.subtype).le_normalizer_map H.subtype
    rwa [hm] at hh
  have hmapI : I'.map H.subtype = I := map_subgroupOf_eq_of_le hIH
  have hmaptop : (⊤ : Subgroup H).map H.subtype = H := by
    rw [←MonoidHom.range_eq_map,H.range_subtype]
  rw [hmapI,hmaptop] at hfr
  exact le_antisymm (sup_le inf_le_left hIH)
    (hfr.symm.le.trans (sup_le_sup_right hn I))

omit [Finite G] in
private theorem sylow_image_congr (X Y Q : Subgroup G) (he : X = Y)
    (h : ∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = Q) :
    ∃ P : Sylow 2 Y, (P : Subgroup Y).map Y.subtype = Q := by
  subst Y
  exact h

/-- The specified Sylow intersection extends across B inside P. -/
theorem hyperplane_kernel_isSylow (P : Sylow 2 G) (S B : Subgroup G) [S.Normal]
    (hBP : B ≤ (P : Subgroup G)) :
    ∃ QI : Sylow 2 (S ⊔ B : Subgroup G),
      (QI : Subgroup (S ⊔ B : Subgroup G)).map (S ⊔ B : Subgroup G).subtype =
        ((P : Subgroup G) ⊓ S) ⊔ B := by
  let Q := ((P : Subgroup G) ⊓ S) ⊔ B
  have hQP : Q ≤ (P : Subgroup G) := sup_le inf_le_left hBP
  obtain ⟨PS,hPS⟩ := P.exists_subgroupOf_eq_of_normal S
  have hPSmap : (PS : Subgroup S).map S.subtype = (P : Subgroup G) ⊓ S := by
    rw [hPS,subgroupOf_map_subtype]
  have hPSQ : (PS : Subgroup S).map S.subtype ≤ Q := by
    rw [hPSmap]
    exact le_sup_left
  have hh := IsPGroup.exists_sylow_sup_of_coprime_index S Q
    (P.isPGroup'.to_le hQP) le_normalizer_of_normal (PS : Subgroup S) PS.not_dvd_index hPSQ
  have he : S ⊔ Q = S ⊔ B := by
    dsimp only [Q]
    rw [←sup_assoc,sup_of_le_left (show (P : Subgroup G) ⊓ S ≤ S from inf_le_right)]
  exact sylow_image_congr (S ⊔ Q) (S ⊔ B) Q he hh

omit [Finite G] in
private theorem hyperplane_kernel_normalized (P S A B : Subgroup G) [S.Normal]
    [IsElementaryAbelian 2 A] (hAP : A ≤ P) (hBA : B ≤ A) :
    A ≤ normalizer ((P ⊓ S ⊔ B : Subgroup G) : Set G) := by
  have hAS : A ≤ normalizer (P ⊓ S : Set G) :=
    (le_inf (hAP.trans P.le_normalizer) le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  have hAB : A ≤ normalizer (B : Set G) := by
    apply (show A ≤ centralizer (B : Set G) from ?_).trans (centralizer_le_normalizer _)
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨b,hBA hb⟩ : A) ⟨a,ha⟩)
  exact (le_inf hAS hAB).trans (normalizer_inf_normalizer_le_normalizer_sup (P ⊓ S) B)

/-- The source's Q is Sylow in SB and is normalized by the original A. -/
theorem hyperplane_kernel_sylow (P : Sylow 2 G) (S A B : Subgroup G) [S.Normal]
    [IsElementaryAbelian 2 A] (hAP : A ≤ (P : Subgroup G)) (hBA : B ≤ A) :
    let Q := ((P : Subgroup G) ⊓ S) ⊔ B
    (∃ QI : Sylow 2 (S ⊔ B : Subgroup G),
      (QI : Subgroup (S ⊔ B : Subgroup G)).map (S ⊔ B : Subgroup G).subtype = Q) ∧
      Q ≤ (P : Subgroup G) ∧ A ≤ normalizer (Q : Set G) :=
  ⟨hyperplane_kernel_isSylow P S B (hBA.trans hAP),
    sup_le inf_le_left (hBA.trans hAP),hyperplane_kernel_normalized _ S A B hAP hBA⟩

/-- Construct H, I, Q and N from the literal quotient hyperplane. Relative
normality and Frattini coverage are consequences, not additional hypotheses. -/
theorem hyperplane_local_normalizer (P : Sylow 2 G) (S A B : Subgroup G) [S.Normal]
    [IsElementaryAbelian 2 A] (hAP : A ≤ (P : Subgroup G)) (hBA : B ≤ A)
    (hi : B.relIndex A = 2) (hASB : A ⊓ S ≤ B)
    (D : Subgroup (G ⧸ S))
    (hDB : D ≤ centralizer (B.map (QuotientGroup.mk' S) : Set (G ⧸ S))) :
    let H := (D ⊔ A.map (QuotientGroup.mk' S)).comap (QuotientGroup.mk' S)
    let I := S ⊔ B
    let Q := ((P : Subgroup G) ⊓ S) ⊔ B
    let N := H ⊓ normalizer (Q : Set G)
    I ≤ H ∧ H ≤ normalizer (I : Set G) ∧
      (∃ QI : Sylow 2 I, (QI : Subgroup I).map I.subtype = Q) ∧
      Q ≤ (P : Subgroup G) ∧ Q ≤ N ∧ A ≤ N ∧ ¬ A ≤ I ∧ N ⊔ I = H := by
  let q := QuotientGroup.mk' S
  let H := (D ⊔ A.map q).comap q
  let I := S ⊔ B
  let Q := ((P : Subgroup G) ⊓ S) ⊔ B
  let N := H ⊓ normalizer (Q : Set G)
  have hAH : A ≤ H := (le_comap_map q A).trans (comap_mono le_sup_right)
  have hSH : S ≤ H := by
    intro s hs
    change q s ∈ D ⊔ A.map q
    rw [show q s = 1 from (QuotientGroup.eq_one_iff s).mpr hs]
    exact one_mem _
  have hIH : I ≤ H := sup_le hSH (hBA.trans hAH)
  have hAB : A ≤ normalizer (B : Set G) := by
    apply (show A ≤ centralizer (B : Set G) from ?_).trans (centralizer_le_normalizer _)
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨b,hBA hb⟩ : A) ⟨a,ha⟩)
  have hImap : (B.map q).comap q = I := by
    rw [comap_map_eq]
    dsimp only [q,I]
    rw [QuotientGroup.ker_mk']
    exact sup_comm _ _
  have hHI : H ≤ normalizer (I : Set G) := by
    have hm := comap_mono (f := q) (sup_le
      (hDB.trans (centralizer_le_normalizer _))
      ((map_mono hAB).trans (B.le_normalizer_map q)))
    rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective S),hImap] at hm
    exact hm
  obtain ⟨hsyl,hQP,hAQ⟩ := hyperplane_kernel_sylow P S A B hAP hBA
  have hQI : Q ≤ I := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hQN : Q ≤ N := le_inf (hQI.trans hIH) Q.le_normalizer
  have hAI : ¬ A ≤ I := by
    intro hAI
    have hAB' : A ≤ B := by
      intro a ha
      obtain ⟨s,hs,b,hb,he⟩ := mem_sup_of_normal_left.mp (hAI ha)
      have hsA : s ∈ A := by
        have hh : s = a * b⁻¹ := eq_mul_inv_iff_mul_eq.mpr he
        rw [hh]
        exact A.mul_mem ha (A.inv_mem (hBA hb))
      rw [←he]
      exact B.mul_mem (hASB ⟨hsA,hs⟩) hb
    have hh : B.relIndex A = 1 := relIndex_eq_one.mpr hAB'
    omega
  have hfr : N ⊔ I = H := by
    obtain ⟨QI,hQI⟩ := hsyl
    exact sylow_relative_frattini_join I H Q hIH hHI QI hQI
  exact ⟨hIH,hHI,hsyl,hQP,hQN,le_inf hAH hAQ,hAI,hfr⟩
end Theory.GroupTheory
