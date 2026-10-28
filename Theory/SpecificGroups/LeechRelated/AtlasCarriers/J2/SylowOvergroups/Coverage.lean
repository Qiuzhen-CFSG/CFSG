module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SylowOvergroups.Checks
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Sylow

/-!
# Exhaustive Hall--Janko Sylow-overgroup coverage

The existing four-level normal forms give a four-point base. Fifteen
separated cosets exhaust the centralizer of the fixed central involution,
by its order 1920 and the Sylow order 128. Combining them with its existing
315-coset cover and the checked factors gives 72 Sylow double cosets.
The representative tests put every proper Sylow overgroup in the union
of the two fixed locals, hence in one of them.

Source: ATLAS J2G1-p100B0 and Aschbacher--Smith A.3.12(16), pp.47--48.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.SylowOvergroups
open Subgroup Theory.GroupTheory GeneratorPair GeneratorPair.SecondOrbitCertificate
open ExceptionalParabolics ExceptionalParabolics.Seed ExceptionalParabolics.PairNormalizer
open ExceptionalParabolics.FirstParabolic.OrderData Data
/-- Four point images determine an element of the actual Hall--Janko carrier. -/
theorem four_ext (x y : Carrier)
    (h : ∀ p : Fin 4, inclusion x (p.castLE (by decide)) = inclusion y (p.castLE (by decide))) : x = y := by
  obtain ⟨⟨i₀,i₁,i₂,i₃⟩, hx⟩ := normalForm_cover x
  obtain ⟨⟨j₀,j₁,j₂,j₃⟩, hy⟩ := normalForm_cover y
  have h0 : inclusion x 0 = inclusion y 0 := h 0
  have h1 : inclusion x 1 = inclusion y 1 := h 1
  have h2 : inclusion x 2 = inclusion y 2 := h 2
  have h3 : inclusion x 3 = inclusion y 3 := h 3
  rw [hx,hy] at h0 h1 h2 h3
  have h₀ := congrArg decode0 h0
  simp only [normalForm, Equiv.Perm.mul_apply, rep3_fix0, rep2_fix0, rep1_fix0,
    decode0_spec] at h₀
  subst j₀
  have h₁ := congrArg decode1 ((rep0 i₀).injective (by
    simpa only [normalForm, Equiv.Perm.mul_apply, rep3_fix1, rep2_fix1] using h1))
  simp only [decode1_spec] at h₁
  subst j₁
  have h₂ := congrArg decode2 ((rep1 i₁).injective ((rep0 i₀).injective (by
    simpa only [normalForm, Equiv.Perm.mul_apply, rep3_fix2] using h2)))
  simp only [decode2_spec] at h₂
  subst j₂
  have h₃ := congrArg decode3 ((rep2 i₂).injective ((rep1 i₁).injective
    ((rep0 i₀).injective (by simpa only [normalForm, Equiv.Perm.mul_apply] using h3))))
  simp only [decode3_spec] at h₃
  subst j₃
  exact inclusion_injective (hx.trans hy.symm)

private theorem eval_inclusion {n : ℕ} (gs : Fin n → Carrier)
    (fs : Fin n → Fin 100 → Fin 100) (h : ∀ i p, inclusion (gs i) p = fs i p)
    (w : List (Fin n)) (p : Fin 100) : inclusion (evalWord gs w) p = evalFun fs w p := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih =>
    rw [evalWord, map_mul, Equiv.Perm.mul_apply, ih, h, evalFun]

def cRep (i : Fin 15) : Carrier := localWord (cWord i)
def dRep (i : Fin 72) : Carrier := cRep (dIndex i).1 * FirstFusion.rep (dIndex i).2

private theorem cRep_spec (i : Fin 15) (p : Fin 100) : inclusion (cRep i) p = cVal i p := by
  apply (eval_inclusion FirstFusion.letter FirstFusion.letterValue
    (fun j q => by rw [FirstFusion.inclusion_letter]; exact (FirstFusion.letterValue_eq j q).symm)
    (cWord i) p).trans
  exact (cWord_spec i p).symm

private theorem fRep_spec (i : Fin 315) (p : Fin 100) : inclusion (FirstFusion.rep i) p = fVal i p := by
  have aux : ∀ (n : ℕ) (j : Fin 315), j.val = n → ∀ q,
      inclusion (FirstFusion.rep j) q = fVal j q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj q
      by_cases hzero : j = 0
      · subst j
        rw [FirstFusion.rep_zero, map_one]
        exact (fBase_spec q).symm
      obtain ⟨hlt,hw,_⟩ := FirstFusion.word_data j hzero
      have hr : FirstFusion.rep j = FirstFusion.rep (FirstFusion.OrbitData.parent j) *
          FirstFusion.letter (FirstFusion.OrbitData.parentLetter j) := by
        simp only [FirstFusion.rep,hw,evalWord_append,evalWord,mul_one]
      rw [hr,map_mul,Equiv.Perm.mul_apply,FirstFusion.inclusion_letter,
        ih _ (hj ▸ hlt) _ rfl]
      rw [fStep_spec j q hzero,FirstFusion.letterValue_eq]
  exact aux i.val i rfl p

private theorem sRep_spec (i : Fin 128) (p : Fin 100) : inclusion (sElement i) p = sVal i p := by
  rw [sElement_inclusion]
  exact (sTable_spec i p).symm

private theorem dRep_spec (i : Fin 72) (p : Fin 100) : inclusion (dRep i) p = dVal i p := by
  rw [dRep,map_mul,Equiv.Perm.mul_apply,fRep_spec,cRep_spec]
  rfl

private theorem cRep_mem (i : Fin 15) : cRep i ∈ l₁ := by
  apply mem_centralizer_singleton_iff.mpr
  apply inclusion_injective
  apply Equiv.ext
  intro p
  change inclusion (cRep i * FirstFusion.t) p = inclusion (FirstFusion.t * cRep i) p
  simp only [map_mul,Equiv.Perm.mul_apply,FirstFusion.inclusion_t,cRep_spec]
  exact cCentral_spec i p

private theorem cRep_separation (i j : Fin 15) (x : s) (he : cRep i = x * cRep j) : i = j := by
  obtain ⟨k,hk⟩ := exists_sElement x.property
  have hp (p : Fin 100) := congrArg (fun a : Carrier => inclusion a p) he
  simp only [map_mul,Equiv.Perm.mul_apply,← hk,sRep_spec,cRep_spec] at hp
  exact cSeparate_spec i j k ⟨hp 0,hp 1,hp 2⟩

private theorem centralizer_cover (x : l₁) : ∃ (u : s) (i : Fin 15), (x : Carrier) = u * cRep i := by
  let f : s × Fin 15 → l₁ := fun ui =>
    ⟨ui.1.val * cRep ui.2, l₁.mul_mem (SecondParabolic.s_le_l₁ ui.1.property) (cRep_mem ui.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨u,i⟩ ⟨v,j⟩ huv
    have he : u.val * cRep i = v.val * cRep j := congrArg Subtype.val huv
    have hij := cRep_separation i j (u⁻¹ * v) (by
      change cRep i = (u.val⁻¹ * v.val) * cRep j
      rw [mul_assoc,← he,inv_mul_cancel_left])
    subst j
    exact Prod.ext (Subtype.ext (mul_right_cancel he)) rfl
  have hc : Nat.card l₁ ≤ Nat.card (s × Fin 15) := by
    rw [Nat.card_prod,card_s,Nat.card_fin,FirstParabolic.card_l₁]
  obtain ⟨⟨u,i⟩,hi⟩ := (hf.bijective_of_nat_card_le hc).surjective x
  exact ⟨u,i,(congrArg Subtype.val hi).symm⟩

/-- Every element factors through one of the 72 fixed Sylow double cosets. -/
theorem double_coset_cover (x : Carrier) :
    ∃ (j : Fin 72) (u v : s), x = u * dRep j * v := by
  obtain ⟨c,j,hj⟩ := FirstFusion.cosetCover.covers FirstFusion.letter_generates x
  change x = c.val * FirstFusion.rep j at hj
  obtain ⟨u,i,hi⟩ := centralizer_cover c
  have ht : cRep i * FirstFusion.rep j =
      sElement (factor i j).2.1 * dRep (factor i j).1 * sElement (factor i j).2.2 := by
    apply four_ext
    intro p
    simp only [map_mul,Equiv.Perm.mul_apply,cRep_spec,fRep_spec,sRep_spec,dRep_spec]
    exact factor_spec i j p
  refine ⟨(factor i j).1,u * ⟨sElement (factor i j).2.1,sElement_mem _⟩,
    ⟨sElement (factor i j).2.2,sElement_mem _⟩,?_⟩
  change x = (u.val * sElement (factor i j).2.1) * dRep _ * sElement _
  rw [hj,hi,mul_assoc,ht]
  simp only [mul_assoc]

private def pGenerator (i : Fin 9) : Carrier :=
  if h : i.val < 7 then sGenerator ⟨i.val,h⟩ else oddGenerator ⟨i.val-7,by omega⟩

private theorem pGenerator_mem (i : Fin 9) : pGenerator i ∈ p₂ := by
  unfold pGenerator
  split
  · exact candidate_le_p₂ (s_le_candidate (subset_closure ⟨_,rfl⟩))
  · exact oddGenerator_mem_p₂ _

private theorem pGenerator_spec (i : Fin 9) (p : Fin 100) : inclusion (pGenerator i) p = pValue i p := by
  unfold pGenerator pValue
  split
  · rw [sGenerator_inclusion]
    exact (sTable_spec _ p).symm
  · rw [oddGenerator_inclusion]
    rfl

private def gGenerator (j : Fin 72) (i : Fin 16) : Carrier :=
  if h : i.val < 7 then sGenerator ⟨i.val,h⟩
  else if i.val = 7 then dRep j
  else if h : i.val < 15 then (sGenerator ⟨i.val-8,by omega⟩)⁻¹
  else (dRep j)⁻¹

private theorem gGenerator_mem (j : Fin 72) (i : Fin 16) (P : Subgroup Carrier)
    (hS : s ≤ P) (hj : dRep j ∈ P) : gGenerator j i ∈ P := by
  unfold gGenerator
  split
  · exact hS (subset_closure ⟨_,rfl⟩)
  · split
    · exact hj
    · split
      · exact P.inv_mem (hS (subset_closure ⟨_,rfl⟩))
      · exact P.inv_mem hj

private theorem gGenerator_spec (j : Fin 72) (i : Fin 16) (p : Fin 100) :
    inclusion (gGenerator j i) p = gValue j i p := by
  unfold gGenerator gValue
  split
  · rw [sGenerator_inclusion]
    exact (sTable_spec _ p).symm
  · split
    · exact dRep_spec j p
    · split
      · rw [map_inv,sGenerator_inclusion]
        exact (sInv_spec _ p).symm
      · rw [map_inv]
        apply (inclusion (dRep j)).injective
        change inclusion (dRep j) ((inclusion (dRep j)).symm p) = _
        rw [Equiv.apply_symm_apply,dRep_spec,dInv_spec]

private theorem word_mem {n : ℕ} (gs : Fin n → Carrier) (P : Subgroup Carrier)
    (h : ∀ i, gs i ∈ P) (w : List (Fin n)) : evalWord gs w ∈ P := by
  induction w with
  | nil => exact P.one_mem
  | cons i w ih => exact P.mul_mem (h i) ih

private theorem representative_mem (P : Subgroup Carrier) (hS : s ≤ P) (hP : P ≠ ⊤)
    (j : Fin 72) (hj : dRep j ∈ P) : dRep j ∈ l₁ ∨ dRep j ∈ p₂ := by
  rcases row_spec j with hc | hp | hg
  · left
    apply mem_centralizer_singleton_iff.mpr
    apply inclusion_injective
    apply Equiv.ext
    intro p
    change inclusion (dRep j * FirstFusion.t) p = inclusion (FirstFusion.t * dRep j) p
    simp only [map_mul,Equiv.Perm.mul_apply,FirstFusion.inclusion_t,dRep_spec]
    exact hc p
  · right
    have he : dRep j = evalWord pGenerator (pWord j) := by
      apply four_ext
      intro p
      rw [dRep_spec,eval_inclusion pGenerator pValue pGenerator_spec]
      exact hp p
    rw [he]
    exact word_mem _ _ pGenerator_mem _
  · have hb : b ∈ P := by
      have he : evalWord (gGenerator j) (gWord j) = b := by
        apply four_ext
        intro p
        rw [eval_inclusion _ _ (gGenerator_spec j)]
        change _ = generatorB _
        rw [generatorB_eq_table]
        exact hg p
      rw [← he]
      exact word_mem _ _ (fun i => gGenerator_mem j i P hS hj) _
    have ha : a ∈ P := by
      have hs : sGenerator 1 ∈ P := hS (subset_closure ⟨1,rfl⟩)
      have he : sGenerator 1 = a := by
        apply inclusion_injective
        rw [sGenerator_inclusion]
        change SylowData.sGenTable 1 = generatorA
        rw [generatorA_eq_table]
        apply Equiv.ext
        decide +kernel
      exact he ▸ hs
    have hgen : closure (Set.range FirstFusion.letter) ≤ P := by
      apply (closure_le P).mpr
      rintro _ ⟨i,rfl⟩
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact P.inv_mem hb
    exact (hP (top_le_iff.mp (FirstFusion.letter_generates ▸ hgen))).elim

/-- Every proper overgroup of the literal full Sylow lies in one of the two locals. -/
theorem proper_overgroup_le (P : Subgroup Carrier) (hS : s ≤ P) (hP : P ≠ ⊤) :
    P ≤ l₁ ∨ P ≤ p₂ := by
  apply SubgroupClass.subset_union.mp
  intro x hx
  obtain ⟨j,u,v,he⟩ := double_coset_cover x
  have hj : dRep j ∈ P := by
    have hm := P.mul_mem (P.mul_mem (P.inv_mem (hS u.property)) hx)
      (P.inv_mem (hS v.property))
    rw [he] at hm
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel,mul_one] using hm
  rcases representative_mem P hS hP j hj with h | h
  · exact Or.inl (he ▸ l₁.mul_mem (l₁.mul_mem (SecondParabolic.s_le_l₁ u.property) h)
      (SecondParabolic.s_le_l₁ v.property))
  · have hsp : s ≤ p₂ := s_le_candidate.trans candidate_le_p₂
    exact Or.inr (he ▸ p₂.mul_mem (p₂.mul_mem (hsp u.property) h) (hsp v.property))

end Sporadic.LeechRelated.J2.SylowOvergroups
