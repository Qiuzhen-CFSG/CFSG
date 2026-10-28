module
public import Theory.SpecificGroups.PSL3Two.Parabolics.WreathPair
public import Theory.SpecificGroups.PSL3Two.BorelCenterNormalizer

/-!
# The complete Sylow interval in the actual paired actor

The independent coordinate Borels and the interchange force an overgroup
to be a coordinate subgroup. Its one-coordinate subgroup contains the
binary Borel, whose only overgroups are the two parabolics and the whole
factor. All three proper possibilities are self-normalizing. Thus the
paired actor has exactly its two original parabolics strictly between the
marked Sylow and the whole group.
-/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Two.WreathPair

private def single (i : Bit) : SL →* Actor where
  toFun x := ⟨Pi.mulSingle i x,1⟩
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext k
    · by_cases hk : k = i <;> simp [Pi.mulSingle_apply,hk]
    · simp

private theorem conjugate_single (w : Actor) (i : Bit) (x : SL) :
    w * single i x * w⁻¹ =
      single (w.right * i) (w.left (w.right * i) * x * (w.left (w.right * i))⁻¹) := by
  apply RegularWreathProduct.ext
  · funext k
    by_cases hk : k = w.right * i
    · subst k
      simp [single,Pi.mulSingle_apply,mul_assoc]
    · have hk' : w.right⁻¹ * k ≠ i := by
        intro he
        apply hk
        rw [←he,mul_inv_cancel_left]
      simp [single,Pi.mulSingle_apply,hk,hk',mul_assoc]
  · simp [single]

private theorem shift_mem (H : Subgroup Actor) (hBH : borel ≤ H) (i : Bit) :
    (RegularWreathProduct.inl i : Actor) ∈ H := hBH (fun _ => one_mem _)

private theorem single_mem_iff (H : Subgroup Actor) (hBH : borel ≤ H) (i : Bit) (x : SL) :
    single i x ∈ H ↔ single 1 x ∈ H := by
  constructor
  · intro hx
    have hi := shift_mem H hBH i⁻¹
    have hh := H.mul_mem (H.mul_mem hi hx) (H.inv_mem hi)
    rw [conjugate_single] at hh
    simpa using hh
  · intro hx
    have hi := shift_mem H hBH i
    have hh := H.mul_mem (H.mul_mem hi hx) (H.inv_mem hi)
    rw [conjugate_single] at hh
    simpa using hh

private theorem factor_interval (K : Subgroup SL) (hBK : borelSL ≤ K) :
    K = borelSL ∨ K = pointParabolicSL ∨ K = lineParabolicSL ∨ K = ⊤ := by
  by_cases ht : K = ⊤
  · exact Or.inr (Or.inr (Or.inr ht))
  have step (P : Subgroup SL) (hP : Nat.card P = 24) (hKP : K ≤ P) :
      K = borelSL ∨ K = P := by
    have h8 : 8 ∣ Nat.card K := card_borelSL ▸ card_dvd_of_le hBK
    have hd : Nat.card K ∣ 24 := hP ▸ card_dvd_of_le hKP
    have hb := Nat.le_of_dvd (by decide : 0 < 24) hd
    have hp := Nat.card_pos (α := K)
    have hn : Nat.card K ≠ 16 := by intro he; rw [he] at hd; norm_num at hd
    have hc : Nat.card K = 8 ∨ Nat.card K = 24 := by omega
    rcases hc with hc | hc
    · exact Or.inl (eq_of_le_of_card_ge hBK (by rw [hc,card_borelSL])).symm
    · exact Or.inr (eq_of_le_of_card_ge hKP (by rw [hc,hP]))
  rcases overgroup_borelSL K hBK ht with hp | hl
  · rcases step _ card_pointParabolicSL hp with he | he
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
  · rcases step _ card_lineParabolicSL hl with he | he
    · exact Or.inl he
    · exact Or.inr (Or.inr (Or.inl he))

/-- Every overgroup of the marked full Sylow is the Sylow itself, one of
the two original coordinate parabolics, or the whole paired actor. -/
theorem overgroup_borel (H : Subgroup Actor) (hBH : borel ≤ H) :
    H = borel ∨ H = point ∨ H = line ∨ H = ⊤ := by
  let K := H.comap (single 1)
  have hBK : borelSL ≤ K := by
    intro x hx
    apply hBH
    intro i
    change (Pi.mulSingle 1 x : Bit → SL) i ∈ borelSL
    by_cases hi : i = 1 <;> simp [hi,hx]
  have hsingle (i : Bit) {x : SL} (hx : x ∈ K) : single i x ∈ H :=
    (single_mem_iff H hBH i x).mpr hx
  have hcoord : RegularWreathProduct.coordinateSubgroup (Q := Bit) K ≤ H := by
    intro w hw
    let b : (Bit → SL) →* Actor := {
      toFun := fun v => ⟨v,1⟩
      map_one' := rfl
      map_mul' := fun v z => by ext <;> simp }
    have hb : b w.left ∈ H :=
      Subgroup.pi_mem_of_mulSingle_mem (H := H.comap b) w.left
        (fun i => hsingle i (hw i))
    have hh := H.mul_mem hb (shift_mem H hBH w.right)
    convert hh using 1
    ext <;> simp [b]
  have hnorm : H ≤ RegularWreathProduct.coordinateSubgroup (Q := Bit)
      (normalizer (K : Set SL)) := by
    intro w hw i
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      have hh := H.mul_mem (H.mul_mem hw (hsingle (w.right⁻¹ * i) hx)) (H.inv_mem hw)
      rw [conjugate_single] at hh
      apply (single_mem_iff H hBH i _).mp
      change single i (w.left i * x * (w.left i)⁻¹) ∈ H
      simpa only [mul_inv_cancel_left] using hh
    · rw [card_map_of_injective (MulAut.conj (w.left i)).injective]
  have heq (hK : normalizer (K : Set SL) = K) :
      H = RegularWreathProduct.coordinateSubgroup (Q := Bit) K := by
    rw [hK] at hnorm
    exact le_antisymm hnorm hcoord
  rcases factor_interval K hBK with hk | hk | hk | hk
  · exact Or.inl (by
      rw [heq (hk ▸ BorelCenterNormalizer.normalizer_borel),hk]
      rfl)
  · exact Or.inr (Or.inl (by
      rw [heq (hk ▸ pointParabolicSL_normalizer),hk]
      rfl))
  · have hn : normalizer (lineParabolicSL : Set SL) = lineParabolicSL := by
      rw [←MarkedAutomorphisms.pointParabolic_map_diagram,
        ←map_equiv_normalizer_eq,pointParabolicSL_normalizer]
    exact Or.inr (Or.inr (Or.inl (by rw [heq (hk ▸ hn),hk]; rfl)))
  · exact Or.inr (Or.inr (Or.inr (top_unique (by
      intro w _
      apply hcoord
      intro i
      rw [hk]
      trivial))))

end Matrix.PSL3Two.WreathPair
