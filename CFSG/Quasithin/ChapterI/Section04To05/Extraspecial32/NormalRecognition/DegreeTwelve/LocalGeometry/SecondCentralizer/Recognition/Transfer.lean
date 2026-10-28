module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.Recognition.Kernel
public import Theory.GroupTheory.InvolutionTransfer

/-!
# The two transfers in the second involution centralizer

The local C₂ × S₄ has odd index in the literal centralizer of t. Transfer of
its first-coordinate character splits off the distinguished central involution.
Every binary character on S₄ kills A₄. Correcting the S₄ embedding by the first
character therefore fixes its literal A₄ and replaces each reflection r, when
necessary, by rt.

Inside the first kernel, the adjusted S₄ again has odd index. Its sign character
transfers nontrivially: a reflection cannot fuse with an even involution because
`LocalSeed.first` separates them in the ambient group. The second kernel meets
the adjusted S₄ in precisely A₄. Centrality of the split C₂ factor makes this
kernel normal in the whole centralizer, and the two indices multiply to four.
The correction fixes A₄, giving the required intersection with the original,
unadjusted local model.

Only the seed is needed: its exact first-class marking already contains the
fusion separation used here. Thus these results apply under all the original
involution and two-class hypotheses without additional transfer assumptions.
The final theorem applies the constructed kernel to the existing recognition
of A₄ or A₅ and its literal Sylow four-group.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemma 4.2, printed p.39.
-/

@[expose] public section
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
open Subgroup Equiv Equiv.Perm
private abbrev C2 := Multiplicative (ZMod 2)

private theorem binary_index {H A : Type*} [Group H] [Group A] [Finite A]
    (f : H →* A) (hA : Nat.card A = 2) (x : H) (hx : f x ≠ 1) :
    f.ker.index = 2 := by
  have hd : f.ker.index ∣ 2 := by
    rw [index_ker]
    simpa only [hA] using card_subgroup_dvd_card f.range
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact (hx (show x ∈ f.ker from index_eq_one.mp h ▸ mem_top x)).elim
  · exact h

private theorem binary_even {A : Type*} [Group A] [Finite A]
    (f : Perm (Fin 4) →* A) (hA : Nat.card A = 2)
    (x : Perm (Fin 4)) (hx : sign x = 1) : f x = 1 := by
  apply alternatingGroup_le_of_index_le_two (G := f.ker) _ (mem_alternatingGroup.mpr hx)
  rw [index_ker]
  rw [← hA]
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

private theorem binary_pow {A : Type*} [Group A] [Finite A]
    (hA : Nat.card A = 2) (a : A) {n : ℕ} (hn : Odd n) : a ^ n = a := by
  have hm : n % 2 = 1 := Nat.odd_iff.mp hn
  simpa only [hA, hm, pow_one] using (pow_mod_natCard a n).symm

private theorem odd_transfer_involution {H A : Type*} [Group H] [Finite H]
    [CommGroup A] [Finite A] (L : Subgroup H) (hL : Odd L.index)
    (f : L →* A) (hA : Nat.card A = 2) (w : L) (hw : orderOf w = 2)
    (hf : ∀ y : L, IsConj (w : H) (y : H) → f y = f w) :
    f.transfer (w : H) = f w := by
  rw [f.transfer_apply_eq_pow_of_conjugate_powers w, binary_pow hA _ hL]
  intro n y hy
  have hr : w ^ n = w ^ (n % 2) := by
    simpa only [hw] using (pow_mod_orderOf w n).symm
  rw [hr] at hy ⊢
  have hb : n % 2 < 2 := Nat.mod_lt _ (by decide)
  generalize n % 2 = r at hy ⊢ hb
  interval_cases r
  · have he : y = 1 := Subtype.coe_injective (isConj_one_right.mp (by simpa using hy))
    simp [he]
  · simpa only [pow_one] using hf y (by simpa using hy)

variable {G : Type*} [Group G] {z t : G}

private theorem local_central (s : LocalSeed z t) (a : C2) :
    s.embed (a, 1) ∈ center (Centralizer t) := by
  have ha : a = 1 ∨ a = Multiplicative.ofAdd 1 :=
    (by decide : ∀ b : C2, b = 1 ∨ b = Multiplicative.ofAdd 1) a
  rcases ha with rfl | rfl
  · change s.embed 1 ∈ _
    rw [map_one]
    exact (center _).one_mem
  · rw [show (Multiplicative.ofAdd 1, (1 : Perm (Fin 4))) = centralInvolution 4 from rfl,
      s.central]
    apply mem_center_iff.mpr
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.mp g.property)

/-- The first transfer splits the specified central involution. -/
private theorem exists_first_character [Finite G] (s : LocalSeed z t) :
    ∃ χ : Centralizer t →* C2, ∀ a : C2, χ (s.embed (a, 1)) = a := by
  classical
  let e := MonoidHom.ofInjective s.injective
  let f : s.embed.range →* C2 := (MonoidHom.fst _ _).comp e.symm.toMonoidHom
  refine ⟨f.transfer, ?_⟩
  intro a
  let w : s.embed.range := e (a, 1)
  have hw : f w = a := by simp [f, w]
  change f.transfer (w : Centralizer t) = a
  rw [f.transfer_apply_eq_pow_of_conjugate_powers w, hw,
    binary_pow (by simp [C2, Nat.card_eq_fintype_card]) _ s.range_index_odd]
  intro n y hy
  have hc : ((w : Centralizer t) ^ n) ∈ center (Centralizer t) :=
    (center _).pow_mem (local_central s a) n
  have he : w ^ n = y := Subtype.ext (hy.eq_of_left_mem_center hc)
  rw [he]

private theorem character_coordinates (s : LocalSeed z t) (χ : Centralizer t →* C2)
    (hχ : ∀ a : C2, χ (s.embed (a, 1)) = a) (x : Model 4) :
    χ (s.embed x) = x.1 * χ (s.embed (1, x.2)) := by
  have he : x = (x.1, 1) * (1, x.2) := by ext <;> simp
  conv_lhs => rw [he, map_mul, map_mul, hχ]

private theorem character_even (s : LocalSeed z t) (χ : Centralizer t →* C2)
    (hχ : ∀ a : C2, χ (s.embed (a, 1)) = a) (x : Model 4)
    (hx : sign x.2 = 1) : χ (s.embed x) = x.1 := by
  rw [character_coordinates s χ hχ]
  have he := binary_even (χ.comp (s.embed.comp (MonoidHom.inr _ _)))
    (by simp [C2, Nat.card_eq_fintype_card]) x.2 hx
  change χ (s.embed (1, x.2)) = 1 at he
  rw [he, mul_one]

/-- The local S₄ adjusted by the first character; it fixes the literal A₄. -/
private def correctedLocal (s : LocalSeed z t) (χ : Centralizer t →* C2)
    (hχ : ∀ a : C2, χ (s.embed (a, 1)) = a) : Perm (Fin 4) →* χ.ker :=
  let p := χ.comp (s.embed.comp (MonoidHom.inr C2 (Perm (Fin 4))))
  let j : Perm (Fin 4) →* Model 4 := p⁻¹.prod (MonoidHom.id _)
  (s.embed.comp j).codRestrict χ.ker (fun σ => by
    change χ (s.embed ((χ (s.embed (1, σ)))⁻¹, σ)) = 1
    rw [character_coordinates s χ hχ]
    exact inv_mul_cancel _)

private theorem correctedLocal_coe (s : LocalSeed z t) (χ : Centralizer t →* C2)
    (hχ : ∀ a : C2, χ (s.embed (a, 1)) = a) (σ : Perm (Fin 4)) :
    (correctedLocal s χ hχ σ : Centralizer t) =
      s.embed ((χ (s.embed (1, σ)))⁻¹, σ) := rfl

private theorem correctedLocal_injective (s : LocalSeed z t) (χ : Centralizer t →* C2)
    (hχ : ∀ a : C2, χ (s.embed (a, 1)) = a) :
    Function.Injective (correctedLocal s χ hχ) := by
  intro a b h
  exact congrArg Prod.snd (s.injective (congrArg Subtype.val h))

private theorem correctedLocal_even (s : LocalSeed z t) (χ : Centralizer t →* C2)
    (hχ : ∀ a : C2, χ (s.embed (a, 1)) = a)
    (σ : Perm (Fin 4)) (hσ : sign σ = 1) :
    (correctedLocal s χ hχ σ : Centralizer t) = s.embed (1, σ) := by
  rw [correctedLocal_coe, character_even s χ hχ (1, σ) hσ]
  simp only [inv_one]

private theorem correctedLocal_of_mem (s : LocalSeed z t) (χ : Centralizer t →* C2)
    (hχ : ∀ a : C2, χ (s.embed (a, 1)) = a)
    (x : Model 4) (hx : s.embed x ∈ χ.ker) :
    (correctedLocal s χ hχ x.2 : Centralizer t) = s.embed x := by
  have he : χ (s.embed x) = 1 := hx
  rw [character_coordinates s χ hχ] at he
  rw [correctedLocal_coe]
  congr 1
  exact Prod.ext (eq_inv_of_mul_eq_one_left he).symm rfl

private theorem first_index (s : LocalSeed z t) (χ : Centralizer t →* C2)
    (hχ : ∀ a : C2, χ (s.embed (a, 1)) = a) : χ.ker.index = 2 := by
  apply binary_index χ (by simp [C2, Nat.card_eq_fintype_card])
    (s.embed (Multiplicative.ofAdd 1, 1))
  rw [hχ]
  decide

private theorem correctedLocal_index [Finite G] (s : LocalSeed z t) (χ : Centralizer t →* C2)
    (hχ : ∀ a : C2, χ (s.embed (a, 1)) = a) :
    (correctedLocal s χ hχ).range.index = s.embed.range.index := by
  have hcard : Nat.card (correctedLocal s χ hχ).range = 24 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective
      (correctedLocal_injective s χ hχ)).toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hI := s.embed.range.card_mul_index
  rw [s.range_card] at hI
  have hH := χ.ker.card_mul_index
  rw [first_index s χ hχ] at hH
  have hL := (correctedLocal s χ hχ).range.card_mul_index
  rw [hcard] at hL
  nlinarith

private theorem correctedLocal_first (s : LocalSeed z t) (χ : Centralizer t →* C2)
    (hχ : ∀ a : C2, χ (s.embed (a, 1)) = a)
    (σ : Perm (Fin 4)) (hσ : orderOf σ = 2) :
    IsConj z ((correctedLocal s χ hχ σ : Centralizer t) : G) ↔ sign σ = 1 := by
  constructor
  · intro h
    exact ((s.first _).mp h).2.2
  · intro hs
    rw [correctedLocal_even s χ hχ σ hs]
    apply (s.first _).mpr
    refine ⟨?_, rfl, hs⟩
    exact (orderOf_injective (MonoidHom.inr C2 (Perm (Fin 4)))
      (fun _ _ h => congrArg Prod.snd h) σ).trans hσ

/-- The second transfer detects a reflection in the adjusted local S₄. -/
private theorem exists_second_character [Finite G] (s : LocalSeed z t) (χ : Centralizer t →* C2)
    (hχ : ∀ a : C2, χ (s.embed (a, 1)) = a) :
    ∃ ψ : χ.ker →* ℤˣ, ψ.ker.index = 2 ∧
      ∀ σ : Perm (Fin 4), ψ (correctedLocal s χ hχ σ) = 1 ↔ sign σ = 1 := by
  classical
  let j := correctedLocal s χ hχ
  let e := MonoidHom.ofInjective (correctedLocal_injective s χ hχ)
  let f : j.range →* ℤˣ := sign.comp e.symm.toMonoidHom
  let r : Perm (Fin 4) := swap 0 1
  have hr : orderOf r = 2 := by
    apply orderOf_eq_prime_iff.mpr
    decide
  have hrs : sign r = -1 := sign_swap (by decide : (0 : Fin 4) ≠ 1)
  let w : j.range := e r
  have hw : orderOf w = 2 := (e.orderOf_eq r).trans hr
  have hf (σ : Perm (Fin 4)) : f (e σ) = sign σ := by simp [f]
  have htrans : f.transfer (j r) = -1 := by
    change f.transfer (w : χ.ker) = -1
    rw [odd_transfer_involution j.range
      (by rw [correctedLocal_index]; exact s.range_index_odd) f
      (by simp [Nat.card_eq_fintype_card]) w hw, hf r, hrs]
    intro y hy
    obtain ⟨σ, rfl⟩ := e.surjective y
    change IsConj (j r) (j σ) at hy
    have hσ : orderOf σ = 2 :=
      (orderOf_injective j (correctedLocal_injective s χ hχ) σ).symm.trans
        ((conjugate_order hy).symm.trans
          ((orderOf_injective j (correctedLocal_injective s χ hχ) r).trans hr))
    have hc : IsConj ((j r : Centralizer t) : G) ((j σ : Centralizer t) : G) :=
      ((Centralizer t).subtype.comp χ.ker.subtype).map_isConj hy
    have hne : sign σ ≠ 1 := by
      intro hs
      have hfirst := (correctedLocal_first s χ hχ σ hσ).mpr hs
      have he := (correctedLocal_first s χ hχ r hr).mp (hfirst.trans hc.symm)
      rw [hrs] at he
      exact (by decide : (-1 : ℤˣ) ≠ 1) he
    rw [hf σ, hf r, hrs]
    exact (Int.units_eq_one_or (sign σ)).resolve_left hne
  have hnontriv : f.transfer (j r) ≠ 1 := by
    rw [htrans]
    decide
  have hi := binary_index f.transfer (by simp [Nat.card_eq_fintype_card]) (j r) hnontriv
  have hlocal : (f.transfer.comp j).ker = alternatingGroup (Fin 4) :=
    eq_alternatingGroup_of_index_eq_two
      (binary_index (f.transfer.comp j) (by simp [Nat.card_eq_fintype_card]) r hnontriv)
  refine ⟨f.transfer, hi, ?_⟩
  intro σ
  change σ ∈ (f.transfer.comp j).ker ↔ _
  rw [hlocal, mem_alternatingGroup]

private theorem second_kernel_normal (s : LocalSeed z t) (χ : Centralizer t →* C2)
    (hχ : ∀ a : C2, χ (s.embed (a, 1)) = a) (ψ : χ.ker →* ℤˣ) :
    (ψ.ker.map χ.ker.subtype).Normal := by
  constructor
  rintro x ⟨k, hk, rfl⟩ g
  let c := s.embed (χ g, 1)
  have hc : c ∈ center (Centralizer t) := local_central s (χ g)
  have hh : c⁻¹ * g ∈ χ.ker := by
    change χ (c⁻¹ * g) = 1
    rw [map_mul, map_inv, show χ c = χ g from hχ (χ g), inv_mul_cancel]
  let h : χ.ker := ⟨c⁻¹ * g, hh⟩
  refine ⟨h * k * h⁻¹, (inferInstance : ψ.ker.Normal).conj_mem k hk h, ?_⟩
  change (c⁻¹ * g) * (k : Centralizer t) * (c⁻¹ * g)⁻¹ =
    g * (k : Centralizer t) * g⁻¹
  calc
    _ = c⁻¹ * (g * (k : Centralizer t) * g⁻¹) * c := by group
    _ = _ := by
      rw [mul_assoc, mem_center_iff.mp hc _, inv_mul_cancel_left]

/-- The two transfer kernels have index four in the whole centralizer, and their
intersection with the original local model is exactly its literal A₄. -/
theorem nonempty_transferKernel [Finite G] (s : LocalSeed z t) :
    Nonempty (TransferKernel s) := by
  obtain ⟨χ, hχ⟩ := exists_first_character s
  obtain ⟨ψ, hψindex, hψ⟩ := exists_second_character s χ hχ
  refine ⟨{
    K := ψ.ker.map χ.ker.subtype
    normal := second_kernel_normal s χ hχ ψ
    index := by rw [index_map_subtype, hψindex, first_index s χ hχ]
    local_mem := ?_
  }⟩
  intro x
  constructor
  · rintro ⟨u, hu, heu⟩
    have hx : s.embed x ∈ χ.ker := heu ▸ u.property
    have he : correctedLocal s χ hχ x.2 = u :=
      Subtype.ext ((correctedLocal_of_mem s χ hχ x hx).trans heu.symm)
    have hs : sign x.2 = 1 := (hψ x.2).mp (he.symm ▸ hu)
    exact ⟨(character_even s χ hχ x hs).symm.trans hx, hs⟩
  · rintro ⟨hx, hs⟩
    have hm : s.embed x ∈ χ.ker := (character_even s χ hχ x hs).trans hx
    exact ⟨correctedLocal s χ hχ x.2, (hψ x.2).mpr hs,
      correctedLocal_of_mem s χ hχ x hm⟩

/-- Applying the constructed kernel to the existing involution-centralizer
recognition gives A₄ or A₅, with the source's actual Sylow four-group. -/
theorem exists_recognized_transferKernel [Finite G] (s : LocalSeed z t) :
    ∃ d : TransferKernel s,
      (Nonempty (d.K ≃* alternatingGroup (Fin 4)) ∨
        Nonempty (d.K ≃* alternatingGroup (Fin 5))) ∧
      centralizer ({d.evenMap evenInvolution} : Set d.K) = d.fourGroup ∧
      IsKleinFour d.fourGroup ∧
      ∃ S : Sylow 2 d.K, (S : Subgroup d.K) = d.fourGroup := by
  obtain ⟨d⟩ := nonempty_transferKernel s
  exact ⟨d, d.alternating_four_or_five, d.centralizer_eq_fourGroup,
    d.fourGroup_isKleinFour, d.fourGroup_isSylow⟩

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
end
