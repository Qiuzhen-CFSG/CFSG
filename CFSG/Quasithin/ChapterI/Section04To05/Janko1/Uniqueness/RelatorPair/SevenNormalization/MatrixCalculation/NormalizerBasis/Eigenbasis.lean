module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.MatrixCalculation.NormalizerBasis.SylowWeights
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.MatrixCalculation.NormalizerBasis.CharacterFrame
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A cyclic eigenbasis from the marked Sylow characters

Starting from an explicit marking of the seven nontrivial characters, the
seven-generator propagates one occurring character around the whole marking.
The seven independent spaces saturate the dimension bound and are all lines.
The cubic element stabilizes the character at index four. Its scalar there is
one, since GF(11) has no nontrivial cube root of one. A vector on that line and
its seven translates then form a basis with the literal x, u, y actions.

The only extra premise is `NormalizerCharacterFrame`. Its construction from
the source local data is a separate obligation; no representation-theoretic
premise such as irreducibility or character multiplicities is assumed.

Source: Gorenstein, *Finite Groups*, §16.6, pp.482–483, the basis choice before
the matrix calculation (6.1)–(6.2).
-/

open Module

namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation

variable {G : Type*} [Group G] [Finite G] {h : Janko1CentralizerData G}

private theorem conjugate_weight_mem (ρ : G →* Janko1.Ambient)
    (g : Subgroup.normalizer (h.sylow : Set G))
    (χ ψ : h.sylow →* (ZMod 11)ˣ)
    (he : ∀ s, ψ s = χ (((h.sylow : Subgroup G).normalizerMonoidHom g).symm s))
    {v : Fin 7 → ZMod 11} (hv : v ∈ (sylowRepresentation h ρ).characterWeightSpace χ) :
    vectorRepresentation ρ g v ∈ (sylowRepresentation h ρ).characterWeightSpace ψ := by
  simp only [Representation.characterWeightSpace, Submodule.mem_iInf,
    Module.End.mem_eigenspace_iff] at hv ⊢
  intro s
  have hc : (s : G) * g = g *
      (((h.sylow : Subgroup G).normalizerMonoidHom g).symm s : h.sylow) := by
    have heq := congrArg (fun z : h.sylow => (z : G))
      (((h.sylow : Subgroup G).normalizerMonoidHom g).apply_symm_apply s)
    change (g : G) * _ * (g : G)⁻¹ = s at heq
    rw [← heq]
    group
  change vectorRepresentation ρ (s : G) (vectorRepresentation ρ g v) =
    (ψ s : ZMod 11) • vectorRepresentation ρ g v
  rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
  have hv' := hv (((h.sylow : Subgroup G).normalizerMonoidHom g).symm s)
  change vectorRepresentation ρ
    ((((h.sylow : Subgroup G).normalizerMonoidHom g).symm s : h.sylow) : G) v =
      (χ (((h.sylow : Subgroup G).normalizerMonoidHom g).symm s) : ZMod 11) • v at hv'
  rw [hv']
  rw [map_smul, he]

omit [Finite G] in
private theorem representation_map_ne_zero (ρ : G →* Janko1.Ambient)
    (g : G) {v : Fin 7 → ZMod 11} (hv : v ≠ 0) : vectorRepresentation ρ g v ≠ 0 := by
  intro he
  have he' := congrArg (vectorRepresentation ρ g⁻¹) he
  rw [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at he'
  exact hv he'

private theorem seven_predicate (P : Fin 7 → Prop) (hs : ∀ i, P i → P (i - 1))
    (he : ∃ i, P i) : ∀ i, P i := by
  obtain ⟨i, h0⟩ := he
  have h1 := hs _ h0
  have h2 := hs _ h1
  have h3 := hs _ h2
  have h4 := hs _ h3
  have h5 := hs _ h4
  have h6 := hs _ h5
  intro j
  fin_cases i <;> fin_cases j <;>
    first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6

public theorem characterFrame_occurs (D : NormalizerFrame h) (C : NormalizerCharacterFrame D)
    (ρ : G →* Janko1.Ambient) (hρ : Function.Injective ρ) (i : Fin 7) :
    (sylowRepresentation h ρ).characterWeightSpace (C.character i) ≠ ⊥ := by
  apply seven_predicate (fun i =>
    (sylowRepresentation h ρ).characterWeightSpace (C.character i) ≠ ⊥) _ _ i
  · intro j hj
    obtain ⟨v, hv, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hj
    apply (Submodule.ne_bot_iff _).mpr
    refine ⟨vectorRepresentation ρ (orientedY D C.reverse) v, ?_,
      representation_map_ne_zero ρ _ hn⟩
    exact conjugate_weight_mem ρ
      ⟨orientedY D C.reverse, D.H_le (orientedY_mem D C.reverse)⟩ _ _ (C.y_action j) hv
  · obtain ⟨χ, hn⟩ := exists_nontrivial_sylow_weight h ρ hρ
    obtain ⟨j, hj⟩ := C.exhaustive χ.val hn
    exact ⟨j, hj.symm ▸ χ.property⟩

public theorem characterFrame_weight_card (D : NormalizerFrame h) (C : NormalizerCharacterFrame D)
    (ρ : G →* Janko1.Ambient) (hρ : Function.Injective ρ) :
    Nat.card (sylowRepresentation h ρ).CharacterWeight = 7 := by
  let f : Fin 7 → (sylowRepresentation h ρ).CharacterWeight :=
    fun i => ⟨C.character i, characterFrame_occurs D C ρ hρ i⟩
  have hf : Function.Injective f := fun i j he => C.injective (congrArg Subtype.val he)
  obtain ⟨hfinit, hle⟩ := sylow_weight_card_le_seven h ρ
  let := hfinit
  have hh := Nat.card_le_card_of_injective f hf
  exact Nat.le_antisymm hle (by simpa only [Nat.card_fin] using hh)

public theorem characterFrame_line (D : NormalizerFrame h) (C : NormalizerCharacterFrame D)
    (ρ : G →* Janko1.Ambient) (hρ : Function.Injective ρ) (i : Fin 7) :
    Module.finrank (ZMod 11) ((sylowRepresentation h ρ).characterWeightSpace (C.character i)) = 1 := by
  let := h.sylow_elementaryAbelian
  exact Representation.characterWeight_finrank_one_of_involutive_card_eq
    (sylowRepresentation h ρ) h.sylow_square
    (by decide) (by rw [h.sylow_card]; decide)
    (by simpa using characterFrame_weight_card D C ρ hρ)
    ⟨C.character i, characterFrame_occurs D C ρ hρ i⟩

private theorem cubic_scalar (a : ZMod 11) (ha : a ^ 3 = 1) : a = 1 := by
  have ht : ∀ a : ZMod 11, a ^ 3 = 1 → a = 1 := by decide +kernel
  exact ht a ha

public theorem characterFrame_fixed_vector (D : NormalizerFrame h) (C : NormalizerCharacterFrame D)
    (ρ : G →* Janko1.Ambient) (hρ : Function.Injective ρ)
    {v : Fin 7 → ZMod 11}
    (hv : v ∈ (sylowRepresentation h ρ).characterWeightSpace (C.character 4)) (hn : v ≠ 0) :
    vectorRepresentation ρ D.u v = v := by
  have hvu : vectorRepresentation ρ D.u v ∈
      (sylowRepresentation h ρ).characterWeightSpace (C.character 4) :=
    conjugate_weight_mem ρ ⟨D.u, D.H_le D.u_mem⟩ _ _ (C.u_action 4) hv
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
    (characterFrame_line D C ρ hρ 4)
    (show (⟨v, hv⟩ : (sylowRepresentation h ρ).characterWeightSpace (C.character 4)) ≠ 0
      from fun he => hn (congrArg Subtype.val he)) ⟨vectorRepresentation ρ D.u v, hvu⟩
  have ha' : vectorRepresentation ρ D.u v = a • v := (congrArg Subtype.val ha).symm
  have hp : (vectorRepresentation ρ D.u) ^ 3 = 1 := by
    rw [← map_pow, ← D.order_u, pow_orderOf_eq_one, map_one]
  have he : Module.End.HasEigenvector (vectorRepresentation ρ D.u) a v :=
    ⟨Module.End.mem_eigenspace_iff.mpr ha', hn⟩
  have hcube : a ^ 3 = 1 := by
    apply smul_left_injective (ZMod 11) hn
    simpa [hp] using (he.pow_apply 3).symm
  simpa [cubic_scalar a hcube] using ha'

private def cyclicVectors (Y : Module.End (ZMod 11) (Fin 7 → ZMod 11))
    (v : Fin 7 → ZMod 11) : Fin 7 → (Fin 7 → ZMod 11) :=
  ![(Y ^ 4) v, (Y ^ 3) v, (Y ^ 2) v, Y v, v, (Y ^ 6) v, (Y ^ 5) v]

private theorem cyclicVectors_y (Y : Module.End (ZMod 11) (Fin 7 → ZMod 11))
    (hY : Y ^ 7 = 1) (v : Fin 7 → ZMod 11) (i : Fin 7) :
    Y (cyclicVectors Y v i) = cyclicVectors Y v (i - 1) := by
  fin_cases i <;> dsimp [cyclicVectors] <;>
    simp only [← Module.End.mul_apply, ← pow_succ', hY, Module.End.one_apply, ← pow_two]

private theorem cyclicVectors_u (Y U : Module.End (ZMod 11) (Fin 7 → ZMod 11))
    (hY : Y ^ 7 = 1) (hUY : U * Y = Y ^ 2 * U)
    (v : Fin 7 → ZMod 11) (hv : U v = v) (i : Fin 7) :
    U (cyclicVectors Y v i) = cyclicVectors Y v (2 * i + 3) := by
  have hpow (n : ℕ) : U * Y ^ n = Y ^ (2 * n) * U := by
    simpa only [← pow_mul] using ((show SemiconjBy U Y (Y ^ 2) from hUY).pow_right n).eq
  have happ (n : ℕ) : U ((Y ^ n) v) = (Y ^ (2 * n)) v := by
    rw [← Module.End.mul_apply, hpow, Module.End.mul_apply, hv]
  have h8 : Y ^ 8 = Y := by rw [show 8 = 7 + 1 from rfl, pow_add, hY]; simp
  have h10 : Y ^ 10 = Y ^ 3 := by rw [show 10 = 7 + 3 from rfl, pow_add, hY, one_mul]
  have h12 : Y ^ 12 = Y ^ 5 := by rw [show 12 = 7 + 5 from rfl, pow_add, hY, one_mul]
  fin_cases i <;> dsimp [cyclicVectors] <;> try simp only [happ, hv, h8, h10, h12]
  · change U (Y v) = (Y ^ 2) v
    simpa using happ 1

public theorem characterFrame_basis (D : NormalizerFrame h) (C : NormalizerCharacterFrame D)
    (ρ : G →* Janko1.Ambient) (hρ : Function.Injective ρ) :
    ∃ b : Basis (Fin 7) (ZMod 11) (Fin 7 → ZMod 11),
      (∀ i, vectorRepresentation ρ D.x (b i) = normalX i i • b i) ∧
      (∀ i, vectorRepresentation ρ D.u (b i) = b (2 * i + 3)) ∧
      (∀ i, vectorRepresentation ρ (orientedY D C.reverse) (b i) = b (i - 1)) := by
  classical
  have hy7 := orientedY_pow_seven D C.reverse
  have huy := orientedY_action D C.reverse
  let σ := vectorRepresentation ρ
  let y := orientedY D C.reverse
  let Y := σ y
  have hY : Y ^ 7 = 1 := by change σ y ^ 7 = 1; rw [← map_pow, hy7, map_one]
  have hUY : σ D.u * Y = Y ^ 2 * σ D.u := by
    have hh : D.u * y = y ^ 2 * D.u := mul_inv_eq_iff_eq_mul.mp huy
    simpa only [map_mul, map_pow] using congrArg σ hh
  obtain ⟨v, hv, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (characterFrame_occurs D C ρ hρ 4)
  let vs := cyclicVectors Y v
  have hvsY (i : Fin 7) : σ y (vs i) = vs (i - 1) := cyclicVectors_y Y hY v i
  have hvsU (i : Fin 7) : σ D.u (vs i) = vs (2 * i + 3) :=
    cyclicVectors_u Y (σ D.u) hY hUY v (characterFrame_fixed_vector D C ρ hρ hv hn) i
  have hvs (i : Fin 7) : vs i ∈
      (sylowRepresentation h ρ).characterWeightSpace (C.character i) := by
    apply seven_predicate (fun i => vs i ∈
      (sylowRepresentation h ρ).characterWeightSpace (C.character i)) _ ⟨4, hv⟩ i
    intro j hj
    rw [← hvsY]
    exact conjugate_weight_mem ρ ⟨y, D.H_le (orientedY_mem D C.reverse)⟩ _ _
      (C.y_action j) hj
  have hnvs (i : Fin 7) : vs i ≠ 0 := by
    have hp (n : ℕ) : (Y ^ n) v ≠ 0 := by
      change (σ y ^ n) v ≠ 0
      rw [← map_pow]
      exact representation_map_ne_zero ρ _ hn
    fin_cases i
    · exact hp 4
    · exact hp 3
    · exact hp 2
    · change Y v ≠ 0
      simpa only [pow_one] using hp 1
    · exact hn
    · exact hp 6
    · exact hp 5
  let := h.sylow_elementaryAbelian
  have hind := ((sylowRepresentation h ρ).characterWeightSpace_independent
    (by rw [h.sylow_card]; decide)).comp C.injective
  have hli : LinearIndependent (ZMod 11) vs := hind.linearIndependent _ hvs hnvs
  let b := basisOfLinearIndependentOfCardEqFinrank' vs hli (by simp)
  have hb (i : Fin 7) : b i = vs i := by
    exact congr_fun (coe_basisOfLinearIndependentOfCardEqFinrank' vs hli _) i
  refine ⟨b, ?_, ?_, ?_⟩
  · intro i
    rw [hb]
    have hh := hvs i
    simp only [Representation.characterWeightSpace, Submodule.mem_iInf,
      Module.End.mem_eigenspace_iff] at hh
    have hhx := hh ⟨D.x, D.x_mem⟩
    change vectorRepresentation ρ D.x (vs i) =
      (C.character i ⟨D.x, D.x_mem⟩ : ZMod 11) • vs i at hhx
    rw [C.x_value] at hhx
    exact hhx
  · intro i
    simpa only [hb] using hvsU i
  · intro i
    simpa only [hb] using hvsY i

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation
