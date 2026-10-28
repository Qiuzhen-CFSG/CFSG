module

public import Theory.ElementaryAbelian.FivePlaneGeometry
public import Theory.SpecificGroups.GL2.FiveWreathSylow

/-!
# The unique pair of lines preserved by a Sylow two-action on the five-plane

A subgroup of order 32 in the automorphism group of an elementary abelian
five-plane preserves at most one unordered pair of distinct lines.
Sylow conjugacy puts its action in the monomial model. The square of the
diagonal matrix with entries 2 and 1 fixes just the two coordinate lines.
Every invariant two-element set is fixed pointwise by that square.
-/

open scoped IsMulCommutative Pointwise Matrix
namespace IsElementaryAbelian.FivePlaneGeometry
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩
private abbrev V := Multiplicative (Fin 2 → ZMod 5)
private abbrev GLFive := Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)

private def linearAut : ((Fin 2 → ZMod 5) ≃ₗ[ZMod 5] (Fin 2 → ZMod 5)) ≃* MulAut V :=
  { toFun := fun a => a.toAddEquiv.toMultiplicative
    invFun := fun a => { AddEquiv.toMultiplicative.symm a with
      map_smul' := ZMod.map_smul (AddEquiv.toMultiplicative.symm a) }
    left_inv := by intro a; ext; rfl
    right_inv := by intro a; ext; rfl
    map_mul' := by intro a b; ext; rfl }

private def glAut : GLFive ≃* MulAut V :=
  Matrix.GeneralLinearGroup.toLin.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 5) (Fin 2 → ZMod 5)).trans
      linearAut)

private def twoUnit : (ZMod 5)ˣ := ⟨2, 3, by decide, by decide⟩
private def diagonal : GLFive := Matrix.GeneralLinearGroup.diagonalPair (ZMod 5) (twoUnit, 1)
private def delta : MulAut V := glAut diagonal

private theorem delta_apply (x : V) :
    (delta x).toAdd = ![2 * x.toAdd 0, x.toAdd 1] := by
  funext i
  fin_cases i <;>
    simp [delta, glAut, linearAut, diagonal,
      Matrix.GeneralLinearGroup.diagonalPair_val, dotProduct,
      Fin.sum_univ_two, twoUnit]

private def coordinate (i : Fin 2) : V →* Multiplicative (ZMod 5) where
  toFun x := Multiplicative.ofAdd (x.toAdd i)
  map_one' := rfl
  map_mul' _ _ := rfl

private def axis (i : Fin 2) : Subgroup V := (coordinate i).ker

private theorem axis_card (i : Fin 2) : Nat.card (axis i) = 5 := by
  change Nat.card {x : V // x.toAdd i = 0} = 5
  fin_cases i <;> rw [Nat.card_eq_fintype_card] <;> decide +kernel

private theorem fixed_line_axis (L : Subgroup V) (hL : Nat.card L = 5)
    (hfix : L.map (delta ^ 2).toMonoidHom = L) : L = axis 0 ∨ L = axis 1 := by
  classical
  have : Nontrivial L := (Finite.one_lt_card_iff_nontrivial (α := L)).mp (by omega)
  obtain ⟨x, hx⟩ := exists_ne (1 : L)
  have hgen : Subgroup.zpowers (x : V) = L := by
    calc
      _ = (Subgroup.zpowers x).map L.subtype := (L.subtype.map_zpowers x).symm
      _ = (⊤ : Subgroup L).map L.subtype := congrArg (Subgroup.map L.subtype)
        (zpowers_eq_top_of_prime_card hL hx)
      _ = L := by
        ext v
        constructor
        · rintro ⟨w, _, rfl⟩; exact w.property
        · intro hv; exact ⟨⟨v, hv⟩, Subgroup.mem_top _, rfl⟩
  have hmem : (delta ^ 2) (x : V) ∈ Subgroup.zpowers (x : V) := by
    rw [hgen]
    exact hfix.le (Subgroup.mem_map_of_mem (delta ^ 2).toMonoidHom x.property)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have he0 := congrArg (fun y : V => y.toAdd 0) hn
  have he1 := congrArg (fun y : V => y.toAdd 1) hn
  have hsq (y : V) : ((delta ^ 2) y).toAdd = ![4 * y.toAdd 0, y.toAdd 1] := by
    change (delta (delta y)).toAdd = _
    rw [delta_apply, delta_apply]
    ext i
    fin_cases i
    · change 2 * (2 * y.toAdd 0) = 4 * y.toAdd 0
      ring
    · rfl
  rw [hsq] at he0 he1
  simp only [toAdd_zpow, Pi.smul_apply, zsmul_eq_mul, Matrix.cons_val_zero] at he0
  simp only [toAdd_zpow, Pi.smul_apply, zsmul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_zero] at he1
  have he1' : (n : ZMod 5) * (x : V).toAdd 1 = 1 * (x : V).toAdd 1 := by simpa using he1
  have hz : (x : V).toAdd 0 = 0 ∨ (x : V).toAdd 1 = 0 := by
    by_contra h
    push Not at h
    have h0 := mul_right_cancel₀ h.1 he0
    have h1 := mul_right_cancel₀ h.2 he1'
    have : (4 : ZMod 5) = 1 := h0.symm.trans h1
    exact (by decide : (4 : ZMod 5) ≠ 1) this
  rcases hz with hz | hz
  · left
    apply Subgroup.eq_of_le_of_card_ge
    · rw [← hgen]
      exact Subgroup.zpowers_le.mpr hz
    · rw [axis_card, hL]
  · right
    apply Subgroup.eq_of_le_of_card_ge
    · rw [← hgen]
      exact Subgroup.zpowers_le.mpr hz
    · rw [axis_card, hL]

private theorem square_fixes_pair {Γ Ω : Type*} [Group Γ] [MulAction Γ Ω]
    (g : Γ) {A B : Ω} (hne : A ≠ B)
    (hA : g • A = A ∨ g • A = B) (hB : g • B = A ∨ g • B = B) :
    (g ^ 2) • A = A ∧ (g ^ 2) • B = B := by
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact (hne (smul_left_cancel g (hA.trans hB.symm))).elim
  · constructor <;> simp only [pow_two, mul_smul, hA, hB]
  · constructor <;> simp only [pow_two, mul_smul, hA, hB]
  · exact (hne (smul_left_cancel g (hA.trans hB.symm))).elim

private theorem diagonal_mem : diagonal ∈
    Matrix.GeneralLinearGroup.FiveWreathSylow.monomialSubgroup := by
  classical
  let w : Matrix.GeneralLinearGroup.FiveWreathSylow.UnitWreath :=
    ⟨fun x => if x = 1 then twoUnit else 1, 1⟩
  refine ⟨Matrix.GeneralLinearGroup.FiveWreathSylow.wreathUnitEquiv.symm w, ?_⟩
  simp [Matrix.GeneralLinearGroup.FiveWreathSylow.wreathHom,
    Matrix.GeneralLinearGroup.FiveWreathSylow.monomialHom,
    Matrix.GeneralLinearGroup.FiveWreathSylow.monomial,
    Matrix.GeneralLinearGroup.FiveWreathSylow.switch, w, diagonal]

private theorem exists_diagonal_conjugate (S : Subgroup (MulAut V))
    (hS : Nat.card S = 32) : ∃ g : MulAut V, g * delta * g⁻¹ ∈ S := by
  classical
  let T := S.map glAut.symm.toMonoidHom
  have hT : Nat.card T = 32 :=
    (Subgroup.card_map_of_injective glAut.symm.injective).trans hS
  let P := Matrix.GeneralLinearGroup.FiveWreathSylow.sylowOfCard32 T hT
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GLFive
    Matrix.GeneralLinearGroup.FiveWreathSylow.monomialSylow P
  have hd : g * diagonal * g⁻¹ ∈ T := by
    have h := Subgroup.smul_mem_pointwise_smul diagonal (MulAut.conj g)
      Matrix.GeneralLinearGroup.FiveWreathSylow.monomialSubgroup diagonal_mem
    change g * diagonal * g⁻¹ ∈
      ((g • Matrix.GeneralLinearGroup.FiveWreathSylow.monomialSylow : Sylow 2 GLFive) :
        Subgroup GLFive) at h
    rw [hg] at h
    exact h
  obtain ⟨s, hs, he⟩ := hd
  refine ⟨glAut g, ?_⟩
  have hh := congrArg glAut he
  have hs' : glAut (g * diagonal * g⁻¹) ∈ S := by
    rw [← hh]
    change glAut (glAut.symm s) ∈ S
    rw [glAut.apply_symm_apply]
    exact hs
  simpa only [map_mul, map_inv, delta] using hs'

private theorem native_pair_unique (S : Subgroup (MulAut V)) (hS : Nat.card S = 32)
    (A B C D : Subgroup V)
    (hA : Nat.card A = 5) (hB : Nat.card B = 5)
    (hC : Nat.card C = 5) (hD : Nat.card D = 5)
    (hAB : A ≠ B) (hCD : C ≠ D)
    (hpresAB : ∀ s ∈ S, (s • A = A ∨ s • A = B) ∧ (s • B = A ∨ s • B = B))
    (hpresCD : ∀ s ∈ S, (s • C = C ∨ s • C = D) ∧ (s • D = C ∨ s • D = D)) :
    ({A, B} : Set (Subgroup V)) = {C, D} := by
  obtain ⟨g, hg⟩ := exists_diagonal_conjugate S hS
  have pair_axes (L M : Subgroup V) (hL : Nat.card L = 5) (hM : Nat.card M = 5)
      (hne : L ≠ M)
      (hp : ((g * delta * g⁻¹) • L = L ∨ (g * delta * g⁻¹) • L = M) ∧
        ((g * delta * g⁻¹) • M = L ∨ (g * delta * g⁻¹) • M = M)) :
      ({g⁻¹ • L, g⁻¹ • M} : Set (Subgroup V)) = {axis 0, axis 1} := by
    have hl : delta • (g⁻¹ • L) = g⁻¹ • L ∨ delta • (g⁻¹ • L) = g⁻¹ • M := by
      simpa only [mul_smul, inv_smul_smul] using
        hp.1.imp (congrArg (g⁻¹ • ·)) (congrArg (g⁻¹ • ·))
    have hm : delta • (g⁻¹ • M) = g⁻¹ • L ∨ delta • (g⁻¹ • M) = g⁻¹ • M := by
      simpa only [mul_smul, inv_smul_smul] using
        hp.2.imp (congrArg (g⁻¹ • ·)) (congrArg (g⁻¹ • ·))
    have hne' : g⁻¹ • L ≠ g⁻¹ • M := fun h => hne (smul_left_cancel g⁻¹ h)
    have hsq := square_fixes_pair delta hne' hl hm
    have hcL : Nat.card (g⁻¹ • L : Subgroup V) = 5 :=
      (Subgroup.card_map_of_injective g.symm.injective).trans hL
    have hcM : Nat.card (g⁻¹ • M : Subgroup V) = 5 :=
      (Subgroup.card_map_of_injective g.symm.injective).trans hM
    have hL' := fixed_line_axis (g⁻¹ • L) hcL hsq.1
    have hM' := fixed_line_axis (g⁻¹ • M) hcM hsq.2
    rcases hL' with hL' | hL' <;> rcases hM' with hM' | hM'
    · exact (hne' (hL'.trans hM'.symm)).elim
    · rw [hL', hM']
    · rw [hL', hM', Set.pair_comm]
    · exact (hne' (hL'.trans hM'.symm)).elim
  have hab := pair_axes A B hA hB hAB (hpresAB _ hg)
  have hcd := pair_axes C D hC hD hCD (hpresCD _ hg)
  have he := congrArg (Set.image (g • ·)) (hab.trans hcd.symm)
  simpa only [Set.image_pair, smul_inv_smul] using he

private theorem map_congr_aut {E F : Type*} [Group E] [Group F]
    (e : E ≃* F) (a : MulAut E) (L : Subgroup E) :
    (L.map e.toMonoidHom).map ((MulAut.congr e) a).toMonoidHom =
      (L.map a.toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  exact congrArg (fun y => e (a y)) (e.symm_apply_apply x)

private theorem full_pair_preserved {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 5 E] (hE : Nat.card E = 25)
    (S : Subgroup (MulAut E)) (hS : Nat.card S = 32)
    (A B : Subgroup E) (hA : Nat.card A = 5)
    (hp : ∀ s ∈ S, s • A = A ∨ s • A = B) :
    ∀ s ∈ S, (s • A = A ∨ s • A = B) ∧ (s • B = A ∨ s • B = B) := by
  classical
  have hm : ∃ t ∈ S, t • A = B := by
    by_contra! hn
    have hf : ∀ s ∈ S, s • A = A := fun s hs => (hp s hs).resolve_right (hn s hs)
    have ht : MulAction.stabilizer S A = ⊤ := by
      apply top_unique
      intro s _
      exact hf s.val s.property
    have hd := stabilizer_card_dvd hE S A hA
    rw [ht, Subgroup.card_top, hS] at hd
    norm_num at hd
  obtain ⟨t, ht, htm⟩ := hm
  intro s hs
  refine ⟨hp s hs, ?_⟩
  have hh := hp (s * t) (S.mul_mem hs ht)
  simpa only [mul_smul, htm] using hh

/-- An order-32 subgroup of the automorphism group of the elementary abelian
five-plane preserves at most one unordered pair of distinct order-five
subgroups. It suffices to give the orbit condition on one member of each pair:
no line can be fixed by the entire order-32 subgroup. -/
public theorem invariant_pair_unique {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 5 E] (hE : Nat.card E = 25)
    (S : Subgroup (MulAut E)) (hS : Nat.card S = 32)
    (A B C D : Subgroup E)
    (hA : Nat.card A = 5) (hB : Nat.card B = 5)
    (hC : Nat.card C = 5) (hD : Nat.card D = 5)
    (hAB : A ≠ B) (hCD : C ≠ D)
    (hpresAB : ∀ s ∈ S, A.map s.toMonoidHom = A ∨ A.map s.toMonoidHom = B)
    (hpresCD : ∀ s ∈ S, C.map s.toMonoidHom = C ∨ C.map s.toMonoidHom = D) :
    ({A, B} : Set (Subgroup E)) = {C, D} := by
  classical
  have hdim : Module.finrank (ZMod 5) (Additive E) = 2 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 5) (V := Additive E)
    change Nat.card E = _ at hc
    rw [Nat.card_zmod, hE] at hc
    exact (Nat.pow_right_injective (by decide : 2 ≤ 5)) hc.symm
  let lin : Additive E ≃ₗ[ZMod 5] (Fin 2 → ZMod 5) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hdim])
  let e : E ≃* V := lin.toAddEquiv.toMultiplicativeRight
  let S' := S.map (MulAut.congr e).toMonoidHom
  have hS' : Nat.card S' = 32 :=
    (Subgroup.card_map_of_injective (MulAut.congr e).injective).trans hS
  have map_card (L : Subgroup E) (hL : Nat.card L = 5) :
      Nat.card (L.map e.toMonoidHom) = 5 :=
    (Subgroup.card_map_of_injective e.injective).trans hL
  have map_ne {L M : Subgroup E} (h : L ≠ M) :
      L.map e.toMonoidHom ≠ M.map e.toMonoidHom :=
    fun he => h (Subgroup.map_injective e.injective he)
  have map_pres (L M : Subgroup E) (hL : Nat.card L = 5)
      (hp : ∀ s ∈ S, L.map s.toMonoidHom = L ∨ L.map s.toMonoidHom = M) :
      ∀ s ∈ S',
        (s • L.map e.toMonoidHom = L.map e.toMonoidHom ∨
          s • L.map e.toMonoidHom = M.map e.toMonoidHom) ∧
        (s • M.map e.toMonoidHom = L.map e.toMonoidHom ∨
          s • M.map e.toMonoidHom = M.map e.toMonoidHom) := by
    intro s hs
    obtain ⟨a, ha, rfl⟩ := hs
    have hh := full_pair_preserved hE S hS L M hL hp a ha
    change ((L.map e.toMonoidHom).map ((MulAut.congr e) a).toMonoidHom = _ ∨
      (L.map e.toMonoidHom).map ((MulAut.congr e) a).toMonoidHom = _) ∧
      ((M.map e.toMonoidHom).map ((MulAut.congr e) a).toMonoidHom = _ ∨
      (M.map e.toMonoidHom).map ((MulAut.congr e) a).toMonoidHom = _)
    rw [map_congr_aut, map_congr_aut]
    exact ⟨hh.1.imp (congrArg (Subgroup.map e.toMonoidHom))
      (congrArg (Subgroup.map e.toMonoidHom)),
      hh.2.imp (congrArg (Subgroup.map e.toMonoidHom))
      (congrArg (Subgroup.map e.toMonoidHom))⟩
  have he := native_pair_unique S' hS'
    (A.map e.toMonoidHom) (B.map e.toMonoidHom)
    (C.map e.toMonoidHom) (D.map e.toMonoidHom)
    (map_card A hA) (map_card B hB) (map_card C hC) (map_card D hD)
    (map_ne hAB) (map_ne hCD) (map_pres A B hA hpresAB) (map_pres C D hC hpresCD)
  have hh : (Subgroup.map e.toMonoidHom) '' ({A, B} : Set (Subgroup E)) =
      (Subgroup.map e.toMonoidHom) '' ({C, D} : Set (Subgroup E)) := by
    simpa only [Set.image_pair] using he
  exact (Set.image_injective.mpr (Subgroup.map_injective e.injective)) hh

end IsElementaryAbelian.FivePlaneGeometry
