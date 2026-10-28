module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiDerivedProducts
/-!
# Locating the Suzuki rank-one centralizer in the middle root

The rank-one Cartan acts without nonidentity fixed points on each of the
four nonmiddle roots in the actual five-root radical coordinates. Otherwise
its reflection places it in two distinct root-action kernels, contradicting
their trivial intersection. Uniqueness of the ordered coordinates then puts
the radical centralizer of the entire rank-one group in the middle root.

This is the geometric placement needed for the denominator of the natural
composition section in Fong--Seitz I (6C), printed p.41. All groups and
conjugation words are the canonical subgroups of the same marked quotient.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped IsMulCommutative commutatorElement
open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
private abbrev kernelAt (i : Fin 2) (w : Weyl Q) := (rootAction Q split i w).ker
private abbrev H := (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))
private theorem rootAt_fixed_iff_kernel (i : Fin 2)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    {m : ℕ} (hm : 0 < m) (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (w : Weyl Q) (h : H Q) (x : rootAt Q split i w) (hx : x ≠ 1) :
    Commute (h : X ⧸ Q.D) (x : X ⧸ Q.D) ↔ h ∈ kernelAt Q split i w := by
  constructor
  · intro hfix
    let n := representative w
    let e := RootAction.conjugateEquiv (simpleRoot Q split i) (n : X ⧸ Q.D)
    have hf : Commute ((normalizerCartanAction Q n h : H Q) : X ⧸ Q.D)
        ((e x : simpleRoot Q split i) : X ⧸ Q.D) :=
      hfix.map (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom
    have hk := (suzuki_cartan_root_fixed_iff_kernel Q split i hKi hm μ ν
      (normalizerCartanAction Q n h) (e x) (fun he => hx (e.map_eq_one_iff.mp he))).mp hf
    rw [kernelAt,rootAction_kernel_conjugate]
    change weylCartanAction Q split w h ∈ (cartanPanelMap Q i).ker
    have hw : weylCartanAction Q split w = normalizerCartanAction Q n := by
      conv_lhs => rw [←representative_spec w,weylCartanAction_lift]
    rwa [hw]
  · intro hk
    rw [kernelAt,rootAction,RootAction.action_kernel] at hk
    exact (mem_centralizer_iff.mp hk x x.property).symm

private theorem rootAt_fixedFree (i : Fin 2)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    {m : ℕ} (hm : 0 < m) (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (T : Subgroup (H Q)) (w : Weyl Q) (hT : ¬ T ≤ kernelAt Q split i w) :
    rootAt Q split i w ⊓ centralizer (T.map (H Q).subtype : Set (X ⧸ Q.D)) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  by_contra hx1
  apply hT
  intro t ht
  exact (rootAt_fixed_iff_kernel Q split i hKi hm μ ν w t ⟨x,hx.1⟩
    (fun he => hx1 (congrArg Subtype.val he))).mp
      (mem_centralizer_iff.mp hx.2 t (mem_map_of_mem _ ht))

private theorem radical_centralizer_le_middle (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (T : Subgroup (X ⧸ Q.D)) (hTH : T ≤ H Q)
    (hA : simpleRoot Q split i ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥)
    (hB : rootAt Q split j (Q.simple i) ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥)
    (hD : rootAt Q split j (Q.simple i*Q.simple j) ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥)
    (hE : rootAt Q split i (Q.simple j) ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥)
    : simpleRemainder Q split j ⊓ centralizer (T : Set (X ⧸ Q.D)) ≤
      rootAt Q split i (Q.simple j*Q.simple i) := by
  let A := simpleRoot Q split i
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j)
  let E := rootAt Q split i (Q.simple j)
  intro x hx
  obtain ⟨⟨a,b,c,d,e⟩,he⟩ := (radicalCoordinates Q split hhex i j hij).surjective ⟨x,hx.1⟩
  have he' : (a : X ⧸ Q.D)*b*c*d*e = x := by
    simpa only [radicalCoordinates_apply] using congrArg Subtype.val he
  have htuple (t : X ⧸ Q.D) (ht : t ∈ T) :
      (A.normalizerMonoidHom ⟨t,torus_normalizes_simpleRoot Q split i (hTH ht)⟩ a,
       B.normalizerMonoidHom ⟨t,rootAt_torus_normalizes Q split j _ (hTH ht)⟩ b,
       C.normalizerMonoidHom ⟨t,rootAt_torus_normalizes Q split i _ (hTH ht)⟩ c,
       D.normalizerMonoidHom ⟨t,rootAt_torus_normalizes Q split j _ (hTH ht)⟩ d,
       E.normalizerMonoidHom ⟨t,rootAt_torus_normalizes Q split i _ (hTH ht)⟩ e) = (a,b,c,d,e) := by
    apply (radicalCoordinates Q split hhex i j hij).injective
    apply Subtype.ext
    simp only [radicalCoordinates_apply]
    change (t*a*t⁻¹)*(t*b*t⁻¹)*(t*c*t⁻¹)*(t*d*t⁻¹)*(t*e*t⁻¹) = (a : X ⧸ Q.D)*b*c*d*e
    calc
      _ = t*((a : X ⧸ Q.D)*b*c*d*e)*t⁻¹ := by group
      _ = _ := by rw [he',mem_centralizer_iff.mp hx.2 t ht,mul_inv_cancel_right]
  have ha : (a : X ⧸ Q.D) ∈ centralizer (T : Set (X ⧸ Q.D)) := by
    rw [mem_centralizer_iff]
    intro t ht
    exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun z : A × B × C × D × E => (z.1 : X ⧸ Q.D)) (htuple t ht))
  have hb : (b : X ⧸ Q.D) ∈ centralizer (T : Set (X ⧸ Q.D)) := by
    rw [mem_centralizer_iff]
    intro t ht
    exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun z : A × B × C × D × E => (z.2.1 : X ⧸ Q.D)) (htuple t ht))
  have hd : (d : X ⧸ Q.D) ∈ centralizer (T : Set (X ⧸ Q.D)) := by
    rw [mem_centralizer_iff]
    intro t ht
    exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun z : A × B × C × D × E => (z.2.2.2.1 : X ⧸ Q.D)) (htuple t ht))
  have hec : (e : X ⧸ Q.D) ∈ centralizer (T : Set (X ⧸ Q.D)) := by
    rw [mem_centralizer_iff]
    intro t ht
    exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun z : A × B × C × D × E => (z.2.2.2.2 : X ⧸ Q.D)) (htuple t ht))
  have ha1 : (a : X ⧸ Q.D) = 1 := hA.le ⟨a.property,ha⟩
  have hb1 : (b : X ⧸ Q.D) = 1 := hB.le ⟨b.property,hb⟩
  have hd1 : (d : X ⧸ Q.D) = 1 := hD.le ⟨d.property,hd⟩
  have he1 : (e : X ⧸ Q.D) = 1 := hE.le ⟨e.property,hec⟩
  rw [ha1,hb1,hd1,he1,one_mul,one_mul,mul_one,mul_one] at he'
  exact he' ▸ c.property

/-- The rank-one Cartan has no nonidentity fixed point on any of the
four nonmiddle radical roots. Reflection invariance would put it in two
of the separated kernels if it centralized one of these roots. -/
theorem suzuki_nonmiddle_rankOne_cartan_fixedFree (hhex : rotationOrder Q = 6)
    (hcore : Q.tits.B.normalCore = ⊥) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    (t : Fin 5) (ht : t ≠ 2) :
    rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ⊓
      centralizer (((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split j : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) = ⊥ := by
  let T := (rankOne Q split j).subgroupOf (H Q)
  have hTmap : T.map (H Q).subtype = H Q ⊓ rankOne Q split j := by
    rw [subgroupOf_map_subtype,inf_comm]
  have hTne : T ≠ ⊥ := by
    intro he
    have hc := (suzuki_rankOne_cartan_cyclic_card Q split j hKj hm μj νj
      (UnitarySource.actorReflection Q split j)).2
    have hcard : Nat.card T = Nat.card ((H Q).subgroupOf (rankOne Q split j)) := by
      let e : T ≃* (H Q).subgroupOf (rankOne Q split j) := {
        toFun x := ⟨⟨x,x.property⟩,x.val.property⟩
        invFun x := ⟨⟨x,x.property⟩,x.val.property⟩
        left_inv _ := rfl
        right_inv _ := rfl
        map_mul' _ _ := rfl }
      exact Nat.card_congr e.toEquiv
    rw [he] at hcard
    have hbot : Nat.card (⊥ : Subgroup (H Q)) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩
    rw [hbot] at hcard
    have hz : 1 = 2^(2*m+1)-1 := hcard.trans hc
    have hpow := Nat.lt_two_pow_self (n := 2*m+1)
    omega
  have hTinvariant {z : H Q} (hz : z ∈ T) : simpleCartanAction Q split j z ∈ T := by
    let s := UnitarySource.actorReflection Q split j
    have he : simpleCartanAction Q split j = normalizerCartanAction Q s.val := by
      change weylCartanAction Q split (Q.simple j) = _
      rw [←s.class_eq,weylCartanAction_lift]
    rw [he]
    change (s.val : X ⧸ Q.D)*z*(s.val : X ⧸ Q.D)⁻¹ ∈ rankOne Q split j
    exact mul_mem (mul_mem s.mem_rankOne hz) (inv_mem s.mem_rankOne)
  have hs : Q.simple j*Q.simple j = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem j)).2
  have hnot : ¬ T ≤ kernelAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) := by
    intro hle
    let u : Fin 5 := ⟨4-t.val,by omega⟩
    have htu : t ≠ u := by
      intro he
      apply ht
      apply Fin.ext
      have hh := congrArg Fin.val he
      change t.val = 4-t.val at hh
      omega
    have hswap : kernelAt Q split (radicalRootKind i j u) (radicalRootWord Q i j u) =
        (kernelAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)).comap
          (simpleCartanAction Q split j).toMonoidHom := by
      have hmul (k : Fin 2) (w : Weyl Q) :
          kernelAt Q split k (w*Q.simple j) =
            (kernelAt Q split k w).comap (simpleCartanAction Q split j).toMonoidHom := by
        simp only [kernelAt,rootAction_kernel_conjugate,map_mul]
        rfl
      fin_cases t
      · change kernelAt Q split i (Q.simple j) = (kernelAt Q split i 1).comap _
        simpa only [one_mul] using hmul i 1
      · change kernelAt Q split j (Q.simple i*Q.simple j) = (kernelAt Q split j (Q.simple i)).comap _
        exact hmul j (Q.simple i)
      · exact (ht rfl).elim
      · change kernelAt Q split j (Q.simple i) = (kernelAt Q split j (Q.simple i*Q.simple j)).comap _
        simpa only [mul_assoc,hs,mul_one] using hmul j (Q.simple i*Q.simple j)
      · change kernelAt Q split i 1 = (kernelAt Q split i (Q.simple j)).comap _
        simpa only [hs] using hmul i (Q.simple j)
    have hle' : T ≤ kernelAt Q split (radicalRootKind i j u) (radicalRootWord Q i j u) := by
      rw [hswap]
      exact fun z hz => hle (hTinvariant hz)
    exact hTne (bot_unique ((le_inf hle hle').trans
      (suzuki_radical_root_kernels_disjoint Q split hhex hcore i j hij hKi hKj hm μi μj νi νj htu).le))
  rw [←hTmap]
  by_cases hk : radicalRootKind i j t = i
  · rw [hk] at hnot ⊢
    exact rootAt_fixedFree Q split i hKi hm μi νi T _ hnot
  · have hk' : radicalRootKind i j t = j := by
      omega
    rw [hk'] at hnot ⊢
    exact rootAt_fixedFree Q split j hKj hm μj νj T _ hnot

/-- The actual radical centralizer of its rank-one actor is contained in
the middle root, by the four fixed-point exclusions and unique coordinates. -/
theorem suzuki_radical_rankOne_centralizer_le_middle (hhex : rotationOrder Q = 6)
    (hcore : Q.tits.B.normalCore = ⊥) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    simpleRemainder Q split j ⊓ centralizer (rankOne Q split j : Set (X ⧸ Q.D)) ≤
      rootAt Q split i (Q.simple j*Q.simple i) := by
  have hf := suzuki_nonmiddle_rankOne_cartan_fixedFree Q split hhex hcore i j hij hKi hKj hm μi μj νi νj
  apply (inf_le_inf_left _ (centralizer_le (show H Q ⊓ rankOne Q split j ≤ rankOne Q split j from inf_le_right))).trans
  apply radical_centralizer_le_middle Q split hhex i j hij _ inf_le_left
  · have hh := hf 0 (by decide)
    change rootAt Q split i 1 ⊓ _ = ⊥ at hh
    rwa [rootAt_one] at hh
  · exact hf 1 (by decide)
  · exact hf 3 (by decide)
  · exact hf 4 (by decide)


end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
