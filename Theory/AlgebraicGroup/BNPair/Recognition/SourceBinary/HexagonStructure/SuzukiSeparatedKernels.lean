module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiKernelIntersections
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanOpposition
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The separated opposite-type Suzuki Cartan kernels

Assume the regular Suzuki parameters have been synchronized. If the Cartan
kernel on U_i meets the kernel on U_j^(s_i s_j) nontrivially, the already
proved same-type and joint-kernel intersections force its centralizer in
U_si to be precisely that single orthogonal root. Unique five-root coordinates
prove this equality on the actual radical. The Suzuki degree bound makes
R_i centralize that root, whose order is only q².

Thus (H ∩ R_i) and the proposed intersection embed as a disjoint product in
the latter root kernel. Joint panel faithfulness embeds this product in the
Cartan action on U_i^(s_i s_j). The actual image has order q−1, already equal
to |H ∩ R_i|, so the additional intersection is trivial. This uses the proved
full Cartan image bound in place of repeating the automorphism classification.
The final export translates the action kernels to literal ambient subgroups
and the source right-conjugation word s_i s_j.

Source: Fong--Seitz I (6C), end of printed p.40 and start of p.41.
This completes that separated kernel case, not the later rank-one Cartan
intersection or radical commutator contradiction. Original/geometric
consumers discharge parameter equality using SuzukiParameters.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private abbrev kernelAt (i : Fin 2) (w : Weyl Q) := (rootAction Q split i w).ker
private abbrev H := (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))

private theorem kernelAt_one (i : Fin 2) : kernelAt Q split i 1 = (cartanPanelMap Q i).ker := by
  rw [kernelAt,rootAction_kernel_conjugate,map_one]
  rfl

private theorem kernelAt_mul (i : Fin 2) (v w : Weyl Q) :
    kernelAt Q split i (v*w) = (kernelAt Q split i v).comap (weylCartanAction Q split w).toMonoidHom := by
  simp only [kernelAt,rootAction_kernel_conjugate,map_mul]
  rfl

private theorem kernelAt_simple_fixed (i : Fin 2) {h : H Q}
    (hh : h ∈ kernelAt Q split i 1) : simpleCartanAction Q split i h = h := by
  rw [kernelAt_one] at hh
  exact cartanPanelMap_kernel_le_fixed Q split i (UnitarySource.actorReflection Q split i) hh

private theorem kernelAt_orthogonal (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    kernelAt Q split i (Q.simple j*Q.simple i*Q.simple j) =
      kernelAt Q split i (Q.simple j*Q.simple i) := by
  simp only [kernelAt,rootAction,RootAction.action_kernel,
    GTwoSource.orthogonal_root_stabilizer Q split hhex i j hij]

private theorem kernelAt_pair (hcore : Q.tits.B.normalCore = ⊥)
    (i j : Fin 2) (hij : i ≠ j) (w : Weyl Q) :
    kernelAt Q split i w ⊓ kernelAt Q split j w = ⊥ := by
  simp only [kernelAt,rootAction_kernel_conjugate,←comap_inf]
  have hjoint : (cartanPanelMap Q i).ker ⊓ (cartanPanelMap Q j).ker = ⊥ := by
    apply eq_bot_iff.mpr
    intro h hh
    have h0 : h ∈ (cartanPanelMap Q 0).ker := by
      by_cases hi : i = 0
      · subst i; exact hh.1
      · have hj : j = 0 := by omega
        subst j; exact hh.2
    have h1 : h ∈ (cartanPanelMap Q 1).ker := by
      by_cases hi : i = 1
      · subst i; exact hh.1
      · have hj : j = 1 := by omega
        subst j; exact hh.2
    have he : ((cartanPanelMap Q 0).prod (cartanPanelMap Q 1)) h = 1 := Prod.ext h0 h1
    exact (cartanPanelPair_injective Q split (UnitarySource.actorReflection Q split) hcore)
      (he.trans (map_one _).symm)
  rw [hjoint]
  exact (MonoidHom.ker_eq_bot_iff _).mpr (weylCartanAction Q split w).injective

private theorem kernelAt_same (hhex : rotationOrder Q = 6)
    (hcore : Q.tits.B.normalCore = ⊥) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup n)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup n) :
    kernelAt Q split i 1 ⊓ kernelAt Q split i (Q.simple j) = ⊥ := by
  have he := suzuki_same_type_cartan_kernels_disjoint Q split hhex hcore i j hij hKi hKj hm hn μi μj νi νj
  apply eq_bot_iff.mpr
  intro h hh
  have h1 := hh.1
  have h2 := hh.2
  rw [kernelAt_one,cartanPanelMap_kernel] at h1
  rw [kernelAt,rootAction_kernel_conjugate,cartanPanelMap_kernel] at h2
  have hw : weylCartanAction Q split (Q.simple j) = normalizerCartanAction Q (representative (Q.simple j)) := by
    conv_lhs => rw [←representative_spec (Q.simple j),weylCartanAction_lift]
  change ((weylCartanAction Q split (Q.simple j) h : H Q) : X ⧸ Q.D) ∈ embeddedPanelKernel Q i at h2
  rw [hw] at h2
  apply Subtype.ext
  apply he.le
  exact ⟨⟨h.property,h1⟩,
    (mem_normalizer_iff.mp (torus_normalizes (representative (Q.simple j))) _).mp h.property,h2⟩

private theorem kernelAt_same_three (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (h : kernelAt Q split i 1 ⊓ kernelAt Q split i (Q.simple j) = ⊥) :
    kernelAt Q split i 1 ⊓ kernelAt Q split i (Q.simple j*Q.simple i) = ⊥ ∧
      kernelAt Q split i (Q.simple j) ⊓ kernelAt Q split i (Q.simple j*Q.simple i) = ⊥ := by
  have hfirst : kernelAt Q split i 1 ⊓ kernelAt Q split i (Q.simple j*Q.simple i) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hi := kernelAt_simple_fixed Q split i hx.1
    have hx2 := hx.2
    rw [kernelAt_mul] at hx2
    change simpleCartanAction Q split i x ∈ kernelAt Q split i (Q.simple j) at hx2
    rw [hi] at hx2
    exact h.le ⟨hx.1,hx2⟩
  refine ⟨hfirst,?_⟩
  apply eq_bot_iff.mpr
  intro x hx
  let y := simpleCartanAction Q split j x
  have hy1 : y ∈ kernelAt Q split i 1 := by
    have hx1 := hx.1
    rw [kernelAt,rootAction_kernel_conjugate] at hx1
    rw [kernelAt_one]
    exact hx1
  have hy2 : y ∈ kernelAt Q split i (Q.simple j*Q.simple i) := by
    have hx2 := hx.2
    rw [←kernelAt_orthogonal Q split hhex i j hij,kernelAt_mul] at hx2
    exact hx2
  have hy : y = 1 := hfirst.le ⟨hy1,hy2⟩
  exact (simpleCartanAction Q split j).map_eq_one_iff.mp hy

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

private theorem rootAt_fixed (i : Fin 2) (T : Subgroup (H Q)) (w : Weyl Q)
    (hT : T ≤ kernelAt Q split i w) :
    rootAt Q split i w ≤ centralizer (T.map (H Q).subtype : Set (X ⧸ Q.D)) := by
  intro x hx
  rw [mem_centralizer_iff]
  rintro _ ⟨t,ht,rfl⟩
  have hk := hT ht
  rw [kernelAt,rootAction,RootAction.action_kernel] at hk
  exact (mem_centralizer_iff.mp hk x hx).symm

private theorem radical_centralizer_middle (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (T : Subgroup (X ⧸ Q.D)) (hTH : T ≤ H Q)
    (hA : simpleRoot Q split i ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥)
    (hB : rootAt Q split j (Q.simple i) ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥)
    (hD : rootAt Q split j (Q.simple i*Q.simple j) ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥)
    (hE : rootAt Q split i (Q.simple j) ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥)
    (hC : rootAt Q split i (Q.simple j*Q.simple i) ≤ centralizer (T : Set (X ⧸ Q.D))) :
    simpleRemainder Q split j ⊓ centralizer (T : Set (X ⧸ Q.D)) =
      rootAt Q split i (Q.simple j*Q.simple i) := by
  let A := simpleRoot Q split i
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j)
  let E := rootAt Q split i (Q.simple j)
  apply le_antisymm
  · intro x hx
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
  · refine le_inf ?_ hC
    exact (show C ≤ middleRoots Q split i j from le_sup_right.trans le_sup_left).trans
      (middleRoots_le_remainder Q split hhex i j hij)

/-- The separated opposite-type Cartan kernels have trivial intersection. -/
theorem suzuki_separated_cartan_kernels_disjoint (hhex : rotationOrder Q = 6)
    (hcore : Q.tits.B.normalCore = ⊥) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    (cartanPanelMap Q i).ker ⊓ (rootAction Q split j (Q.simple i*Q.simple j)).ker = ⊥ := by
  let T := kernelAt Q split i 1 ⊓ kernelAt Q split j (Q.simple i*Q.simple j)
  change (cartanPanelMap Q i).ker ⊓ kernelAt Q split j (Q.simple i*Q.simple j) = ⊥
  rw [←kernelAt_one Q split i]
  change T = ⊥
  by_contra hT
  let A := T.map (H Q).subtype
  have hAH : A ≤ H Q := map_subtype_le _
  have hi := kernelAt_same Q split hhex hcore i j hij hKi hKj hm hm μi μj νi νj
  have hj := kernelAt_same Q split hhex hcore j i hij.symm hKj hKi hm hm μj μi νj νi
  have hi3 := kernelAt_same_three Q split hhex i j hij hi
  have hj3 := kernelAt_same_three Q split hhex j i hij.symm hj
  have hnot (K : Subgroup (H Q)) (hK : T ⊓ K = ⊥) : ¬ T ≤ K := by
    intro hle
    exact hT ((inf_eq_left.mpr hle).symm.trans hK)
  have hTA : ¬ T ≤ kernelAt Q split j 1 := hnot _ (eq_bot_iff.mpr (by
    intro x hx
    exact (kernelAt_pair Q split hcore i j hij 1).le ⟨hx.1.1,hx.2⟩))
  have hTB : ¬ T ≤ kernelAt Q split i (Q.simple j) := hnot _ (eq_bot_iff.mpr (by
    intro x hx
    exact hi.le ⟨hx.1.1,hx.2⟩))
  have hTD : ¬ T ≤ kernelAt Q split i (Q.simple j*Q.simple i) := hnot _ (eq_bot_iff.mpr (by
    intro x hx
    exact hi3.1.le ⟨hx.1.1,hx.2⟩))
  have hTE : ¬ T ≤ kernelAt Q split j (Q.simple i) := hnot _ (eq_bot_iff.mpr (by
    intro x hx
    exact hj3.2.le ⟨hx.2,hx.1.2⟩))
  have hmid : simpleRemainder Q split i ⊓ centralizer (A : Set (X ⧸ Q.D)) =
      rootAt Q split j (Q.simple i*Q.simple j) :=
    radical_centralizer_middle Q split hhex j i hij.symm A hAH
      (by simpa only [rootAt_one] using rootAt_fixedFree Q split j hKj hm μj νj T 1 hTA)
      (rootAt_fixedFree Q split i hKi hm μi νi T _ hTB)
      (rootAt_fixedFree Q split i hKi hm μi νi T _ hTD)
      (rootAt_fixedFree Q split j hKj hm μj νj T _ hTE)
      (rootAt_fixed Q split j T _ inf_le_right)
  have hAR : A ≤ centralizer (rankOne Q split i : Set (X ⧸ Q.D)) := by
    rintro _ ⟨a,ha,rfl⟩
    have hk := ha.1
    rw [kernelAt_one,cartanPanelMap_kernel] at hk
    have hh : (a : X ⧸ Q.D) ∈ H Q ⊓ embeddedPanelKernel Q i := ⟨a.property,hk⟩
    rw [←cartan_centralizer_rankOneRootGroup Q split i] at hh
    exact hh.2
  let d := centralizerSection Q split i hKi A hAR
  have hd : d.numerator = rootAt Q split j (Q.simple i*Q.simple j) := hmid
  have hc : Nat.card d.numerator = 2^(2*(2*m+1)) := by
    rw [hd,rootAt,card_rightConjugate,Nat.card_congr νj.toEquiv,suzukiRootSubgroup_card m hm,←pow_mul]
    congr 1
    omega
  have hact : d.action = 1 := by
    by_contra hact
    have hlo := suzuki_section_card_bound Q split i hm μi d hact
    have hup : Nat.card d.EffectiveCarrier ≤ Nat.card d.numerator :=
      Nat.card_le_card_of_surjective (QuotientGroup.mk' d.effectiveDenominator) (QuotientGroup.mk'_surjective _)
    rw [hc] at hup
    have he := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hlo.trans hup)
    omega
  have hRC : rankOne Q split i ≤ centralizer
      (rootAt Q split j (Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) := by
    intro r hr
    rw [mem_centralizer_iff]
    intro x hx
    let u : d.numerator := ⟨x,hd.symm ▸ hx⟩
    have he := congrArg (fun f : rankOne Q split i →* MulAut d.Carrier =>
      f ⟨r,hr⟩ (QuotientGroup.mk u)) hact
    rw [d.action_mk] at he
    have hv : d.numeratorAction ⟨r,hr⟩ u = u :=
      congrArg (QuotientGroup.quotientBot (G := d.numerator)) he
    have he' : r*x*r⁻¹ = x := congrArg Subtype.val hv
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  let C := (rankOne Q split i).subgroupOf (H Q)
  have hCD : C ≤ kernelAt Q split j (Q.simple i*Q.simple j) := by
    intro c hc
    rw [kernelAt,rootAction,RootAction.action_kernel]
    exact hRC hc
  let D := C ⊔ T
  have hDK : D ≤ kernelAt Q split j (Q.simple i*Q.simple j) := sup_le hCD inf_le_right
  have hCT : Disjoint C T := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro c hc
    have hk := hc.2.1
    rw [kernelAt_one] at hk
    let f := (cartanPanelMap Q i).rangeRestrict.comp C.subtype
    have hf := (suzuki_rankOne_cartan_panel_bijective Q split i hKi hm μi νi).1
    have he : f ⟨c,hc.1⟩ = 1 := Subtype.ext hk
    have he' : (⟨c,hc.1⟩ : C) = 1 := hf (he.trans (map_one f).symm)
    exact congrArg Subtype.val he'
  let f := (rootAction Q split i (Q.simple i*Q.simple j)).rangeRestrict.comp D.subtype
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    have hx' : (x : H Q) ∈ kernelAt Q split i (Q.simple i*Q.simple j) := congrArg Subtype.val hx
    exact Subtype.ext ((kernelAt_pair Q split hcore i j hij _).le ⟨hx',hDK x.property⟩)
  have hDcard : Nat.card D ≤ 2^(2*m+1)-1 := by
    have he := Nat.card_le_card_of_injective f hf
    rw [Nat.card_congr (rootActionImageEquiv Q split i (Q.simple i*Q.simple j)).toEquiv,
      suzuki_cartan_panel_image_card Q split i hKi hm μi νi] at he
    exact he
  let e : (H Q).subgroupOf (rankOne Q split i) ≃* C :=
    { toFun c := ⟨⟨c,c.property⟩,c.val.property⟩
      invFun c := ⟨⟨c,c.property⟩,c.val.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl }
  have hCcard : Nat.card C = 2^(2*m+1)-1 := (Nat.card_congr e.symm.toEquiv).trans
    (suzuki_rankOne_cartan_cyclic_card Q split i hKi hm μi νi
      (UnitarySource.actorReflection Q split i)).2
  let := split.abelian
  have hDc : Nat.card D = Nat.card C * Nat.card T :=
    card_sup_eq_mul_of_normalizes_of_disjoint C T (by rw [Subgroup.normalizer_eq_top]; exact le_top) hCT
  rw [hDc,hCcard] at hDcard
  have hp : 0 < 2^(2*m+1)-1 := by
    have he : 1 < 2^(2*m+1) := one_lt_pow₀ (by decide) (by omega)
    omega
  have ht1 : Nat.card T ≤ 1 := Nat.le_of_mul_le_mul_left (by simpa only [mul_one] using hDcard) hp
  exact hT (Subgroup.card_eq_one.mp (Nat.le_antisymm ht1 (Nat.card_pos (α := T))))

/-- The separated-kernel conclusion expressed on ambient subgroups, with
the exact source right-conjugation word s_i s_j. -/
theorem suzuki_separated_local_kernels_disjoint (hhex : rotationOrder Q = 6)
    (hcore : Q.tits.B.normalCore = ⊥) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    ((Q.tits.B ⊓ Q.tits.N) ⊓ localKernel Q i) ⊓
      rightConjugate ((Q.tits.B ⊓ Q.tits.N) ⊓ localKernel Q j)
        (representative (Q.simple i*Q.simple j) : X ⧸ Q.D) = ⊥ := by
  have he := suzuki_separated_cartan_kernels_disjoint Q split hhex hcore i j hij hKi hKj hm μi μj νi νj
  apply eq_bot_iff.mpr
  intro x hx
  let a : H Q := ⟨x,hx.1.1⟩
  have ha : a ∈ (cartanPanelMap Q i).ker := by
    rw [cartanPanelMap_kernel]
    exact hx.1.2
  have hb : a ∈ (rootAction Q split j (Q.simple i*Q.simple j)).ker := by
    rw [rootAction_kernel_conjugate,cartanPanelMap_kernel]
    change ((weylCartanAction Q split (Q.simple i*Q.simple j) a : H Q) : X ⧸ Q.D) ∈ embeddedPanelKernel Q j
    have hw : weylCartanAction Q split (Q.simple i*Q.simple j) =
        normalizerCartanAction Q (representative (Q.simple i*Q.simple j)) := by
      conv_lhs => rw [←representative_spec (Q.simple i*Q.simple j),weylCartanAction_lift]
    rw [hw]
    exact hx.2.2
  exact congrArg Subtype.val (show a = 1 from he.le ⟨ha,hb⟩)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
