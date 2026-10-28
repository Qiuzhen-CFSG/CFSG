module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.ElementaryEight

/-!
# An elementary eight from a norm-one Cayley frame in G₂(3)

The vectors `a`, `b`, `c` give a Cayley frame
`(1, a, b, ab, c, ac, bc, (ab)c)` whose eight vectors all have norm one.
An explicit inverse coordinate map proves that this is a basis. The signed
multiplication table is graded by the additive group of `𝔽₂³`. Its sign
characters therefore define an injective homomorphism into the actual
split-octonion automorphism group, with elementary abelian image of order eight.

The characters separate the eight basis lines. An automorphism centralizing
the image preserves each line; its nonzero scalars on the algebra generators
`a`, `b`, `c` are the three signs of a character. Thus the ambient centralizer
is the eight itself. In the actual normalizer, the eight lies in the intrinsic
two-core, which is consequently self-centralizing. The conjugation homomorphism
to `Aut(E)` has kernel `E`, so the normalizer order divides `8 * 168` and is
not divisible by 27. No surjectivity onto `Aut(E)` or exact normalizer order
is asserted here. The split-torus eight in the parent module is preserved.

Source context: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(4), printed pp.3–4 (Theorem 0.1.1 on pp.481–482), and
§I.4(G2), printed p.417. These are local model facts for the converse;
coverage of maximal two-locals and the full source theorem are separate.
The frame was found in `Scratch/G2TernaryCover/corrected_frame.py` in the
retained coverage workspace; all facts used here are proved in Lean.
The multiplication is from the ATLAS port, Copyright (c) 2026 Gerald Höhn
and the ATLAS contributors, under the ATLAS Research and Attribution License
1.0; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Atlas.SplitOctonion
namespace Atlas.G2.TernaryLocals.CayleyEight
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev V := Carrier (ZMod 3)
def a : V := ![1,0,0,0,0,0,0,1]
def b : V := ![0,1,0,0,0,0,1,0]
def c : V := ![1,1,0,0,0,0,-1,-1]
/-- The eight explicitly parenthesized Cayley products. -/
def frame : Fin 8 → V := ![unit,a,b,mul a b,c,mul a c,mul b c,mul (mul a b) c]

/-- Send frame coordinates to the original octonion coordinates. -/
def expansion : V →ₗ[ZMod 3] V where
  toFun x := ![x 1+x 4-x 7, x 2+x 4+x 7, -x 3+x 5+x 6,
    x 0+x 5-x 6, x 0-x 5+x 6, -x 3-x 5-x 6, x 2-x 4-x 7, x 1-x 4+x 7]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp <;> ring

/-- The inverse coordinate map, over `𝔽₃`. -/
def coordinates : V →ₗ[ZMod 3] V where
  toFun x := ![-x 3-x 4, -x 0-x 7, -x 1-x 6, x 2+x 5,
    x 0+x 1-x 6-x 7, x 2+x 3-x 4-x 5, x 2-x 3+x 4-x 5, -x 0+x 1-x 6+x 7]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp <;> ring

/-- The invertible change from frame coordinates to octonion coordinates. -/
def frameEquiv : V ≃ₗ[ZMod 3] V where
  toLinearMap := expansion
  invFun := coordinates
  left_inv x := by
    have h : coordinates.comp expansion = LinearMap.id := by
      apply linearMap_ext
      exact (by decide +kernel : ∀ i, coordinates (expansion (basisVector i)) = basisVector i)
    exact congrArg (fun f : V →ₗ[ZMod 3] V => f x) h
  right_inv x := by
    have h : expansion.comp coordinates = LinearMap.id := by
      apply linearMap_ext
      exact (by decide +kernel : ∀ i, expansion (coordinates (basisVector i)) = basisVector i)
    exact congrArg (fun f : V →ₗ[ZMod 3] V => f x) h

@[simp] theorem frameEquiv_basis (i : Fin 8) : frameEquiv (basisVector i) = frame i :=
  (by decide +kernel : ∀ i, frameEquiv (basisVector i) = frame i) i

/-- The all-norm-one Cayley basis in the actual octonion algebra. -/
noncomputable def frameBasis : Module.Basis (Fin 8) (ZMod 3) V :=
  (Pi.basisFun (ZMod 3) (Fin 8)).map frameEquiv

@[simp] theorem frameBasis_apply (i : Fin 8) : frameBasis i = frame i := by
  simpa only [frameBasis, Module.Basis.map_apply, Pi.basisFun_apply, basisVector] using frameEquiv_basis i

@[simp] theorem coe_frameBasis : ⇑frameBasis = frame := funext frameBasis_apply

theorem frame_linearIndependent : LinearIndependent (ZMod 3) frame := by
  simpa only [coe_frameBasis] using frameBasis.linearIndependent

theorem frame_span : Submodule.span (ZMod 3) (Set.range frame) = ⊤ := by
  simpa only [coe_frameBasis] using frameBasis.span_eq

/-- In particular, the supplied frame has rank eight. -/
theorem frame_rank :
    Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range frame)) = 8 := by
  simpa using finrank_span_eq_card frame_linearIndependent

/-- Every vector of this frame has norm one. -/
theorem norm_frame (i : Fin 8) : norm (frame i) = 1 :=
  (by decide +kernel : ∀ i, norm (frame i) = 1) i

/-- Binary digits, with division performed in `ℕ` before reduction modulo two. -/
def grade (i : Fin 8) : Fin 3 → ZMod 2 :=
  ![(i.val : ZMod 2), ((i.val / 2 : Nat) : ZMod 2), ((i.val / 4 : Nat) : ZMod 2)]
def gradeSum (i j : Fin 8) : Fin 8 := Fin.ofNat 8 (Nat.xor i.val j.val)
/-- The signs of the Cayley multiplication table. -/
def twist : Fin 8 → Fin 8 → ZMod 3 :=
  ![![1,1,1,1,1,1,1,1], ![1,-1,1,-1,1,-1,-1,1],
    ![1,-1,-1,1,1,1,-1,-1], ![1,1,-1,-1,1,-1,1,-1],
    ![1,-1,-1,-1,-1,1,1,1], ![1,1,-1,1,-1,-1,-1,1],
    ![1,1,1,-1,-1,1,-1,-1], ![1,-1,1,1,-1,-1,1,-1]]

theorem grade_gradeSum (i j : Fin 8) : grade (gradeSum i j) = grade i + grade j :=
  (by decide +kernel : ∀ i j, grade (gradeSum i j) = grade i + grade j) i j

/-- The complete multiplication table, in the original octonion algebra. -/
theorem frame_mul (i j : Fin 8) :
    mul (frame i) (frame j) = twist i j • frame (gradeSum i j) :=
  (by decide +kernel : ∀ i j, mul (frame i) (frame j) = twist i j • frame (gradeSum i j)) i j



/-- The character paired with a binary parameter. -/
def sign (p : Parameters) (i : Fin 8) : ZMod 3 :=
  (-1) ^ (p.toAdd 0 * grade i 0 + p.toAdd 1 * grade i 1 + p.toAdd 2 * grade i 2).val

theorem sign_sq (p : Parameters) (i : Fin 8) : sign p i * sign p i = 1 :=
  (by decide +kernel : ∀ p i, sign p i * sign p i = 1) p i

theorem sign_gradeSum (p : Parameters) (i j : Fin 8) :
    sign p (gradeSum i j) = sign p i * sign p j :=
  (by decide +kernel : ∀ p i j, sign p (gradeSum i j) = sign p i * sign p j) p i j

theorem sign_one (i : Fin 8) : sign 1 i = 1 :=
  (by decide +kernel : ∀ i, sign 1 i = 1) i

theorem sign_mul (p q : Parameters) (i : Fin 8) : sign (p*q) i = sign p i * sign q i :=
  (by decide +kernel : ∀ p q i, sign (p*q) i = sign p i * sign q i) p q i

def signLinear (p : Parameters) : V →ₗ[ZMod 3] V where
  toFun x i := sign p i * x i
  map_add' x y := by ext i; simp [_root_.mul_add]
  map_smul' r x := by ext i; simp [mul_left_comm]

def signEquiv (p : Parameters) : V ≃ₗ[ZMod 3] V where
  toLinearMap := signLinear p
  invFun := signLinear p
  left_inv x := by ext i; exact (mul_assoc _ _ _).symm.trans (by rw [sign_sq, one_mul])
  right_inv x := by ext i; exact (mul_assoc _ _ _).symm.trans (by rw [sign_sq, one_mul])

theorem signEquiv_basis (p : Parameters) (i : Fin 8) :
    signEquiv p (basisVector i) = sign p i • basisVector i := by
  ext j
  by_cases h : j = i
  · subst j; simp [signEquiv, signLinear, basisVector]
  · simp [signEquiv, signLinear, basisVector, h]

/-- A diagonal sign character, transported to the actual octonion coordinates. -/
def action (p : Parameters) : V ≃ₗ[ZMod 3] V :=
  (frameEquiv.symm.trans (signEquiv p)).trans frameEquiv

@[simp] theorem action_frame (p : Parameters) (i : Fin 8) :
    action p (frame i) = sign p i • frame i := by
  have h : frameEquiv.symm (frame i) = basisVector i := by
    rw [← frameEquiv_basis, LinearEquiv.symm_apply_apply]
  change frameEquiv (signEquiv p (frameEquiv.symm (frame i))) = _
  rw [h, signEquiv_basis, map_smul, frameEquiv_basis]

/-- The graded table makes every sign character multiplicative. -/
theorem action_mul (p : Parameters) (x y : V) :
    action p (mul x y) = mul (action p x) (action p y) := by
  have he : multiplication.compr₂ (action p).toLinearMap =
      multiplication.compl₁₂ (action p).toLinearMap (action p).toLinearMap := by
    apply frameBasis.ext
    intro i
    apply frameBasis.ext
    intro j
    change action p (mul (frameBasis i) (frameBasis j)) =
      mul (action p (frameBasis i)) (action p (frameBasis j))
    simp only [frameBasis_apply, frame_mul, map_smul, action_frame, smul_mul, SplitOctonion.mul_smul,
      smul_smul, sign_gradeSum]
    congr 1
    ring
  exact congrArg (fun f : V →ₗ[ZMod 3] V →ₗ[ZMod 3] V => f x y) he

/-- The sign characters as actual octonion automorphisms. -/
def embedding : Parameters →* Model (ZMod 3) where
  toFun p := ⟨action p, action_mul p⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply frameBasis.ext
    intro i
    change action 1 (frameBasis i) = frameBasis i
    simp only [frameBasis_apply, action_frame, sign_one, one_smul]
  map_mul' p q := by
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply frameBasis.ext
    intro i
    change action (p*q) (frameBasis i) = action p (action q (frameBasis i))
    simp only [frameBasis_apply, action_frame, map_smul, smul_smul, sign_mul]
    rw [mul_comm]

@[simp] theorem embedding_frame (p : Parameters) (i : Fin 8) :
    (embedding p).val (frame i) = sign p i • frame i := action_frame p i

theorem frame_ne_zero (i : Fin 8) : frame i ≠ 0 :=
  (by decide +kernel : ∀ i, frame i ≠ 0) i

theorem embedding_injective : Function.Injective embedding := by
  intro p q h
  have he (i : Fin 8) : sign p i = sign q i := by
    apply smul_left_injective (ZMod 3) (frame_ne_zero i)
    simpa only [embedding_frame] using congrArg (fun g : Model (ZMod 3) => g.val (frame i)) h
  change p.toAdd = q.toAdd
  apply funext
  exact (by decide +kernel : ∀ p q : Parameters,
    (∀ i, sign p i = sign q i) → ∀ k, p.toAdd k = q.toAdd k) p q he

/-- The new Cayley-frame eight; this does not redefine the old torus/Weyl eight. -/
def elementary : Subgroup (Model (ZMod 3)) := embedding.range

noncomputable def elementaryEquiv : Parameters ≃* elementary :=
  MonoidHom.ofInjective embedding_injective

theorem card_elementary : Nat.card elementary = 8 := by
  rw [← Nat.card_congr elementaryEquiv.toEquiv]
  change Nat.card (Fin 3 → ZMod 2) = 8
  simp

instance elementary_isElementaryAbelian : IsElementaryAbelian 2 elementary where
  is_comm := ⟨by
    rintro ⟨_,p,rfl⟩ ⟨_,q,rfl⟩
    apply Subtype.ext
    change embedding p * embedding q = embedding q * embedding p
    rw [← map_mul, ← map_mul, mul_comm]⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    rintro ⟨_,p,rfl⟩
    apply Subtype.ext
    change embedding p ^ 2 = 1
    rw [← map_pow]
    have hp : p^2 = 1 := by
      rw [pow_two]
      change (fun i => p.toAdd i + p.toAdd i) = (fun _ => 0)
      exact funext (fun i => (by decide +kernel : ∀ x : ZMod 2, x+x=0) (p.toAdd i))
    rw [hp, map_one])

theorem character_separates (i j : Fin 8) (h : i ≠ j) :
    ∃ p : Parameters, sign p i ≠ sign p j :=
  (by decide +kernel : ∀ i j, i ≠ j → ∃ p : Parameters, sign p i ≠ sign p j) i j h

theorem action_coordinate (p : Parameters) (x : V) (i : Fin 8) :
    frameEquiv.symm (action p x) i = sign p i * frameEquiv.symm x i := by
  change frameEquiv.symm (frameEquiv (signEquiv p (frameEquiv.symm x))) i = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- Each simultaneous character space is exactly its one-dimensional frame line. -/
theorem character_line (i : Fin 8) (x : V)
    (hx : ∀ p, action p x = sign p i • x) : ∃ r : ZMod 3, x = r • frame i := by
  refine ⟨frameEquiv.symm x i, ?_⟩
  apply frameEquiv.symm.injective
  have hframe : frameEquiv.symm (frame i) = basisVector i := by
    rw [← frameEquiv_basis, LinearEquiv.symm_apply_apply]
  rw [map_smul, hframe]
  ext j
  by_cases hji : j = i
  · subst j
    simp [basisVector]
  · obtain ⟨p,hp⟩ := character_separates j i hji
    have he := congrArg (fun y : V => frameEquiv.symm y j) (hx p)
    rw [action_coordinate, map_smul] at he
    have hz : frameEquiv.symm x j = 0 := by
      by_contra hn
      exact hp (mul_right_cancel₀ hn he)
    simp [basisVector, hji, hz]

private def generators : Fin 3 → V := ![a,b,c]
private def generatorIndex : Fin 3 → Fin 8 := ![1,2,4]

private theorem frame_generatorIndex (i : Fin 3) : frame (generatorIndex i) = generators i :=
  (by decide +kernel : ∀ i, frame (generatorIndex i) = generators i) i

private theorem ext_generators {g h : Model (ZMod 3)}
    (he : ∀ i, g.val (generators i) = h.val (generators i)) : g = h := by
  have ha : g.val a = h.val a := he 0
  have hb : g.val b = h.val b := he 1
  have hc : g.val c = h.val c := he 2
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply frameBasis.ext
  intro i
  simp only [frameBasis_apply, LinearEquiv.coe_coe]
  fin_cases i <;> simp [frame, ha, hb, hc]

private theorem signs_realized : ∀ r : Fin 3 → ZMod 3, (∀ i, r i ≠ 0) →
    ∃ p : Parameters, ∀ i, sign p (generatorIndex i) = r i := by decide +kernel

/-- The new embedded eight is its own ambient centralizer. -/
theorem centralizer_elementary :
    Subgroup.centralizer (elementary : Set (Model (ZMod 3))) = elementary := by
  apply le_antisymm
  · intro g hg
    have hs (i : Fin 3) : ∃ r : ZMod 3, r ≠ 0 ∧ g.val (generators i) = r • generators i := by
      have hx (p : Parameters) : action p (g.val (frame (generatorIndex i))) =
          sign p (generatorIndex i) • g.val (frame (generatorIndex i)) := by
        have hc : embedding p * g = g * embedding p :=
          Subgroup.mem_centralizer_iff.mp hg _ ⟨p, rfl⟩
        have he := congrArg (fun t : Model (ZMod 3) => t.val (frame (generatorIndex i))) hc
        change action p (g.val (frame (generatorIndex i))) =
          g.val ((embedding p).val (frame (generatorIndex i))) at he
        simpa only [embedding_frame, map_smul] using he
      obtain ⟨r, hr⟩ := character_line (generatorIndex i) _ hx
      rw [frame_generatorIndex] at hr
      refine ⟨r, ?_, hr⟩
      intro hzero
      have he : g.val (generators i) = g.val 0 := by simpa [hzero] using hr
      have hn := frame_ne_zero (generatorIndex i)
      rw [frame_generatorIndex] at hn
      exact hn (g.val.injective he)
    choose r hr he using hs
    obtain ⟨p,hp⟩ := signs_realized r hr
    refine ⟨p, ext_generators (fun i => ?_)⟩
    rw [← frame_generatorIndex, embedding_frame, hp, frame_generatorIndex]
    exact (he i).symm
  · rintro _ ⟨p,rfl⟩ _ ⟨q,rfl⟩
    change embedding q * embedding p = embedding p * embedding q
    rw [← map_mul, ← map_mul, mul_comm]



/-- The actual ambient normalizer of the Cayley-frame eight. -/
def normalizer : Subgroup (Model (ZMod 3)) := Subgroup.normalizer (elementary : Set (Model (ZMod 3)))

/-- The new normalizer is genuinely two-local, witnessed by the embedded eight. -/
theorem normalizer_isTwoLocal : IsTwoLocal normalizer := by
  have hE : elementary ≠ ⊥ := by
    intro h
    have he := card_elementary
    simp [h] at he
  exact ⟨elementary, hE, IsElementaryAbelian.isPGroup 2 _, rfl⟩

/-- The intrinsic two-core of the new normalizer is self-centralizing. -/
theorem normalizer_centralizer_pCore :
    Subgroup.centralizer (pCore 2 normalizer : Set normalizer) ≤ pCore 2 normalizer := by
  let E := elementary.subgroupOf normalizer
  have hEN : elementary ≤ normalizer := elementary.le_normalizer
  have hnormal : E.Normal := Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  have hp : IsPGroup 2 E := (IsElementaryAbelian.isPGroup 2 elementary).comap_subtype
  have hcore : E ≤ pCore 2 normalizer := le_sSup ⟨hnormal, hp⟩
  intro g hg
  apply hcore
  change g.val ∈ elementary
  rw [← centralizer_elementary]
  intro a ha
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hg
    ⟨a, hEN ha⟩ (hcore ha))

/-- Conjugation embeds the normalizer modulo the eight into its automorphism group. -/
theorem card_normalizer_dvd_1344 : Nat.card normalizer ∣ 1344 := by
  have hker : Nat.card elementary.normalizerMonoidHom.ker = 8 := by
    rw [Subgroup.normalizerMonoidHom_ker, centralizer_elementary]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe elementary.le_normalizer).toEquiv).trans
      card_elementary
  have hd : Nat.card elementary.normalizerMonoidHom.range ∣ 168 := by
    rw [← card_mulAut_of_elementary_eight elementary card_elementary]
    exact elementary.normalizerMonoidHom.range.card_subgroup_dvd_card
  change Nat.card (Subgroup.normalizer (elementary : Set (Model (ZMod 3)))) ∣ 1344
  rw [← elementary.normalizerMonoidHom.ker.card_mul_index, Subgroup.index_ker, hker]
  exact Nat.mul_dvd_mul_left 8 hd

/-- The divisibility bound required by the local three-rank calculation. -/
theorem three_cube_not_dvd_card_normalizer : ¬ 3^3 ∣ Nat.card normalizer := by
  intro h
  exact (by decide : ¬ 3^3 ∣ 1344) (h.trans card_normalizer_dvd_1344)

end Atlas.G2.TernaryLocals.CayleyEight
