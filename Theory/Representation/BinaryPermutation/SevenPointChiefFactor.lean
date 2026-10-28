module

public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.AlternatingFiveLinearTwoObstruction

/-!
# The five-point chief factor inside the seven-point binary core

Partition seven letters into five and two. The alternating group on the first
five fixes the weight-two vector on the last two and centralizes their external
transposition. Its four-dimensional permutation core embeds by extension by
zero. Every invariant subspace of this core is zero or the whole core.

In a six-dimensional space, this simple submodule lies in every invariant
subspace of dimension at least four, and survives quotienting by an invariant
subspace of dimension at most two. Thus an actual natural SL₂ section cannot
occur for the same A₅ action: the resulting injection contradicts the cubic
fixed-vector calculation in `AlternatingFiveLinearTwoObstruction`.

This constructs the chief-factor comparison used in both six-dimensional
branches of Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Lemma 16.4.7, printed p.1187. Recognition of an arbitrary action as this
seven-point action is separate. The transposition is external to A₇.
-/

@[expose] public section

open Module Matrix
open scoped MatrixGroups
namespace BinaryPermutation.SevenPointChiefFactor
open BinaryPermutation

abbrev Seven := Fin 5 ⊕ Fin 2
abbrev Five := alternatingGroup (Fin 5)

def fivePerm : Five →* Equiv.Perm Seven where
  toFun a := Equiv.sumCongr a.val (Equiv.refl _)
  map_one' := by ext i; cases i <;> rfl
  map_mul' _ _ := by ext i; cases i <;> rfl

def fiveAlternating : Five →* alternatingGroup Seven where
  toFun a := ⟨fivePerm a, by
    rw [Equiv.Perm.mem_alternatingGroup]
    change Equiv.Perm.sign (Equiv.sumCongr a.val (1 : Equiv.Perm (Fin 2))) = 1
    rw [Equiv.Perm.sign_sumCongr, (Equiv.Perm.mem_alternatingGroup.mp a.property), map_one, mul_one]⟩
  map_one' := by apply Subtype.ext; exact fivePerm.map_one
  map_mul' a b := by apply Subtype.ext; exact fivePerm.map_mul a b

theorem fivePerm_injective : Function.Injective fivePerm := by
  intro a b h
  apply Subtype.ext
  apply Equiv.ext
  intro i
  exact Sum.inl.inj (show Sum.inl (a.val i) = Sum.inl (b.val i) from
    Equiv.congr_fun h (Sum.inl i))

def externalTransposition : Equiv.Perm Seven :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.swap 0 1)

theorem fivePerm_commutes_externalTransposition (a : Five) :
    Commute (fivePerm a) externalTransposition := by
  apply Equiv.ext
  intro i
  cases i <;> rfl

theorem externalTransposition_not_mem_alternating :
    externalTransposition ∉ alternatingGroup Seven := by
  simp [externalTransposition, Equiv.Perm.mem_alternatingGroup]

def markedVector : core Seven :=
  ⟨Sum.elim (fun _ => 0) (fun _ => 1), by
    rw [mem_core, Fintype.sum_sum_type]
    decide⟩

theorem markedVector_support :
    {i : Seven | markedVector.val i ≠ 0} = {Sum.inr 0, Sum.inr 1} := by
  ext i
  cases i with
  | inl i => simp [markedVector]
  | inr i => fin_cases i <;> decide

theorem fivePerm_fixes_markedVector (a : Five) :
    coreRepresentation Seven (fivePerm a) markedVector = markedVector := by
  apply Subtype.ext
  ext i
  cases i <;> rfl

/-- The external transposition is the rank-one operator with marked center
and with axis given by equality of its two moved coordinates. -/
theorem externalTransposition_formula (v : core Seven) :
    coreRepresentation Seven externalTransposition v =
      v + (v.val (Sum.inr 0) + v.val (Sum.inr 1)) • markedVector := by
  apply Subtype.ext
  funext i
  cases i with
  | inl i =>
    change v.val (Sum.inl i) = v.val (Sum.inl i) + _ * 0
    simp
  | inr i =>
    fin_cases i
    · change v.val (Sum.inr 1) = v.val (Sum.inr 0) +
        (v.val (Sum.inr 0) + v.val (Sum.inr 1)) * 1
      simp [← add_assoc, CharTwo.add_self_eq_zero]
    · change v.val (Sum.inr 0) = v.val (Sum.inr 1) +
        (v.val (Sum.inr 0) + v.val (Sum.inr 1)) * 1
      simp [add_left_comm, CharTwo.add_self_eq_zero]

def fiveCoreEmbedding : core (Fin 5) →ₗ[ZMod 2] core Seven where
  toFun v := ⟨Sum.elim v.val (fun _ => 0), by
    rw [mem_core, Fintype.sum_sum_type]
    simpa only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, add_zero] using
      (mem_core (Fin 5) v.val).mp v.property⟩
  map_add' _ _ := by apply Subtype.ext; ext i; cases i <;> rfl
  map_smul' _ _ := by apply Subtype.ext; ext i; cases i <;> rfl

theorem fiveCoreEmbedding_injective : Function.Injective fiveCoreEmbedding := by
  intro v w h
  apply Subtype.ext
  ext i
  exact congrArg (fun u : core Seven => u.val (Sum.inl i)) h

theorem fiveCoreEmbedding_equivariant (a : Five) (v : core (Fin 5)) :
    fiveCoreEmbedding (coreRepresentation (Fin 5) a.val v) =
      coreRepresentation Seven (fivePerm a) (fiveCoreEmbedding v) := by
  apply Subtype.ext
  ext i
  cases i <;> rfl

theorem fiveCore_simple (P : Submodule (ZMod 2) (core (Fin 5)))
    (hP : ∀ a : Five, ∀ v ∈ P, coreRepresentation (Fin 5) a.val v ∈ P) :
    P = ⊥ ∨ P = ⊤ := by
  let W := P.map (core (Fin 5)).subtype
  have hW : ∀ a : Five, ∀ v ∈ W, representation (Fin 5) a.val v ∈ W := by
    rintro a _ ⟨v, hv, rfl⟩
    exact ⟨coreRepresentation (Fin 5) a.val v, hP a v hv, rfl⟩
  rcases invariant_le_constants_or_core_le (by decide : 5 ≤ Fintype.card (Fin 5)) W hW with h | h
  · left
    apply le_antisymm _ bot_le
    intro v hv
    have hw : v.val ∈ W := ⟨v, hv, rfl⟩
    have hz : v.val = 0 := (Submodule.disjoint_def.mp
      (core_isCompl_constants (Fin 5) (by decide)).disjoint) v.val v.property (h hw)
    exact Subtype.ext hz
  · right
    apply le_antisymm le_top
    intro v _
    obtain ⟨u, hu, huv⟩ := h v.property
    exact (Subtype.ext huv : u = v) ▸ hu

theorem fiveCore_finrank : finrank (ZMod 2) (core (Fin 5)) = 4 := by
  simpa using finrank_core (Fin 5)

theorem sevenCore_finrank : finrank (ZMod 2) (core Seven) = 6 := by
  simpa using finrank_core Seven

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- An invariant section of dimension at least four in a six-dimensional
space contains every embedded copy of the four-dimensional simple A₅ core. -/
theorem fiveCore_range_le (ρ : Representation (ZMod 2) Five V)
    (j : core (Fin 5) →ₗ[ZMod 2] V) (hj : Function.Injective j)
    (hact : ∀ a v, j (coreRepresentation (Fin 5) a.val v) = ρ a (j v))
    (hdim : finrank (ZMod 2) V = 6)
    (W : Submodule (ZMod 2) V) (hWdim : 4 ≤ finrank (ZMod 2) W)
    (hW : ∀ a v, v ∈ W → ρ a v ∈ W) : LinearMap.range j ≤ W := by
  rcases fiveCore_simple (W.comap j) (by
    intro a v hv
    change j (coreRepresentation (Fin 5) a.val v) ∈ W
    rw [hact]
    exact hW a (j v) hv) with h | h
  · have hd : Disjoint (LinearMap.range j) W := by
      apply Submodule.disjoint_def.mpr
      rintro v ⟨u, rfl⟩ hu
      have hu' : u ∈ W.comap j := hu
      rw [h] at hu'
      rw [show u = 0 from hu', map_zero]
    have hh := Submodule.finrank_add_finrank_le_of_disjoint hd
    rw [LinearMap.finrank_range_of_inj hj, fiveCore_finrank, hdim] at hh
    omega
  · rintro v ⟨u, rfl⟩
    have hu : u ∈ W.comap j := by rw [h]; trivial
    exact hu

/-- The embedded five-point chief factor survives a lower section of dimension
at most two. This constructs the needed injection; it is not an assumed
identification of the two four-dimensional modules. -/
theorem fiveCore_section_injective (ρ : Representation (ZMod 2) Five V)
    (j : core (Fin 5) →ₗ[ZMod 2] V) (hj : Function.Injective j)
    (hact : ∀ a v, j (coreRepresentation (Fin 5) a.val v) = ρ a (j v))
    (W : Submodule (ZMod 2) V) (hjW : LinearMap.range j ≤ W)
    (U : Submodule (ZMod 2) W) (hUdim : finrank (ZMod 2) U ≤ 2)
    (hW : ∀ a v, v ∈ W → ρ a v ∈ W)
    (hU : ∀ a (w : W), w ∈ U → (⟨ρ a w, hW a w w.property⟩ : W) ∈ U) :
    Function.Injective (U.mkQ.comp (j.codRestrict W (fun v => hjW ⟨v, rfl⟩))) := by
  let k := j.codRestrict W (fun v => hjW ⟨v, rfl⟩)
  have hk : Function.Injective k := fun _ _ h => hj (congrArg Subtype.val h)
  have hkact (a : Five) (v : core (Fin 5)) :
      k (coreRepresentation (Fin 5) a.val v) = ⟨ρ a (k v), hW a _ (k v).property⟩ :=
    Subtype.ext (hact a v)
  have hinv : ∀ (a : Five) v, v ∈ U.comap k → coreRepresentation (Fin 5) a.val v ∈ U.comap k := by
    intro a v hv
    change k (coreRepresentation (Fin 5) a.val v) ∈ U
    rw [hkact]
    exact hU a (k v) hv
  rcases fiveCore_simple (U.comap k) hinv with h | h
  · apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    exact h
  · have hh : LinearMap.range k ≤ U := by
      rintro _ ⟨v, rfl⟩
      have hv : v ∈ U.comap k := by rw [h]; trivial
      exact hv
    have hle := Submodule.finrank_mono hh
    rw [LinearMap.finrank_range_of_inj hk, fiveCore_finrank] at hle
    omega

/-- The four-dimensional natural section over a four-element field leaves
at most two central dimensions in the six-dimensional permutation core. -/
theorem plane_section_bounds
    (W : Submodule (ZMod 2) (core Seven)) (U : Submodule (ZMod 2) W)
    {F : Type*} [Field F] (hF : Nat.card F = 4)
    (e : (W ⧸ U) ≃+ (Fin 2 → F)) :
    4 ≤ finrank (ZMod 2) W ∧ finrank (ZMod 2) U ≤ 2 := by
  have hc := Nat.card_congr e.toEquiv
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    Nat.card_fun, hF] at hc
  have hpow : 2 ^ finrank (ZMod 2) (W ⧸ U) = 2 ^ 4 := by simpa using hc
  have hd := Nat.pow_right_injective (by decide : 2 ≤ 2) hpow
  have htotal := U.finrank_quotient_add_finrank
  have hWle := Submodule.finrank_le W
  rw [sevenCore_finrank] at hWle
  omega

/-- In the seven-point core, the actual four-dimensional five-point chief
factor cannot coexist with a natural SL₂ section under a faithful A₅ action. -/
theorem sevenCore_no_natural_section
    {F : Type*} [Field F] [CharP F 2]
    (f : Five →* SL(2,F)) (hf : Function.Injective f)
    (W : Submodule (ZMod 2) (core Seven))
    (hWdim : 4 ≤ finrank (ZMod 2) W)
    (hW : ∀ a v, v ∈ W → coreRepresentation Seven (fivePerm a) v ∈ W)
    (U : Submodule (ZMod 2) W) (hUdim : finrank (ZMod 2) U ≤ 2)
    (hU : ∀ a (w : W), w ∈ U →
      (⟨coreRepresentation Seven (fivePerm a) w, hW a w w.property⟩ : W) ∈ U)
    (e : (W ⧸ U) ≃+ (Fin 2 → F))
    (hsection : ∀ a (w : W),
      e (U.mkQ ⟨coreRepresentation Seven (fivePerm a) w, hW a w w.property⟩) =
        (f a).val *ᵥ e (U.mkQ w)) : False := by
  let ρ := (coreRepresentation Seven).comp fivePerm
  have hjW := fiveCore_range_le ρ fiveCoreEmbedding fiveCoreEmbedding_injective
    fiveCoreEmbedding_equivariant sevenCore_finrank W hWdim hW
  let k := fiveCoreEmbedding.codRestrict W (fun v => hjW ⟨v, rfl⟩)
  let q := U.mkQ.comp k
  have hq : Function.Injective q := fiveCore_section_injective ρ fiveCoreEmbedding
    fiveCoreEmbedding_injective fiveCoreEmbedding_equivariant W hjW U hUdim hW hU
  apply AlternatingFiveLinearTwo.no_equivariant_core_injection f hf
    (e.toAddMonoidHom.comp q.toAddMonoidHom) (e.injective.comp hq)
  intro a v
  change e (U.mkQ (k (coreRepresentation (Fin 5) a.val v))) =
    (f a).val *ᵥ e (U.mkQ (k v))
  have hk : k (coreRepresentation (Fin 5) a.val v) =
      ⟨coreRepresentation Seven (fivePerm a) (k v), hW a _ (k v).property⟩ :=
    Subtype.ext (fiveCoreEmbedding_equivariant a v)
  rw [hk]
  exact hsection a (k v)

end BinaryPermutation.SevenPointChiefFactor
