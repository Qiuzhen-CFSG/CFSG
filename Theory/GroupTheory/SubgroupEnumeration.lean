module

public import Theory.GroupTheory.WordSubgroup
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Order.Atoms

/-!
# Soundness of subgroup extension certificates

A family containing the trivial subgroup and closed, up to conjugacy, under
adjoining one element represents every subgroup of a finite group. The proof
is induction on a finite generating set, transporting each extension through
the conjugation supplied by the previous step. No distinctness of the entries
is needed; finiteness of the family is needed only by concrete checking code.

Right cosets `K * r` and double cosets `K * r * K` give identical extensions.
Their coverage must be proved, and extension equalities require both
containments. The word interfaces below reduce these obligations to equations
between evaluated words and actual group elements. Finite instances of these
equations can be proved by kernel reduction (`decide`).

Source: the elementary subgroup-lattice enumeration argument (successive
adjunction of generators); word evaluation is provided by
`Theory.GroupTheory.WordSubgroup`. This module is independent of any matrix
model or externally generated enumeration.
-/

namespace Theory.GroupTheory.SubgroupEnumeration

variable {G : Type*} [Group G] {ι : Type*}

/-- The subgroup `H` is conjugate to an actual entry of the family `K`.
The convention is `g H g⁻¹ = K i`. -/
@[expose] public def Represented (K : ι → Subgroup G) (H : Subgroup G) : Prop :=
  ∃ i g, H.map (MulAut.conj g).toMonoidHom = K i

private theorem map_conj_map (H : Subgroup G) (g h : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      H.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- The mathematical obligations for a subgroup extension enumeration. -/
public structure ExtensionClosed (K : ι → Subgroup G) : Prop where
  bot : ∃ i, K i = ⊥
  step : ∀ i x, Represented K (K i ⊔ Subgroup.zpowers x)

/-- The core argument also works in infinite groups for finite generating sets. -/
public theorem ExtensionClosed.represents_closure (K : ι → Subgroup G)
    (cert : ExtensionClosed K) {s : Set G} (hs : s.Finite) :
    Represented K (Subgroup.closure s) := by
  classical
  induction s, hs using Set.Finite.induction_on with
  | empty =>
      obtain ⟨i, hi⟩ := cert.bot
      exact ⟨i, 1, by simp [Subgroup.closure_empty, hi]⟩
  | @insert x s hx hs ih =>
      obtain ⟨i, g, hg⟩ := ih
      obtain ⟨j, h, hh⟩ := cert.step i ((MulAut.conj g) x)
      refine ⟨j, h * g, ?_⟩
      rw [← map_conj_map]
      rw [← Set.singleton_union, Subgroup.closure_union, Subgroup.map_sup,
        ← Subgroup.zpowers_eq_closure, MonoidHom.map_zpowers, hg, sup_comm]
      exact hh

/-- Soundness of an enumeration closed under all one-element extensions.
In particular this applies to a finite family indexed by `Fin n`. -/
public theorem ExtensionClosed.complete [Finite G] (K : ι → Subgroup G)
    (cert : ExtensionClosed K) (H : Subgroup G) : Represented K H := by
  simpa only [Subgroup.closure_eq] using
    cert.represents_closure K (Set.toFinite (H : Set G))

/-- If every enumerated node is either top or lies in a candidate subgroup,
every proper subgroup lies in a conjugate of a candidate. The top alternative
is excluded using injectivity of conjugation, not by comparing subgroup orders. -/
public theorem ExtensionClosed.proper_le_conjugate [Finite G] {κ : Type*}
    (K : ι → Subgroup G) (cert : ExtensionClosed K) (C : κ → Subgroup G)
    (bound : ∀ i, K i = ⊤ ∨ ∃ j, K i ≤ C j)
    (H : Subgroup G) (hH : H ≠ ⊤) :
    ∃ j g, H ≤ (C j).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨i, g, hg⟩ := cert.complete K H
  rcases bound i with hi | ⟨j, hj⟩
  · exfalso
    apply hH
    apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective
    rw [hg, hi, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]
  · refine ⟨j, g⁻¹, ?_⟩
    intro x hx
    have hmem : (MulAut.conj g) x ∈ K i := by
      rw [← hg]
      exact Subgroup.mem_map_of_mem _ hx
    refine Subgroup.mem_map.mpr ⟨(MulAut.conj g) x, hj hmem, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

/-- Adjoining an element already present leaves a subgroup unchanged. -/
public theorem extension_eq_self {K : Subgroup G} {x : G} (hx : x ∈ K) :
    K ⊔ Subgroup.zpowers x = K :=
  sup_eq_left.mpr (Subgroup.zpowers_le.mpr hx)

/-- Only extensions by elements outside the current subgroup need checking. -/
public theorem extensionClosed_of_outside (K : ι → Subgroup G)
    (hbot : ∃ i, K i = ⊥)
    (hstep : ∀ i x, x ∉ K i → Represented K (K i ⊔ Subgroup.zpowers x)) :
    ExtensionClosed K := by
  classical
  refine ⟨hbot, fun i x => ?_⟩
  by_cases hx : x ∈ K i
  · refine ⟨i, 1, ?_⟩
    rw [extension_eq_self hx]
    have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext y
      simp
    rw [hid, Subgroup.map_id]
  · exact hstep i x hx

/-- Left multiplication by a member of `K` preserves the extension. -/
public theorem extension_mul_left (K : Subgroup G) {a : G} (ha : a ∈ K) (x : G) :
    K ⊔ Subgroup.zpowers (a * x) = K ⊔ Subgroup.zpowers x := by
  apply le_antisymm
  · exact sup_le le_sup_left (Subgroup.zpowers_le.mpr
      ((K ⊔ Subgroup.zpowers x).mul_mem (Subgroup.mem_sup_left ha)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))))
  · refine sup_le le_sup_left (Subgroup.zpowers_le.mpr ?_)
    have h := (K ⊔ Subgroup.zpowers (a * x)).mul_mem
      (Subgroup.mem_sup_left (K.inv_mem ha)) (Subgroup.mem_sup_right (Subgroup.mem_zpowers (a * x)))
    simpa only [inv_mul_cancel_left] using h

/-- Right multiplication by a member of `K` preserves the extension. -/
public theorem extension_mul_right (K : Subgroup G) (x : G) {b : G} (hb : b ∈ K) :
    K ⊔ Subgroup.zpowers (x * b) = K ⊔ Subgroup.zpowers x := by
  apply le_antisymm
  · exact sup_le le_sup_left (Subgroup.zpowers_le.mpr
      ((K ⊔ Subgroup.zpowers x).mul_mem
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)) (Subgroup.mem_sup_left hb)))
  · refine sup_le le_sup_left (Subgroup.zpowers_le.mpr ?_)
    have h := (K ⊔ Subgroup.zpowers (x * b)).mul_mem
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers (x * b))) (Subgroup.mem_sup_left (K.inv_mem hb))
    simpa only [mul_inv_cancel_right] using h

/-- All elements of a double coset give exactly the same extension. -/
public theorem extension_double_coset (K : Subgroup G) {a b : G}
    (ha : a ∈ K) (hb : b ∈ K) (x : G) :
    K ⊔ Subgroup.zpowers (a * x * b) = K ⊔ Subgroup.zpowers x := by
  rw [extension_mul_right K _ hb, extension_mul_left K ha]

/-- Coverage by right cosets, with membership and factorization proved. -/
@[expose] public def RightCosetCover {ρ : Type*} (K : Subgroup G) (rep : ρ → G) : Prop :=
  ∀ x, ∃ r a, a ∈ K ∧ x = a * rep r

/-- Coverage by double cosets, with both factors checked in `K`. -/
@[expose] public def DoubleCosetCover {ρ : Type*} (K : Subgroup G) (rep : ρ → G) : Prop :=
  ∀ x, ∃ r a b, a ∈ K ∧ b ∈ K ∧ x = a * rep r * b

public theorem RightCosetCover.doubleCosetCover {ρ : Type*} {K : Subgroup G}
    {rep : ρ → G} (cover : RightCosetCover K rep) : DoubleCosetCover K rep := by
  intro x
  obtain ⟨r, a, ha, hx⟩ := cover x
  exact ⟨r, a, 1, ha, K.one_mem, by simpa using hx⟩

/-- Double-coset reduction of all extension checks. The representative types
may vary with the subgroup; in applications they are finite index types. -/
public theorem extensionClosed_of_doubleCosetCover (K : ι → Subgroup G)
    {ρ : ι → Type*} (rep : ∀ i, ρ i → G)
    (hbot : ∃ i, K i = ⊥)
    (cover : ∀ i, DoubleCosetCover (K i) (rep i))
    (step : ∀ i r, Represented K (K i ⊔ Subgroup.zpowers (rep i r))) :
    ExtensionClosed K := by
  refine ⟨hbot, fun i x => ?_⟩
  obtain ⟨r, a, b, ha, hb, hx⟩ := cover i x
  rw [hx, extension_double_coset (K i) ha hb]
  exact step i r

public theorem extensionClosed_of_rightCosetCover (K : ι → Subgroup G)
    {ρ : ι → Type*} (rep : ∀ i, ρ i → G)
    (hbot : ∃ i, K i = ⊥)
    (cover : ∀ i, RightCosetCover (K i) (rep i))
    (step : ∀ i r, Represented K (K i ⊔ Subgroup.zpowers (rep i r))) :
    ExtensionClosed K :=
  extensionClosed_of_doubleCosetCover K rep hbot
    (fun i => (cover i).doubleCosetCover) step

/-- Maximality can be checked solely by one-element extensions. -/
public theorem isCoatom_iff_extensions (K : Subgroup G) :
    IsCoatom K ↔ K ≠ ⊤ ∧ ∀ x, x ∉ K → K ⊔ Subgroup.zpowers x = ⊤ := by
  classical
  constructor
  · rintro ⟨hproper, hmax⟩
    refine ⟨hproper, fun x hx => hmax _ ?_⟩
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    exact hx (heq.symm ▸ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
  · rintro ⟨hproper, hstep⟩
    refine ⟨hproper, fun H hKH => ?_⟩
    obtain ⟨x, hxH, hxK⟩ := SetLike.exists_of_lt hKH
    apply top_unique
    rw [← hstep x hxK]
    exact sup_le hKH.le (Subgroup.zpowers_le.mpr hxH)

/-- Maximality checks may also be reduced to double-coset representatives. -/
public theorem isCoatom_of_doubleCosetCover {ρ : Type*} (K : Subgroup G)
    (rep : ρ → G) (hproper : K ≠ ⊤) (cover : DoubleCosetCover K rep)
    (step : ∀ r, rep r ∉ K → K ⊔ Subgroup.zpowers (rep r) = ⊤) : IsCoatom K := by
  apply (isCoatom_iff_extensions K).mpr
  refine ⟨hproper, fun x hx => ?_⟩
  obtain ⟨r, a, b, ha, hb, hxab⟩ := cover x
  have hr : rep r ∉ K := by
    intro hr
    exact hx (hxab ▸ K.mul_mem (K.mul_mem ha hr) hb)
  rw [hxab, extension_double_coset K ha hb]
  exact step r hr

/-- A word in elements of any subgroup stays in that subgroup. -/
public theorem evalWord_mem {n : Nat} (gen : Fin n → G) (H : Subgroup G)
    (hgen : ∀ i, gen i ∈ H) (w : List (Fin n)) : evalWord gen w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons i w ih => exact H.mul_mem (hgen i) ih

/-- Generator membership proves containment of a word subgroup in any subgroup. -/
public theorem wordSubgroup_le {n : Nat} (gen : Fin n → G)
    (invOf : Fin n → Fin n) (hInv : ∀ i, gen (invOf i) = (gen i)⁻¹)
    (H : Subgroup G) (hgen : ∀ i, gen i ∈ H) : wordSubgroup gen invOf hInv ≤ H := by
  rintro x ⟨w, rfl⟩
  exact evalWord_mem gen H hgen w

/-- Adjoin an inverse letter for every generator. -/
@[expose] public def symmGen {n : Nat} (gen : Fin n → G) : Fin (n + n) → G :=
  Fin.addCases gen (fun i => (gen i)⁻¹)

/-- Swap the original and inverse halves of the alphabet. -/
@[expose] public def symmInv {n : Nat} : Fin (n + n) → Fin (n + n) :=
  Fin.addCases (Fin.natAdd n) (Fin.castAdd n)

public theorem symmGen_inv {n : Nat} (gen : Fin n → G) : ∀ i,
    symmGen gen (symmInv i) = (symmGen gen i)⁻¹ := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [symmGen, symmInv, Fin.addCases_left, Fin.addCases_right, inv_inv]

/-- The inverse-closed word alphabet generates precisely the usual closure. -/
public theorem symm_wordSubgroup_eq_closure {n : Nat} (gen : Fin n → G) :
    wordSubgroup (symmGen gen) symmInv (symmGen_inv gen) =
      Subgroup.closure (Set.range gen) := by
  apply le_antisymm
  · apply wordSubgroup_le
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [symmGen, Fin.addCases_left]
      apply Subgroup.subset_closure
      exact ⟨j, rfl⟩
    · simpa only [symmGen, Fin.addCases_right] using
        (Subgroup.closure (Set.range gen)).inv_mem (Subgroup.subset_closure ⟨j, rfl⟩)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨[Fin.castAdd n j], by simp [evalWord, symmGen]⟩

/-- The alphabet for an extension consists of the old generators and `x, x⁻¹`.
The inverse letter allows short reverse witnesses even when `x` has large order. -/
@[expose] public def extensionGen {n : Nat} (gen : Fin n → G) (x : G) : Fin (n + 2) → G :=
  Fin.addCases gen (fun i => if i = 0 then x else x⁻¹)

public theorem extensionGen_mem {n : Nat} (gen : Fin n → G)
    (invOf : Fin n → Fin n) (hInv : ∀ i, gen (invOf i) = (gen i)⁻¹)
    (x : G) (i : Fin (n + 2)) :
    extensionGen gen x i ∈ wordSubgroup gen invOf hInv ⊔ Subgroup.zpowers x := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · apply Subgroup.mem_sup_left
    exact ⟨[j], by simp [extensionGen, evalWord]⟩
  · simp only [extensionGen, Fin.addCases_right]
    split
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    · exact Subgroup.mem_sup_right ((Subgroup.zpowers x).inv_mem (Subgroup.mem_zpowers x))

/-- Finite word data for both directions of an extension equality. -/
public structure ExtensionWords (n m : Nat) where
  forward : Fin n → List (Fin m)
  newGenerator : List (Fin m)
  backward : Fin m → List (Fin (n + 2))

/-- Only finitely many group equations are checked. Taking `f = MulAut.conj g`
checks conjugacy of the *exact* extension with the target word subgroup.
This predicate has a computable decision procedure whenever equality in `G` does. -/
@[expose] public def ExtensionWords.Valid {n m : Nat} (data : ExtensionWords n m)
    (gen : Fin n → G) (target : Fin m → G) (x : G) (f : G →* G) : Prop :=
  (∀ i, evalWord target (data.forward i) = f (gen i)) ∧
  evalWord target data.newGenerator = f x ∧
  ∀ j, evalWord (fun i => f (extensionGen gen x i)) (data.backward j) = target j

public instance instDecidableExtensionWordsValid {n m : Nat} [DecidableEq G] (data : ExtensionWords n m)
    (gen : Fin n → G) (target : Fin m → G) (x : G) (f : G →* G) :
    Decidable (data.Valid gen target x f) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop)))

/-- Word witnesses in both directions prove exact equality, also after mapping
by a homomorphism (in particular by conjugation). -/
public theorem ExtensionWords.sound {n m : Nat} (data : ExtensionWords n m)
    (gen : Fin n → G) (invOf : Fin n → Fin n)
    (hInv : ∀ i, gen (invOf i) = (gen i)⁻¹)
    (target : Fin m → G) (targetInv : Fin m → Fin m)
    (hTargetInv : ∀ j, target (targetInv j) = (target j)⁻¹)
    (x : G) (f : G →* G) (valid : data.Valid gen target x f) :
    (wordSubgroup gen invOf hInv ⊔ Subgroup.zpowers x).map f =
      wordSubgroup target targetInv hTargetInv := by
  obtain ⟨hf, hx, hb⟩ := valid
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    refine sup_le (wordSubgroup_le gen invOf hInv _ (fun i => ?_))
      (Subgroup.zpowers_le.mpr ?_)
    · change f (gen i) ∈ wordSubgroup target targetInv hTargetInv
      exact ⟨data.forward i, hf i⟩
    · change f x ∈ wordSubgroup target targetInv hTargetInv
      exact ⟨data.newGenerator, hx⟩
  · apply wordSubgroup_le target targetInv hTargetInv
    intro j
    rw [← hb j]
    exact evalWord_mem _ _
      (fun i => Subgroup.mem_map_of_mem f (extensionGen_mem gen invOf hInv x i)) _

/-- Explicit factorization data for a double-coset cover by a word subgroup. -/
public structure DoubleCosetWords (G : Type*) (n r : Nat) where
  index : G → Fin r
  left : G → List (Fin n)
  right : G → List (Fin n)

@[expose] public def DoubleCosetWords.Valid {n r : Nat} (data : DoubleCosetWords G n r)
    (gen : Fin n → G) (rep : Fin r → G) : Prop :=
  ∀ x, x = evalWord gen (data.left x) * rep (data.index x) * evalWord gen (data.right x)

public instance instDecidableDoubleCosetWordsValid {n r : Nat} [Fintype G] [DecidableEq G] (data : DoubleCosetWords G n r)
    (gen : Fin n → G) (rep : Fin r → G) : Decidable (data.Valid gen rep) :=
  inferInstanceAs (Decidable (∀ x, x = evalWord gen (data.left x) *
    rep (data.index x) * evalWord gen (data.right x)))

public theorem DoubleCosetWords.sound {n r : Nat} (data : DoubleCosetWords G n r)
    (gen : Fin n → G) (invOf : Fin n → Fin n)
    (hInv : ∀ i, gen (invOf i) = (gen i)⁻¹) (rep : Fin r → G)
    (valid : data.Valid gen rep) : DoubleCosetCover (wordSubgroup gen invOf hInv) rep := by
  intro x
  exact ⟨data.index x, evalWord gen (data.left x), evalWord gen (data.right x),
    evalWord_mem_wordSubgroup gen invOf hInv _, evalWord_mem_wordSubgroup gen invOf hInv _,
    valid x⟩

/-- A right-coset transition table. `n` is the number of ambient generators,
`m` the number of subgroup generators, and `r` the number of representatives.
Surplus or repeated representatives are harmless. -/
public structure RightCosetTable (n m r : Nat) where
  base : Fin r
  next : Fin r → Fin n → Fin r
  factor : Fin r → Fin n → List (Fin m)

/-- Finitely many equations suffice for coverage: the identity has a row,
and every row times every ambient generator has a checked successor. -/
@[expose] public def RightCosetTable.Valid {n m r : Nat} (data : RightCosetTable n m r)
    (ambient : Fin n → G) (gen : Fin m → G) (rep : Fin r → G) : Prop :=
  rep data.base = 1 ∧ ∀ a i,
    rep a * ambient i = evalWord gen (data.factor a i) * rep (data.next a i)

public instance instDecidableRightCosetTableValid {n m r : Nat} [DecidableEq G] (data : RightCosetTable n m r)
    (ambient : Fin n → G) (gen : Fin m → G) (rep : Fin r → G) :
    Decidable (data.Valid ambient gen rep) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop)))

/-- A checked transition table covers the group, provided the ambient alphabet
really generates the group. This is proved by induction on ambient words. -/
public theorem RightCosetTable.sound {n m r : Nat} (data : RightCosetTable n m r)
    (ambient : Fin n → G) (ambientInv : Fin n → Fin n)
    (hAmbientInv : ∀ i, ambient (ambientInv i) = (ambient i)⁻¹)
    (hAmbient : wordSubgroup ambient ambientInv hAmbientInv = ⊤)
    (gen : Fin m → G) (invOf : Fin m → Fin m)
    (hInv : ∀ i, gen (invOf i) = (gen i)⁻¹) (rep : Fin r → G)
    (valid : data.Valid ambient gen rep) : RightCosetCover (wordSubgroup gen invOf hInv) rep := by
  let K := wordSubgroup gen invOf hInv
  have words : ∀ w : List (Fin n), ∃ a k, k ∈ K ∧ evalWord ambient w = k * rep a := by
    intro w
    induction w using List.reverseRecOn with
    | nil =>
        exact ⟨data.base, 1, K.one_mem, by simp [evalWord, valid.1]⟩
    | append_singleton w i ih =>
        obtain ⟨a, k, hk, hw⟩ := ih
        refine ⟨data.next a i, k * evalWord gen (data.factor a i),
          K.mul_mem hk (evalWord_mem_wordSubgroup gen invOf hInv _), ?_⟩
        rw [evalWord_append, hw]
        simp only [evalWord, mul_one]
        rw [mul_assoc, valid.2 a i, ← mul_assoc]
  intro x
  have hx : x ∈ wordSubgroup ambient ambientInv hAmbientInv := by rw [hAmbient]; trivial
  obtain ⟨w, rfl⟩ := hx
  exact words w

end Theory.GroupTheory.SubgroupEnumeration
