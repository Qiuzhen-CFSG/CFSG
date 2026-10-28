module
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Tactic

/-!
# The centralizer of two identical binary natural modules

Elementary transvections force each additive intertwiner of the natural
SL_n(2) module, n≥2, to be scalar. Applying this to the four blocks of a
doubled endomorphism gives its unique two-by-two multiplicity matrix.
Invertibility is preserved in both directions, so the full centralizer
is GL₂(2), with an actual isomorphism to S₃ and order six.

The matrix argument extends `SL3DoubledNaturalOffenders.Centralizer` to
arbitrary binary degree. Its source application is the cubic-actor step
in Aschbacher--Smith, original 12.2.25, printed p.806; both natural copies
must carry the same marked action.
-/

@[expose] public section
namespace Representation.BinaryDoubledNatural
open Matrix
variable (n : ℕ) [NeZero n]
abbrev Natural := Fin n → (ZMod 2)
abbrev Space := Fin 2 → Natural n
abbrev SL := SpecialLinearGroup (Fin n) (ZMod 2)
abbrev MultiplicitySL := SpecialLinearGroup (Fin 2) (ZMod 2)
abbrev Ambient := (Module.End (ZMod 2) (Space n))ˣ

/-- The identical natural marking on the two copies. -/
def representation : Representation (ZMod 2) (SL n) (Space n) where
  toFun g :=
    { toFun := fun v i => g.val.mulVec (v i)
      map_add' v w := by funext i; exact Matrix.mulVec_add g.val (v i) (w i)
      map_smul' a v := by funext i; exact Matrix.mulVec_smul g.val a (v i) }
  map_one' := by apply LinearMap.ext; intro v; funext i; exact Matrix.one_mulVec (v i)
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext i
    exact (Matrix.mulVec_mulVec (v i) g.val h.val).symm

omit [NeZero n] in
@[simp] theorem representation_apply (g : SL n) (v : Space n) (i : Fin 2) :
    representation n g v i = g.val.mulVec (v i) := rfl

/-- The actual special-linear image in binary invertible operators. -/
def component : Subgroup (Ambient n) := (representation n).asGroupHom.range

/-- The full binary normalizer of the marked component. -/
def normalizer : Subgroup (Ambient n) := Subgroup.normalizer (component n)

/-- Evaluation by binary invertible operators. -/
def action : Representation (ZMod 2) (Ambient n) (Space n) := Units.coeHom _

omit [NeZero n] in
@[simp] theorem action_component (g : SL n) :
    action n ((representation n).asGroupHom g) = representation n g := rfl

omit [NeZero n] in
theorem action_injective : Function.Injective (action n) := fun _ _ h => Units.ext h

omit [NeZero n] in
theorem representation_injective : Function.Injective (representation n) := by
  intro g h he
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  exact congrArg (fun f : Module.End (ZMod 2) (Space n) => f (fun _ => v) 0) he

/-- Two by two field matrices acting on the multiplicity indices. -/
def multiplicity (c : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Module.End (ZMod 2) (Space n) where
  toFun v i := c i 0 • v 0 + c i 1 • v 1
  map_add' v w := by ext i j; simp; ring
  map_smul' a v := by
    ext i j
    simp only [Pi.smul_apply, Pi.add_apply]
    rw [smul_comm (c i 0) a, smul_comm (c i 1) a, smul_add]
    rfl

omit [NeZero n] in
@[simp] theorem multiplicity_apply (c : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (v : Space n) (i : Fin 2) :
    multiplicity n c v i = c i 0 • v 0 + c i 1 • v 1 := rfl

omit [NeZero n] in
@[simp] theorem multiplicity_one : multiplicity n 1 = 1 := by
  apply LinearMap.ext
  intro v
  funext i j
  fin_cases i <;> simp [multiplicity, Matrix.one_apply]

omit [NeZero n] in
@[simp] theorem multiplicity_mul (c d : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    multiplicity n (c * d) = multiplicity n c * multiplicity n d := by
  apply LinearMap.ext
  intro v
  funext i j
  simp [multiplicity, Module.End.mul_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ring

omit [NeZero n] in
@[simp] theorem multiplicity_zero : multiplicity n 0 = 0 := by
  apply LinearMap.ext
  intro v
  funext i j
  simp [multiplicity]

omit [NeZero n] in
@[simp] theorem multiplicity_add (c d : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    multiplicity n (c + d) = multiplicity n c + multiplicity n d := by
  apply LinearMap.ext
  intro v
  funext i j
  simp [multiplicity, add_mul]
  ring

/-- The concrete matrix algebra in the binary commutant. -/
def multiplicityHom : Matrix (Fin 2) (Fin 2) (ZMod 2) →+* Module.End (ZMod 2) (Space n) where
  toFun := multiplicity n
  map_one' := multiplicity_one n
  map_mul' := multiplicity_mul n
  map_zero' := multiplicity_zero n
  map_add' := multiplicity_add n

theorem multiplicity_injective : Function.Injective (multiplicity n) := by
  intro c d h
  ext i j
  have he := congrArg (fun f : Module.End (ZMod 2) (Space n) =>
    f (Pi.single j (Pi.single 0 1)) i 0) h
  fin_cases j <;> simpa [multiplicity] using he

omit [NeZero n] in
/-- Multiplicity matrices commute with the identical natural action. -/
theorem multiplicity_commutes (c : Matrix (Fin 2) (Fin 2) (ZMod 2)) (g : SL n) :
    multiplicity n c * representation n g = representation n g * multiplicity n c := by
  apply LinearMap.ext
  intro v
  funext i j
  change (c i 0 • g.val.mulVec (v 0) + c i 1 • g.val.mulVec (v 1)) j =
    g.val.mulVec (c i 0 • v 0 + c i 1 • v 1) j
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]


variable {n}
omit [NeZero n] in
private theorem natural_transvection {i j : Fin n} (hij : i ≠ j) (a : (ZMod 2))
    (v : Natural n) :
    (SpecialLinearGroup.transvection hij a).val.mulVec v =
      v + Pi.single i (a * v j) := by
  change ((1 : Matrix (Fin n) (Fin n) (ZMod 2)) + Matrix.single i j a).mulVec v = _
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  congr 1
  funext k
  by_cases hk : k = i <;> simp [hk]

/-- The additive commutant on one natural copy is precisely the field scalars. -/
theorem natural_centralizer_scalar (hn : 2 ≤ n) (f : Natural n →+ Natural n)
    (hf : ∀ (g : SL n) v, f (g.val.mulVec v) = g.val.mulVec (f v)) :
    ∃ c : (ZMod 2), ∀ v, f v = c • v := by
  have hsingle {i j : Fin n} (hij : i ≠ j) (a : (ZMod 2)) :
      f (Pi.single i a) = Pi.single i (a * f (Pi.single j 1) j) := by
    have h := hf (SpecialLinearGroup.transvection hij a) (Pi.single j 1)
    rw [natural_transvection, natural_transvection, map_add] at h
    simpa using add_left_cancel h
  have hdiag {i j : Fin n} (hij : i ≠ j) :
      f (Pi.single i 1) i = f (Pi.single j 1) j := by
    simpa using congrFun (hsingle hij 1) i
  have hs (i : Fin n) (a : (ZMod 2)) :
      f (Pi.single i a) = Pi.single i (a * f (Pi.single 0 1) 0) := by
    obtain ⟨j, hij⟩ : ∃ j : Fin n, i ≠ j := by
      let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
      exact exists_ne i |>.imp fun j hj => hj.symm
    rw [hsingle hij]
    by_cases hj : j = 0
    · rw [hj]
    · rw [hdiag hj]
  refine ⟨f (Pi.single 0 1) 0, fun v => ?_⟩
  have hv : v = ∑ i : Fin n, Pi.single i (v i) := by
    funext i
    simp [Finset.sum_apply]
  calc
    f v = ∑ i : Fin n, f (Pi.single i (v i)) := by rw [← map_sum, ← hv]
    _ = ∑ i : Fin n, Pi.single i (v i * f (Pi.single 0 1) 0) :=
      Finset.sum_congr rfl (fun i _ => hs i (v i))
    _ = f (Pi.single 0 1) 0 • v := by
      funext i
      simp [Finset.sum_apply, mul_comm]



omit [NeZero n] in
private theorem representation_single (g : SL n) (j : Fin 2) (v : Natural n) :
    representation n g (Pi.single j v) = Pi.single j (g.val.mulVec v) := by
  funext i
  by_cases hi : i = j <;> simp [hi, Pi.single_eq_of_ne]

/-- Every binary map commuting with the doubled component is a multiplicity
matrix. This includes all off-diagonal maps between the natural copies. -/
theorem centralizer_multiplicity (hn : 2 ≤ n) (f : Module.End (ZMod 2) (Space n))
    (hf : ∀ (g : SL n) v, f (representation n g v) = representation n g (f v)) :
    ∃ c : Matrix (Fin 2) (Fin 2) (ZMod 2), f = multiplicity n c := by
  let block (i j : Fin 2) : Natural n →+ Natural n :=
    { toFun := fun v => f (Pi.single j v) i
      map_zero' := by simp
      map_add' v w := by simp [Pi.single_add] }
  have hb (i j : Fin 2) (g : SL n) (v : Natural n) :
      block i j (g.val.mulVec v) = g.val.mulVec (block i j v) := by
    change f (Pi.single j (g.val.mulVec v)) i = g.val.mulVec (f (Pi.single j v) i)
    rw [← representation_single]
    exact congrFun (hf g (Pi.single j v)) i
  choose c hc using fun i j => natural_centralizer_scalar hn (block i j) (hb i j)
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  have hv : v = Pi.single 0 (v 0) + Pi.single 1 (v 1) := by
    funext i
    fin_cases i <;> simp
  funext i
  have he : f v i = f (Pi.single 0 (v 0)) i + f (Pi.single 1 (v 1)) i := by
    conv_lhs => rw [hv, map_add]
    rfl
  exact he.trans (congrArg₂ (· + ·) (hc i 0 (v 0)) (hc i 1 (v 1)))

/-- Exact coverage and uniqueness for the full binary commutant. -/
theorem commutes_iff_multiplicity (hn : 2 ≤ n) (f : Module.End (ZMod 2) (Space n)) :
    (∀ (g : SL n) v, f (representation n g v) = representation n g (f v)) ↔
      ∃! c : Matrix (Fin 2) (Fin 2) (ZMod 2), f = multiplicity n c := by
  constructor
  · intro hf
    obtain ⟨c, hc⟩ := centralizer_multiplicity hn f hf
    exact ⟨c, hc, fun d hd => multiplicity_injective n (hd.symm.trans hc)⟩
  · rintro ⟨c, rfl, _⟩ g v
    exact LinearMap.congr_fun (multiplicity_commutes n c g) v

/-- An actual centralizing ambient unit has an invertible multiplicity matrix. -/
theorem centralizer_units (hn : 2 ≤ n) (b : Ambient n)
    (hb : b ∈ Subgroup.centralizer (component n : Set (Ambient n))) :
    ∃ c : (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ, (b : Module.End (ZMod 2) (Space n)) =
      multiplicity n c.val := by
  have hex (a : Ambient n) (ha : a ∈ Subgroup.centralizer (component n : Set (Ambient n))) :
      ∃ c : Matrix (Fin 2) (Fin 2) (ZMod 2), (a : Module.End (ZMod 2) (Space n)) =
        multiplicity n c := by
    apply centralizer_multiplicity hn
    intro g v
    have he := (Subgroup.mem_centralizer_iff.mp ha) ((representation n).asGroupHom g) ⟨g, rfl⟩
    exact LinearMap.congr_fun (congrArg Units.val he.symm) v
  obtain ⟨c, hc⟩ := hex b hb
  obtain ⟨d, hd⟩ := hex b⁻¹ ((Subgroup.centralizer _).inv_mem hb)
  have hcd : c * d = 1 := by
    apply multiplicity_injective n
    rw [multiplicity_mul, ← hc, ← hd, multiplicity_one]
    exact b.val_inv
  have hdc : d * c = 1 := by
    apply multiplicity_injective n
    rw [multiplicity_mul, ← hd, ← hc, multiplicity_one]
    exact b.inv_val
  exact ⟨⟨c, d, hcd, hdc⟩, hc⟩



/-- The full centralizer consists of the invertible multiplicity matrices. -/
def multiplicityCentralizer (n : ℕ) : (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ →*
    Subgroup.centralizer (component n : Set (Ambient n)) :=
  (Units.map (multiplicityHom n).toMonoidHom).codRestrict _ (by
    intro c
    rw [Subgroup.mem_centralizer_iff]
    rintro a ⟨g,rfl⟩
    apply Units.ext
    exact (multiplicity_commutes n c.val g).symm)

theorem multiplicityCentralizer_bijective (hn : 2 ≤ n) :
    Function.Bijective (multiplicityCentralizer n) := by
  constructor
  · intro c d h
    apply Units.ext
    apply multiplicity_injective n
    exact congrArg (fun x => (x.val : Module.End (ZMod 2) (Space n))) h
  · intro b
    obtain ⟨c,hc⟩ := centralizer_units hn b.val b.property
    exact ⟨c,Subtype.ext (Units.ext hc.symm)⟩

noncomputable def centralizerEquiv (hn : 2 ≤ n) :
    Subgroup.centralizer (component n : Set (Ambient n)) ≃*
      Equiv.Perm (Fin 3) :=
  (MulEquiv.ofBijective (multiplicityCentralizer n)
    (multiplicityCentralizer_bijective hn)).symm.trans
      (Matrix.GeneralLinearGroup.toLin.trans
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 2 → ZMod 2)).trans
          BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))

theorem card_centralizer (hn : 2 ≤ n) :
    Nat.card (Subgroup.centralizer (component n : Set (Ambient n))) = 6 := by
  rw [Nat.card_congr (centralizerEquiv hn).toEquiv,Nat.card_perm,Nat.card_fin]
  rfl

end Representation.BinaryDoubledNatural
