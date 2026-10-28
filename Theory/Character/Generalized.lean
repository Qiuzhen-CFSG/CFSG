module

public import Theory.Character.Transport
public import Theory.Character.ScalarProductMultiplicity

/-!
# Algebra of generalized characters

Differences of characters of actual finite-dimensional complex representations
form an integer module and are stable under multiplication by characters.
Direct sums and tensor products provide the representations; a choice of basis
puts their spaces in the coordinate form required by `IsCharacter`.

These are the elementary character-ring operations used in the restriction
criterion for Brauer induction (Serre, *Linear Representations of Finite
Groups*, Chapter 10).
-/

public section
noncomputable section

variable {G : Type*} [Group G]

/-- A finite-dimensional representation can be put in the coordinates used by
the ordinary-character predicate. -/
theorem Representation.isCharacter {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) : IsCharacter ρ.character := by
  let e := (Module.finBasis ℂ V).equivFun
  let σ := e.conjRingEquiv.toMonoidHom.comp ρ
  refine ⟨_, σ, ?_⟩
  ext g
  exact (LinearMap.trace_conj' (ρ g) e).symm

theorem IsCharacter.add {f g : ClassFunction G} (hf : IsCharacter f)
    (hg : IsCharacter g) : IsCharacter (f + g) := by
  obtain ⟨n, ρ, rfl⟩ := hf
  obtain ⟨m, σ, rfl⟩ := hg
  have he : (ρ.prod σ).character = ρ.character + σ.character := by
    ext x
    exact LinearMap.trace_prodMap' (ρ x) (σ x)
  rw [← he]
  exact (ρ.prod σ).isCharacter

theorem IsCharacter.mul {f g : ClassFunction G} (hf : IsCharacter f)
    (hg : IsCharacter g) : IsCharacter (f * g) := by
  obtain ⟨n, ρ, rfl⟩ := hf
  obtain ⟨m, σ, rfl⟩ := hg
  rw [← Representation.char_tensor]
  exact (ρ.tprod σ).isCharacter

theorem isCharacter_zero : IsCharacter (0 : ClassFunction G) := by
  refine ⟨0, Representation.trivial ℂ G (Fin 0 → ℂ), ?_⟩
  ext g
  simp [Representation.character]

theorem IsCharacter.isGeneralized {f : ClassFunction G} (hf : IsCharacter f) :
    IsGeneralizedCharacter f :=
  ⟨f, 0, hf, isCharacter_zero, (sub_zero f).symm⟩

theorem IsGeneralizedCharacter.isClassFunction {f : ClassFunction G}
    (hf : IsGeneralizedCharacter f) : IsClassFunction f := by
  obtain ⟨_, _, ⟨n, ρ, rfl⟩, ⟨m, σ, rfl⟩, rfl⟩ := hf
  intro x g
  simp only [Pi.sub_apply, Representation.char_conj]

theorem isGeneralizedCharacter_zero : IsGeneralizedCharacter (0 : ClassFunction G) :=
  isCharacter_zero.isGeneralized

theorem IsGeneralizedCharacter.add {f g : ClassFunction G}
    (hf : IsGeneralizedCharacter f) (hg : IsGeneralizedCharacter g) :
    IsGeneralizedCharacter (f + g) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hf
  obtain ⟨c, d, hc, hd, rfl⟩ := hg
  refine ⟨a + c, b + d, ha.add hc, hb.add hd, ?_⟩
  abel

theorem IsGeneralizedCharacter.neg {f : ClassFunction G}
    (hf : IsGeneralizedCharacter f) : IsGeneralizedCharacter (-f) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hf
  exact ⟨b, a, hb, ha, neg_sub a b⟩

theorem IsGeneralizedCharacter.sub {f g : ClassFunction G}
    (hf : IsGeneralizedCharacter f) (hg : IsGeneralizedCharacter g) :
    IsGeneralizedCharacter (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem IsGeneralizedCharacter.nsmul {f : ClassFunction G}
    (hf : IsGeneralizedCharacter f) (n : ℕ) : IsGeneralizedCharacter (n • f) := by
  induction n with
  | zero => simpa using isGeneralizedCharacter_zero (G := G)
  | succ n ih => simpa only [succ_nsmul] using ih.add hf

theorem IsGeneralizedCharacter.zsmul {f : ClassFunction G}
    (hf : IsGeneralizedCharacter f) (n : ℤ) : IsGeneralizedCharacter (n • f) := by
  cases n with
  | ofNat n => simpa using hf.nsmul n
  | negSucc n =>
    rw [negSucc_zsmul]
    exact (hf.nsmul (n + 1)).neg

theorem IsGeneralizedCharacter.sum {ι : Type*} (s : Finset ι)
    {f : ι → ClassFunction G} (hf : ∀ i ∈ s, IsGeneralizedCharacter (f i)) :
    IsGeneralizedCharacter (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isGeneralizedCharacter_zero (G := G)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj])))

theorem IsCharacter.mul_generalized {f g : ClassFunction G}
    (hf : IsCharacter f) (hg : IsGeneralizedCharacter g) :
    IsGeneralizedCharacter (f * g) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hg
  exact ⟨f * a, f * b, hf.mul ha, hf.mul hb, mul_sub f a b⟩

end
