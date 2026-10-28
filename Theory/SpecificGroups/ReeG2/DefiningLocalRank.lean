module

public import Theory.AtlasPort.LinearGroups.ReeG2.TorusRootAction
public import Theory.GroupTheory.PrimeRankWitness

/-!
# A defining-characteristic local rank witness in the small Ree groups

The actual torus element h(−1) is an involution. Its conjugation character
on the beta root group is trivial, and a matrix entry recovers every beta
parameter. Thus the additive field embeds in its centralizer, also after
any injective homomorphism of the Ree model. Over a field of order
3^(2m+1), this gives local 3-rank at least 2m+1.

This supplies directly the rank contradiction used in Aschbacher–Smith,
Lemma A.2.17, printed p.38 of `refs/quasithin.pdf`. It does not identify the
full involution centralizer with C₂ × PSL₂, and it does not exclude the
separate small derived group at m=0. The matrices and their conjugation law
come from the licensed ATLAS adaptations imported above; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- The torus element h(−1) in the actual seven-dimensional Ree group. -/
noncomputable def torusInvolution (m : ℕ) : Model F m :=
  ⟨torus m (-1), Subgroup.subset_closure (Or.inl (Or.inr ⟨-1, rfl⟩))⟩

/-- The torus parameter is faithful, so h(−1) is nonidentity in characteristic three. -/
theorem torusInvolution_ne_one (m : ℕ) : torusInvolution (F := F) m ≠ 1 := by
  intro h
  have ht : torus (F := F) m (-1) = torus m 1 := by
    have hh : torus (F := F) m (-1) = 1 := congrArg Subtype.val h
    exact hh.trans (torusHom m).map_one.symm
  have hn : (-1 : Fˣ) = 1 := torus_injective m ht
  have hc : (-1 : F) = 1 := congrArg Units.val hn
  have htwo : (2 : F) = 0 := by linear_combination -hc
  have := (CharP.cast_eq_zero_iff F 3 2).mp htwo
  norm_num at this

/-- The torus element h(−1) has square one. -/
theorem torusInvolution_sq (m : ℕ) : torusInvolution (F := F) m ^ 2 = 1 := by
  apply Subtype.ext
  change torus m (-1) ^ 2 = 1
  change (torusHom m) (-1) ^ 2 = 1
  rw [← map_pow]
  simp

/-- The beta root group as an additive copy of the defining field inside the Ree group. -/
noncomputable def betaHom (m : ℕ) (hcard : Nat.card F = 3^(2*m+1)) :
    Multiplicative F →* Model F m where
  toFun b := ⟨beta m b.toAdd,
    Subgroup.subset_closure (Or.inl (Or.inl (Or.inl (Or.inr ⟨b.toAdd,rfl⟩))))⟩
  map_one' := Subtype.ext (beta_zero m)
  map_mul' b c := by
    apply Subtype.ext
    change beta m (b.toAdd+c.toAdd) = beta m b.toAdd * beta m c.toAdd
    simpa [rootElement] using (rootElement_mul m hcard 0 b.toAdd 0 0 c.toAdd 0).symm

/-- The matrix entry in row 2, column 6 recovers the beta parameter. -/
theorem betaHom_injective (m : ℕ) (hcard : Nat.card F = 3^(2*m+1)) :
    Function.Injective (betaHom m hcard) := by
  intro a b h
  have hh := congrArg (fun g : Model F m => g.val.val 2 6) h
  change a.toAdd = b.toAdd at hh
  exact Multiplicative.toAdd.injective hh

/-- The beta character takes value one at the torus parameter −1. -/
theorem betaHom_commute (m : ℕ) (hcard : Nat.card F = 3^(2*m+1)) (b : Multiplicative F) :
    Commute (torusInvolution m) (betaHom m hcard b) := by
  apply Subtype.ext
  change torus m (-1) * beta m b.toAdd = beta m b.toAdd * torus m (-1)
  have hc := torus_conjugate_root m hcard (-1 : Fˣ) 0 b.toAdd 0
  have he : (torus m (-1))⁻¹ * beta m b.toAdd * torus m (-1) = beta m b.toAdd := by
    norm_num only [Units.val_neg, Units.val_one, map_neg, map_one, zero_mul,
      zero_div, mul_neg, mul_one, rootElement, alpha_zero, gamma_zero,
      one_mul, neg_div_neg_eq, div_one] at hc
    exact hc
  calc
    torus m (-1) * beta m b.toAdd =
      torus m (-1) * ((torus m (-1))⁻¹ * beta m b.toAdd * torus m (-1)) :=
        congrArg (torus m (-1) * ·) he.symm
    _ = _ := by simp only [← mul_assoc, mul_inv_cancel, one_mul]
end Atlas.ReeG2

namespace Atlas.ReeG2
variable {F G : Type*} [Field F] [Finite F] [CharP F 3] [Group G]

/-- The beta root group lies in the centralizer of the transported torus involution. -/
noncomputable def betaCentralizerHom (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (f : Model F m →* G) :
    Multiplicative F →* Subgroup.centralizer ({f (torusInvolution m)} : Set G) :=
  (f.comp (betaHom m hcard)).codRestrict _ fun b => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((betaHom_commute m hcard b).map f).eq.symm

/-- An ambient embedding preserves the faithful beta parameter. -/
theorem betaCentralizerHom_injective (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (f : Model F m →* G) (hf : Function.Injective f) :
    Function.Injective (betaCentralizerHom m hcard f) := by
  intro a b h
  exact betaHom_injective m hcard (hf (congrArg Subtype.val h))

/-- The concrete beta root group witnesses local 3-rank at least 2m+1. -/
theorem fieldExponent_le_primeRank_torusInvolution_centralizer [Finite G] (m : ℕ)
    (hcard : Nat.card F = 3^(2*m+1))
    (f : Model F m →* G) (hf : Function.Injective f) :
    2*m+1 ≤ primeRank 3 (Subgroup.centralizer ({f (torusInvolution m)} : Set G)) := by
  have hp : ∀ a : Multiplicative F, a^3 = 1 := by
    intro a
    change 3 • a.toAdd = 0
    simp [nsmul_eq_mul, show (3 : F) = 0 from CharP.cast_eq_zero F 3]
  exact primeRank_ge_of_elementary_embedding hp hcard (betaCentralizerHom m hcard f)
    (betaCentralizerHom_injective m hcard f hf)

/-- Every embedded Ree model has an actual involution with the defining-field rank witness. -/
theorem exists_involution_primeRank_ge [Finite G] (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (f : Model F m →* G) (hf : Function.Injective f) :
    ∃ z : G, z ≠ 1 ∧ z^2=1 ∧ 2*m+1 ≤ primeRank 3 (Subgroup.centralizer ({z} : Set G)) := by
  refine ⟨f (torusInvolution m), ?_, ?_,
    fieldExponent_le_primeRank_torusInvolution_centralizer m hcard f hf⟩
  · intro h
    exact torusInvolution_ne_one m (hf (h.trans f.map_one.symm))
  · rw [← map_pow, torusInvolution_sq, map_one]
end Atlas.ReeG2
