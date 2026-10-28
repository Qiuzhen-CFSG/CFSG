module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Theory.GroupTheory.QuasithinBasic
public import Theory.GroupTheory.PrimeRankWitness
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-!
# Three inverse diagonal pairs in a symplectic root normalizer

In the symplectic group of natural dimension `2 * (3 + k)`, the matrices
`diag(a,b,c,1,…,a⁻¹,b⁻¹,c⁻¹,1,…)` normalize the long-root subgroup
`[1, x Eᵢᵢ; 0, 1]`. Both constructions are in Mathlib's actual symplectic
matrix group and descend through its literal quotient by `Subgroup.center`.
Commutation with the standard symplectic matrix `J` shows that the root map
has trivial projective kernel and that a central diagonal parameter squares
to one. Thus odd-prime torsion in the three parameters embeds faithfully in
the projective root normalizer.

For a finite field of characteristic two and order greater than two, a prime
dividing `|F| - 1` is odd. The nontrivial root subgroup is a two-group, and the
rank-three torus contradicts quasithinness of its normalizer. This is the
symplectic instance of the Cartan-subgroup obstruction in Aschbacher–Smith,
*The Classification of Quasithin Groups*, A.2.18 (printed p.40), used for
Theorem D/14.8.2(1) (printed pp.1078–1079). The argument applies in every
rank at least three, without parabolic induction or a group-order formula.
-/

@[expose] public section

open Matrix
namespace Theory.SpecificGroups.SymplecticRoot
variable {F : Type*} [Field F] {r : ℕ}
/-- The standard symplectic matrix group; `r` is half the natural dimension. -/
abbrev Sp (r : ℕ) (F : Type*) [Field F] := ↥(symplecticGroup (Fin r) F)
/-- The literal central quotient of the standard symplectic group. -/
abbrev PSp (r : ℕ) (F : Type*) [Field F] := Sp r F ⧸ Subgroup.center (Sp r F)

/-- A long-root element, with its symplectic membership checked by blocks. -/
def root (i : Fin r) (x : F) : Sp r F :=
  ⟨fromBlocks 1 (diagonal (Pi.single i x)) 0 1, by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    simp⟩

/-- Zero is the identity root parameter. -/
@[simp] theorem root_zero (i : Fin r) : root i (0 : F) = 1 := by
  apply Subtype.ext
  simp [root, ← Matrix.fromBlocks_one]

/-- Root multiplication is addition of field parameters. -/
theorem root_add (i : Fin r) (x y : F) : root i (x + y) = root i x * root i y := by
  apply Subtype.ext
  change fromBlocks _ _ _ _ = fromBlocks _ _ _ _ * fromBlocks _ _ _ _
  rw [fromBlocks_multiply]
  simp [Pi.single_add, diagonal_add, add_comm]

/-- Commuting with `J` forces a central root parameter to vanish. -/
theorem root_eq_zero_of_central (i : Fin r) (x : F)
    (hx : root i x ∈ Subgroup.center (Sp r F)) : x = 0 := by
  have hc := (Subgroup.mem_center_iff.mp hx) (SymplecticGroup.symJ (Fin r) F)
  have hm := congrArg Subtype.val hc
  change J (Fin r) F * (root i x).val = (root i x).val * J (Fin r) F at hm
  have hi := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F =>
    M (.inl i) (.inl i)) hm
  simpa [root, J, fromBlocks_multiply] using hi.symm

/-- A diagonal symplectic matrix with inverse entries on each paired coordinate. -/
def diagonalSp (d : Fin r → Fˣ) : Sp r F :=
  ⟨fromBlocks (diagonal (fun i => (d i : F))) 0 0
    (diagonal (fun i => ((d i)⁻¹ : Fˣ))), by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    simp [diagonal_mul_diagonal]⟩

/-- Commuting with `J` equates each central diagonal parameter with its inverse. -/
theorem diagonalSp_eq_inv_of_central (d : Fin r → Fˣ) (hd : diagonalSp d ∈ Subgroup.center (Sp r F))
    (i : Fin r) : d i = (d i)⁻¹ := by
  have hc := (Subgroup.mem_center_iff.mp hd) (SymplecticGroup.symJ (Fin r) F)
  have hm := congrArg Subtype.val hc
  change J (Fin r) F * (diagonalSp d).val = (diagonalSp d).val * J (Fin r) F at hm
  have hi := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F =>
    M (.inl i) (.inr i)) hm
  apply Units.ext
  simpa [diagonalSp, J, fromBlocks_multiply] using hi.symm

/-- Conjugation scales the long-root parameter by the square of its diagonal entry. -/
theorem diagonalSp_conj_root (d : Fin r → Fˣ) (i : Fin r) (x : F) :
    diagonalSp d * root i x * (diagonalSp d)⁻¹ = root i ((d i : F) ^ 2 * x) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  change fromBlocks _ _ _ _ * fromBlocks _ _ _ _ =
    fromBlocks _ _ _ _ * fromBlocks _ _ _ _
  simp only [fromBlocks_multiply, mul_zero, zero_mul, add_zero, zero_add,
    mul_one, one_mul, diagonal_mul_diagonal]
  congr 1
  apply congrArg diagonal
  funext j
  by_cases hj : j = i
  · subst j
    simp [pow_two, mul_assoc, mul_comm]
  · simp [Pi.single_eq_of_ne hj]

/-- The additive root homomorphism into the symplectic matrix group. -/
noncomputable def rootHom (i : Fin r) : Multiplicative F →* Sp r F where
  toFun x := root i x.toAdd
  map_one' := root_zero i
  map_mul' x y := root_add i x.toAdd y.toAdd

/-- The quotient homomorphism by the actual center. -/
noncomputable def project : Sp r F →* PSp r F := QuotientGroup.mk' _

/-- The additive root homomorphism into the projective symplectic group. -/
noncomputable def projectiveRootHom (i : Fin r) : Multiplicative F →* PSp r F :=
  project.comp (rootHom i)

/-- The root subgroup survives the central quotient faithfully. -/
theorem projectiveRootHom_injective (i : Fin r) :
    Function.Injective (projectiveRootHom (F := F) i) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  change QuotientGroup.mk (root i x.toAdd) = 1 at hx
  rw [QuotientGroup.eq_one_iff] at hx
  exact congrArg Multiplicative.ofAdd (root_eq_zero_of_central i x.toAdd hx)

/-- The image of the additive root map in the literal projective group. -/
noncomputable def rootSubgroup (i : Fin r) : Subgroup (PSp r F) :=
  (projectiveRootHom i).range

/-- The root element with parameter one remains nonidentity. -/
theorem rootSubgroup_ne_bot (i : Fin r) : rootSubgroup (F := F) i ≠ ⊥ := by
  intro h
  have hx : projectiveRootHom i (Multiplicative.ofAdd (1 : F)) = 1 := by
    have hm : projectiveRootHom i (Multiplicative.ofAdd (1 : F)) ∈ rootSubgroup i :=
      ⟨_, rfl⟩
    simpa [h] using hm
  have := (projectiveRootHom_injective i) (hx.trans (map_one _).symm)
  exact one_ne_zero (congrArg Multiplicative.toAdd this)

/-- In characteristic two, the additive root image is a two-group. -/
theorem rootSubgroup_isTwoGroup [CharP F 2] (i : Fin r) :
    IsPGroup 2 (rootSubgroup (F := F) i) := by
  have h : IsPGroup 2 (Multiplicative F) := by
    intro x
    refine ⟨1, ?_⟩
    change (2 ^ 1 : ℕ) • x.toAdd = 0
    rw [pow_one, nsmul_eq_mul, CharP.cast_eq_zero F 2, zero_mul]
  exact h.of_surjective (projectiveRootHom (F := F) i).rangeRestrict
    (projectiveRootHom (F := F) i).rangeRestrict_surjective

/-- The normalizer of the nontrivial root image is a genuine two-local subgroup. -/
theorem rootNormalizer_isTwoLocal [CharP F 2] (i : Fin r) :
    IsTwoLocal (Subgroup.normalizer (rootSubgroup (F := F) i : Set (PSp r F))) :=
  ⟨rootSubgroup i, rootSubgroup_ne_bot i, rootSubgroup_isTwoGroup i, rfl⟩

/-- Independent inverse diagonal pairs form a multiplicative homomorphism. -/
def diagonalHom : (Fin r → Fˣ) →* Sp r F where
  toFun := diagonalSp
  map_one' := by
    apply Subtype.ext
    simp [diagonalSp, ← fromBlocks_one]
  map_mul' d e := by
    apply Subtype.ext
    change fromBlocks _ _ _ _ = fromBlocks _ _ _ _ * fromBlocks _ _ _ _
    simp [diagonal_mul_diagonal, mul_comm]

variable (k : ℕ) (C : Subgroup Fˣ)

/-- Three free diagonal parameters, with identity on the remaining pairs. -/
def torusEntries (a : Fin 3 → C) : Fin (3 + k) → Fˣ :=
  Fin.append ![(a 0).val, (a 1).val, (a 2).val] (fun _ => 1)

/-- Extending the three diagonal parameters by identity is multiplicative. -/
def torusEntriesHom : (Fin 3 → C) →* (Fin (3 + k) → Fˣ) where
  toFun := torusEntries k C
  map_one' := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      fin_cases j <;> simp [torusEntries]
    · intro j
      simp [torusEntries]
  map_mul' a b := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      fin_cases j <;> simp [torusEntries]
    · intro j
      simp [torusEntries]

/-- Three inverse diagonal pairs in the symplectic group. -/
def torusSp : (Fin 3 → C) →* Sp (3 + k) F :=
  diagonalHom.comp (torusEntriesHom k C)

/-- The three-parameter torus after the literal central quotient. -/
noncomputable def torusProjective : (Fin 3 → C) →* PSp (3 + k) F :=
  project.comp (torusSp k C)

/-- Parameter groups with no involutions inject after projectivization. -/
theorem torusProjective_injective (htwo : ∀ u : C, u ^ 2 = 1 → u = 1) :
    Function.Injective (torusProjective k C) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  change QuotientGroup.mk (diagonalSp (torusEntries k C a)) = 1 at ha
  rw [QuotientGroup.eq_one_iff] at ha
  funext i
  have hi := diagonalSp_eq_inv_of_central _ ha (Fin.castAdd k i)
  have he : (a i).val = (a i).val⁻¹ := by
    fin_cases i <;> simpa [torusEntries] using hi
  apply htwo
  apply Subtype.ext
  change (a i).val ^ 2 = 1
  simpa only [pow_two] using (eq_inv_iff_mul_eq_one.mp he)

private theorem torusProjective_conj_root (a : Fin 3 → C)
    (i : Fin (3 + k)) (x : Multiplicative F) :
    torusProjective k C a * projectiveRootHom i x * (torusProjective k C a)⁻¹ =
      projectiveRootHom i (Multiplicative.ofAdd
        ((torusEntries k C a i : F) ^ 2 * x.toAdd)) := by
  have ht := congrArg (project (F := F))
    (diagonalSp_conj_root (torusEntries k C a) i x.toAdd)
  simpa only [torusProjective, torusSp, diagonalHom, torusEntriesHom,
    projectiveRootHom, rootHom, MonoidHom.comp_apply, MonoidHom.coe_mk,
    OneHom.coe_mk, map_mul, map_inv, toAdd_ofAdd] using ht

/-- Every torus element normalizes the actual projective root subgroup. -/
theorem torusProjective_mem_normalizer (a : Fin 3 → C) (i : Fin (3 + k)) :
    torusProjective k C a ∈ Subgroup.normalizer
      (rootSubgroup (F := F) i : Set (PSp (3 + k) F)) := by
  have hf (a : Fin 3 → C) (g : PSp (3 + k) F) (hg : g ∈ rootSubgroup i) :
      torusProjective k C a * g * (torusProjective k C a)⁻¹ ∈ rootSubgroup i := by
    obtain ⟨x, rfl⟩ := hg
    rw [torusProjective_conj_root]
    exact ⟨_, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨hf a g, fun hg => ?_⟩
  simpa only [map_inv, inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel,
    mul_one] using hf a⁻¹ _ hg

/-- The three-parameter homomorphism into the actual root normalizer. -/
noncomputable def torusNormalizer (i : Fin (3 + k)) :
    (Fin 3 → C) →* Subgroup.normalizer
      (rootSubgroup (F := F) i : Set (PSp (3 + k) F)) :=
  (torusProjective k C).codRestrict _ (fun a => torusProjective_mem_normalizer k C a i)

/-- The root-normalizer homomorphism is faithful on groups without involutions. -/
theorem torusNormalizer_injective (i : Fin (3 + k))
    (htwo : ∀ u : C, u ^ 2 = 1 → u = 1) :
    Function.Injective (torusNormalizer k C i) := by
  intro a b hab
  exact torusProjective_injective k C htwo (congrArg Subtype.val hab)

/-- Every odd prime dividing the multiplicative field order contributes rank three. -/
theorem primeRank_rootNormalizer_ge_three [Finite F] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hd : p ∣ Nat.card F - 1)
    (i : Fin (3 + k)) :
    3 ≤ primeRank p (Subgroup.normalizer
      (rootSubgroup (F := F) i : Set (PSp (3 + k) F))) := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have hdu : p ∣ Nat.card Fˣ := by simpa only [Nat.card_units] using hd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hdu
  have hroot : IsPrimitiveRoot u p := hu ▸ IsPrimitiveRoot.orderOf u
  have hc : Nat.card (rootsOfUnity p F) = p := hroot.card_rootsOfUnity'
  have hpow (u : rootsOfUnity p F) : u ^ p = 1 :=
    Subtype.ext ((mem_rootsOfUnity p u.val).mp u.property)
  have hcop : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr (by
    intro h
    have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
    rw [he] at ho
    norm_num at ho)
  have htwo (u : rootsOfUnity p F) (hu : u ^ 2 = 1) : u = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (hpow u)) (orderOf_dvd_of_pow_eq_one hu)
  apply primeRank_ge_of_elementary_embedding
    (A := Fin 3 → rootsOfUnity p F)
    (fun a => funext (fun i => hpow (a i)))
    (by rw [Nat.card_fun, hc, Nat.card_fin])
    (torusNormalizer k (rootsOfUnity p F) i)
  exact torusNormalizer_injective k (rootsOfUnity p F) i htwo

/-- No PSp of rank at least three over an even field larger than two is quasithin. -/
theorem not_quasithin [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) :
    ¬ IsQuasithin (PSp (3 + k) F) := by
  intro hG
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (show Nat.card F - 1 ≠ 1 by omega)
  have heven : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card, even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
    exact FiniteField.even_card_iff_char_two.mp (ringChar.eq F 2)
  have ho : Odd p := hp.odd_of_ne_two (by
    intro he
    subst p
    obtain ⟨a, ha⟩ := heven
    obtain ⟨b, hb⟩ := hd
    omega)
  let i : Fin (3 + k) := ⟨0, by omega⟩
  have hr := primeRank_rootNormalizer_ge_three (F := F) k hp ho hd i
  have hb := Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hG _
    (rootNormalizer_isTwoLocal i) p hp ho
  omega

end Theory.SpecificGroups.SymplecticRoot
