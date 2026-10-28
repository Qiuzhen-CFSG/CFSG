module

public import Theory.GroupTheory.ChiefFactorDirectPower.CharacteristicallySimple
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# A simple normal subgroup in primitive degree nine

Choose a minimal nontrivial normal subgroup `M` of `H`. It is characteristically
simple, so the finite structure theorem gives an actual equivalence `M ≃* Sⁿ`
with `S` simple and `n > 0`. The hypothesis on abelian normal subgroups makes
both `M` and `S` nonabelian.

Each direct factor is normal in the transitive group `M`, so its orbit sizes
divide nine. A nontrivial orbit gives a faithful action of the simple factor;
solvability of the symmetric group on four letters excludes orbit sizes one
and three. Thus every factor is transitive. Two distinct factors commute,
and a subgroup centralizing a transitive faithful action acts freely. A second
transitive factor would therefore have order nine, making it abelian. Hence
`n = 1`, and the original normal subgroup `M` is simple.

This is the simple-socle step for the alternating A₉ case of condition K in
Aschbacher–Smith, *The Classification of Quasithin Groups*, Theorem 0.1.2(3),
printed p.4, and the corresponding main theorem on printed p.482. It uses no
list of primitive groups and makes no model-recognition assumption.
-/

namespace CFSG.Quasithin.MainConverse.NineReduction

open MulAction
open scoped IsMulCommutative

/-- A simple group acting faithfully on at most four points is abelian. -/
private theorem simple_faithful_small_action {S X : Type*} [Group S] [IsSimpleGroup S]
    [MulAction S X] [FaithfulSMul S X] [Finite X] (hc : Nat.card X ≤ 4) :
    IsMulCommutative S := by
  classical
  let := Fintype.ofFinite X
  have hcard : Fintype.card X ≤ Fintype.card (Fin 4) := by simpa using hc
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm X) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  have hi : Function.Injective (toPermHom S X) := by
    intro a b h
    exact FaithfulSMul.eq_of_smul_eq_smul (fun x => congrArg (fun p : Equiv.Perm X => p x) h)
  have hs : Group.IsSolvable S := Group.isSolvable_of_isSolvable_injective hi
  exact ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr hs⟩⟩

/-- Normality makes each orbit size divide nine; simplicity rules out the small sizes. -/
private theorem simple_normal_transitive_nine {G : Type*} [Group G]
    [MulAction G (Fin 9)] [FaithfulSMul G (Fin 9)] [IsPretransitive G (Fin 9)]
    (S : Subgroup G) [S.Normal] [IsSimpleGroup S] (hna : ¬ IsMulCommutative S) :
    IsPretransitive S (Fin 9) := by
  classical
  obtain ⟨s, hs⟩ := exists_ne (1 : S)
  have hm : ∃ x : Fin 9, s • x ≠ x := by
    by_contra! h
    apply hs
    exact FaithfulSMul.eq_of_smul_eq_smul (fun x => (h x).trans (one_smul S x).symm)
  obtain ⟨x, hx⟩ := hm
  let f := toPermHom S (orbit S x)
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    obtain he | he := (inferInstance : f.ker.Normal).eq_bot_or_eq_top
    · exact he
    · have hm : s ∈ f.ker := he.symm ▸ Subgroup.mem_top s
      have hh := congrArg (fun p : Equiv.Perm (orbit S x) => (p ⟨x, mem_orbit_self x⟩).val) hm
      exact (hx hh).elim
  let : FaithfulSMul S (orbit S x) := ⟨fun h => hf (Equiv.ext h)⟩
  have hd : Nat.card (orbit S x) ∣ 9 := by
    simpa only [← Nat.card_coe_set_eq, Nat.card_fin] using
      (IsBlock.orbit_of_normal (G := G) (N := S) x).ncard_dvd_card
        ⟨x, mem_orbit_self x⟩
  have hc : Nat.card (orbit S x) = 9 := by
    have hd' : Nat.card (orbit S x) = 1 ∨ Nat.card (orbit S x) = 3 ∨
        Nat.card (orbit S x) = 9 := by
      have := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp (show Nat.card (orbit S x) ∣ 3 ^ 2 from hd)
      obtain ⟨k, hk, he⟩ := this
      interval_cases k <;> norm_num at he ⊢ <;> omega
    rcases hd' with hc | hc | hc
    · exact (hna (simple_faithful_small_action (X := orbit S x) (by omega))).elim
    · exact (hna (simple_faithful_small_action (X := orbit S x) (by omega))).elim
    · exact hc
  apply (isPretransitive_iff_orbit_eq_univ x).mpr
  apply (Set.eq_univ_iff_ncard (orbit S x)).mpr
  simpa only [← Nat.card_coe_set_eq, Nat.card_fin] using hc

/-- The centralizer of a transitive action acts freely; a transitive subgroup of it is regular. -/
private theorem commuting_transitive_card_nine {G : Type*} [Group G]
    [MulAction G (Fin 9)] [FaithfulSMul G (Fin 9)]
    (A B : Subgroup G) [IsPretransitive A (Fin 9)] [IsPretransitive B (Fin 9)]
    (hc : ∀ a : A, ∀ b : B, Commute (a : G) (b : G)) : Nat.card B = 9 := by
  have hi : Function.Injective (fun b : B => b • (0 : Fin 9)) := by
    intro b c h
    change (b : G) • (0 : Fin 9) = (c : G) • (0 : Fin 9) at h
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin 9)
    intro x
    obtain ⟨a, rfl⟩ := exists_smul_eq A (0 : Fin 9) x
    change (b : G) • ((a : G) • (0 : Fin 9)) = (c : G) • ((a : G) • (0 : Fin 9))
    rw [← mul_smul, (hc a b).eq.symm, mul_smul,
      ← mul_smul (c : G), (hc a c).eq.symm, mul_smul, h]
  have hs : Function.Surjective (fun b : B => b • (0 : Fin 9)) :=
    fun x => exists_smul_eq B 0 x
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hi, hs⟩)).trans (Nat.card_fin 9)

private theorem coordinate_normal {S : Type*} [Group S] (n : ℕ) (i : Fin n) :
    (MonoidHom.mulSingle (fun _ : Fin n => S) i).range.Normal := by
  classical
  constructor
  rintro _ ⟨s, rfl⟩ g
  refine ⟨g i * s * (g i)⁻¹, ?_⟩
  ext j
  by_cases hj : j = i
  · subst j; simp
  · simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj]

/-- Two nonabelian simple direct factors cannot act faithfully and transitively in degree nine. -/
private theorem simple_power_degree_nine {S : Type*} [Group S] [IsSimpleGroup S]
    (hna : ¬ IsMulCommutative S) (n : ℕ)
    [MulAction (Fin n → S) (Fin 9)] [FaithfulSMul (Fin n → S) (Fin 9)]
    [IsPretransitive (Fin n → S) (Fin 9)] : n ≤ 1 := by
  classical
  by_contra hn
  have hn2 : 2 ≤ n := by omega
  let f (i : Fin n) := MonoidHom.mulSingle (fun _ : Fin n => S) i
  let F (i : Fin n) := (f i).range
  let e (i : Fin n) : S ≃* F i := MonoidHom.ofInjective (f := f i) (Pi.mulSingle_injective (M := fun _ : Fin n => S) i)
  have hfn (i : Fin n) : (F i).Normal := coordinate_normal n i
  have hfs (i : Fin n) : IsSimpleGroup (F i) := (e i).symm.isSimpleGroup
  have hfna (i : Fin n) : ¬ IsMulCommutative (F i) := by
    intro ha
    let := ha
    apply hna
    apply IsMulCommutative.of_comm
    intro a b
    apply (e i).injective
    simp only [map_mul, mul_comm]
  have ht (i : Fin n) : IsPretransitive (F i) (Fin 9) := by
    let := hfn i
    let := hfs i
    exact simple_normal_transitive_nine (F i) (hfna i)
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let := ht i
  let := ht j
  have hc : ∀ a : F i, ∀ b : F j, Commute (a : Fin n → S) (b : Fin n → S) := by
    rintro ⟨a, s, rfl⟩ ⟨b, t, rfl⟩
    apply Pi.mulSingle_commute (f := fun _ : Fin n => S) _ s t
    intro h
    have := congrArg Fin.val h
    simp [i, j] at this
  have hcard := commuting_transitive_card_nine (F i) (F j) hc
  have ha : IsMulCommutative (F j) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hcard
  exact hfna j ha


/-- A primitive subgroup of A₉ with no nontrivial abelian normal subgroup has
an actual nonabelian simple normal subgroup. Normality is inside `H`. -/
public theorem primitive_exists_nonabelian_simple_normal
    (H : Subgroup (alternatingGroup (Fin 9)))
    (hp : IsPreprimitive H (Fin 9))
    (habel : ∀ A : Subgroup H, A.Normal → IsMulCommutative A → A = ⊥) :
    ∃ N : Subgroup H, N.Normal ∧ IsSimpleGroup N ∧ ¬ IsMulCommutative N := by
  classical
  let := hp
  have hnt : Nontrivial H := by
    obtain ⟨g, hg⟩ := exists_smul_eq H (0 : Fin 9) 1
    refine ⟨⟨g, 1, ?_⟩⟩
    intro he
    subst g
    norm_num at hg
  let := hnt
  obtain ⟨M, hM, hminimal⟩ := exists_minimal_of_wellFoundedLT
    (fun M : Subgroup H => M.Normal ∧ M ≠ ⊥) ⟨⊤, inferInstance, top_ne_bot⟩
  let : M.Normal := hM.1
  let : Nontrivial M := M.nontrivial_iff_ne_bot.mpr hM.2
  have hmin (K : Subgroup H) (hK : K.Normal) (hKM : K ≤ M) : K = ⊥ ∨ K = M := by
    by_cases hb : K = ⊥
    · exact Or.inl hb
    · exact Or.inr (le_antisymm hKM (hminimal ⟨hK, hb⟩ hKM))
  have hchar (C : Subgroup M) (hC : C.Characteristic) : C = ⊥ ∨ C = ⊤ := by
    let := hC
    obtain he | he := hmin (C.map M.subtype) inferInstance (Subgroup.map_subtype_le C)
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective C M.subtype_injective).mp he)
    · right
      apply Subgroup.map_injective M.subtype_injective
      simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using he
  have hnaM : ¬ IsMulCommutative M := fun ha => hM.2 (habel M hM.1 ha)
  obtain ⟨S, hs, n, hn, ⟨e⟩⟩ :=
    CharacteristicallySimple.exists_simple_subgroup_power hchar
  let := hs
  have hnaS : ¬ IsMulCommutative S := by
    intro ha
    let := ha
    apply hnaM
    apply IsMulCommutative.of_comm
    intro a b
    apply e.injective
    ext i
    simp only [map_mul, Pi.mul_apply, mul_comm]
  let : IsPretransitive M (Fin 9) := Atlas.GroupTheory.normal_pretransitive M hM.2
  let : MulAction (Fin n → S) (Fin 9) := MulAction.compHom (Fin 9) e.symm.toMonoidHom
  let : FaithfulSMul (Fin n → S) (Fin 9) :=
    ⟨fun h => e.symm.injective (FaithfulSMul.eq_of_smul_eq_smul (α := Fin 9) h)⟩
  let : IsPretransitive (Fin n → S) (Fin 9) :=
    MulAction.isPretransitive_compHom e.symm.surjective
  have hnle := simple_power_degree_nine hnaS n
  have hn1 : n = 1 := by omega
  subst n
  have hsimple : IsSimpleGroup M := (e.trans (MulEquiv.piUnique (fun _ : Fin 1 => S))).isSimpleGroup
  exact ⟨M, hM.1, hsimple, hnaM⟩

end CFSG.Quasithin.MainConverse.NineReduction
