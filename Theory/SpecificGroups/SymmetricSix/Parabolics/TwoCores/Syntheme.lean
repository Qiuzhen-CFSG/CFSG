module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Syntheme.Calculation
import Mathlib.Tactic

/-!
# Syntheme parabolic two-cores in S₆ and A₆

The stabilizer of `{01,23,45}` is the group of affine permutations of three
binary blocks. Its block action has elementary abelian kernel of order eight.
The even subgroup has the even-parity kernel of order four. The trivial
two-core of S₃ identifies these as the intrinsic cores. Both cores are
self-centralizing in their parabolics. The even action is irreducible, while
the simultaneous swap of all three blocks gives the invariant line in S₆.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.7,
printed pp. 420–421. These are the local syntheme calculations used in its
proof, including its S₆ exception; the other geometric clauses remain with
the source-theorem assembly.
-/

public section
namespace Theory.SpecificGroups.SymmetricSix
open SynthemeCalculation
private theorem elementary_of_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) [IsElementaryAbelian 2 H] : IsElementaryAbelian 2 G where
  is_comm.comm := by
    intro x y
    apply e.injective
    simpa only [map_mul] using IsMulCommutative.is_comm.comm (e x) (e y)
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply e.injective
    simpa only [map_pow, map_one] using
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 H) (e x)

private noncomputable def coreTransport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : pCore 2 G ≃* pCore 2 H :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))

private theorem mem_core_transport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (x : G) : e x ∈ pCore 2 H ↔ x ∈ pCore 2 G := by
  rw [← pCore_map_iso 2 e, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, he⟩
    exact e.injective he ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

private theorem centralizer_transport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H)
    (hc : Subgroup.centralizer (pCore 2 H : Set H) = pCore 2 H) :
    Subgroup.centralizer (pCore 2 G : Set G) = pCore 2 G := by
  ext x
  rw [← mem_core_transport e x, ← hc, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    obtain ⟨z, rfl⟩ := e.surjective y
    have hz := hx z ((mem_core_transport e z).mp hy)
    simpa only [map_mul] using congrArg e hz
  · intro hx y hy
    apply e.injective
    simpa only [map_mul] using hx (e y) ((mem_core_transport e y).mpr hy)

/-- The actual kernel consists of the three independent within-block swaps. -/
noncomputable def synthemeCoreEquiv : pCore 2 synthemeStabilizer ≃* core :=
  (coreTransport modelEquiv.symm).trans (MulEquiv.subgroupCongr core_eq.symm)

/-- The actual even kernel consists of the even-parity within-block swaps. -/
noncomputable def a6SynthemeCoreEquiv : pCore 2 a6SynthemeStabilizer ≃* evenCore :=
  (coreTransport evenModelEquiv.symm).trans (MulEquiv.subgroupCongr evenCore_eq.symm)

noncomputable def synthemeCoreBinaryEquiv :
    pCore 2 synthemeStabilizer ≃* Multiplicative (Fin 3 → ZMod 2) :=
  synthemeCoreEquiv.trans binaryEquiv.symm

noncomputable def a6SynthemeCoreBinaryEquiv :
    pCore 2 a6SynthemeStabilizer ≃* Multiplicative (Fin 2 → ZMod 2) :=
  a6SynthemeCoreEquiv.trans binaryFourEquiv.symm

theorem synthemeCore_elementary : IsElementaryAbelian 2 (pCore 2 synthemeStabilizer) :=
  elementary_of_equiv synthemeCoreEquiv

theorem a6SynthemeCore_elementary : IsElementaryAbelian 2 (pCore 2 a6SynthemeStabilizer) :=
  elementary_of_equiv a6SynthemeCoreEquiv

theorem synthemeCore_card : Nat.card (pCore 2 synthemeStabilizer) = 8 :=
  (Nat.card_congr synthemeCoreEquiv.toEquiv).trans core_card

theorem a6SynthemeCore_card : Nat.card (pCore 2 a6SynthemeStabilizer) = 4 :=
  (Nat.card_congr a6SynthemeCoreEquiv.toEquiv).trans evenCore_card

/-- The block permutation is trivial exactly for independent within-block swaps. -/
theorem mem_synthemeCore_iff (g : synthemeStabilizer) :
    g ∈ pCore 2 synthemeStabilizer ↔ (modelEquiv.symm g).right = 1 := by
  rw [← mem_core_transport modelEquiv.symm, ← core_eq]
  rfl

theorem mem_a6SynthemeCore_iff (g : a6SynthemeStabilizer) :
    g ∈ pCore 2 a6SynthemeStabilizer ↔ (evenModelEquiv.symm g).val.right = 1 := by
  rw [← mem_core_transport evenModelEquiv.symm, ← evenCore_eq]
  rfl

/-- The actual action of the syntheme stabilizer on its three blocks. -/
noncomputable def synthemeQuotientHom : synthemeStabilizer →* Equiv.Perm (Fin 3) :=
  quotientHom.comp modelEquiv.symm.toMonoidHom

/-- The same block action restricted to the even permutations. -/
noncomputable def a6SynthemeQuotientHom : a6SynthemeStabilizer →* Equiv.Perm (Fin 3) :=
  evenQuotientHom.comp evenModelEquiv.symm.toMonoidHom

theorem synthemeQuotientHom_surjective : Function.Surjective synthemeQuotientHom :=
  quotientHom_surjective.comp modelEquiv.symm.surjective

theorem a6SynthemeQuotientHom_surjective : Function.Surjective a6SynthemeQuotientHom :=
  evenQuotientHom_surjective.comp evenModelEquiv.symm.surjective

theorem synthemeQuotientHom_ker : synthemeQuotientHom.ker = pCore 2 synthemeStabilizer := by
  ext g
  exact (mem_synthemeCore_iff g).symm

theorem a6SynthemeQuotientHom_ker :
    a6SynthemeQuotientHom.ker = pCore 2 a6SynthemeStabilizer := by
  ext g
  exact (mem_a6SynthemeCore_iff g).symm

noncomputable def synthemeCoreQuotientEquiv :
    synthemeStabilizer ⧸ pCore 2 synthemeStabilizer ≃* Equiv.Perm (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq synthemeQuotientHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ synthemeQuotientHom_surjective)

noncomputable def a6SynthemeCoreQuotientEquiv :
    a6SynthemeStabilizer ⧸ pCore 2 a6SynthemeStabilizer ≃* Equiv.Perm (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq a6SynthemeQuotientHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ a6SynthemeQuotientHom_surjective)

/-- Kernel of the actual conjugation action in the S₆ parabolic. -/
theorem synthemeCore_centralizer :
    Subgroup.centralizer (pCore 2 synthemeStabilizer : Set synthemeStabilizer) =
      pCore 2 synthemeStabilizer :=
  centralizer_transport modelEquiv.symm (by rw [← core_eq]; exact centralizer_core)

/-- Kernel of the actual conjugation action in the A₆ parabolic. -/
theorem a6SynthemeCore_centralizer :
    Subgroup.centralizer (pCore 2 a6SynthemeStabilizer : Set a6SynthemeStabilizer) =
      pCore 2 a6SynthemeStabilizer :=
  centralizer_transport evenModelEquiv.symm (by rw [← evenCore_eq]; exact centralizer_evenCore)

/-- Irreducibility with normality in the actual parabolic. -/
theorem a6SynthemeCore_irreducible (N : Subgroup a6SynthemeStabilizer) [N.Normal]
    (hle : N ≤ pCore 2 a6SynthemeStabilizer) :
    N = ⊥ ∨ N = pCore 2 a6SynthemeStabilizer := by
  let e := evenModelEquiv.symm
  let M := N.map e.toMonoidHom
  have : M.Normal := Subgroup.Normal.map inferInstance _ e.surjective
  have hm : M ≤ evenCore := by
    rw [evenCore_eq, ← pCore_map_iso 2 e]
    exact Subgroup.map_mono hle
  rcases normal_subgroup_evenCore M hm with h | h
  · left
    apply e.mapSubgroup.injective
    simpa only [MulEquiv.coe_mapSubgroup, Subgroup.map_bot] using h
  · right
    apply e.mapSubgroup.injective
    simpa only [MulEquiv.coe_mapSubgroup, pCore_map_iso, ← evenCore_eq] using h

/-- The invariant line generated by the simultaneous swap `(01)(23)(45)`. -/
noncomputable def synthemeInvariantLine : Subgroup synthemeStabilizer :=
  invariantLine.map modelEquiv.toMonoidHom

instance : synthemeInvariantLine.Normal :=
  Subgroup.Normal.map inferInstance _ modelEquiv.surjective

theorem synthemeInvariantLine_card : Nat.card synthemeInvariantLine = 2 :=
  (Nat.card_congr (modelEquiv.subgroupMap invariantLine).toEquiv).symm.trans invariantLine_card

theorem synthemeInvariantLine_bot_lt :
    (⊥ : Subgroup synthemeStabilizer) < synthemeInvariantLine := by
  apply bot_lt_iff_ne_bot.mpr
  intro h
  have := synthemeInvariantLine_card
  rw [h, Nat.card_eq_fintype_card] at this
  simp at this

theorem synthemeInvariantLine_lt_core : synthemeInvariantLine < pCore 2 synthemeStabilizer := by
  rw [← pCore_map_iso 2 modelEquiv, ← core_eq]
  exact modelEquiv.mapSubgroup.strictMono invariantLine_lt_core

/-- This quotient map is the action on the three actual blocks. -/
theorem synthemeQuotientHom_blocks (g : synthemeStabilizer) (i : Fin 3) :
    (block i).image g.val = block (synthemeQuotientHom g i) := by
  have hg : modelHom (modelEquiv.symm g) = g.val :=
    congrArg Subtype.val (modelEquiv.apply_symm_apply g)
  change (block i).image g.val = block ((modelEquiv.symm g).right i)
  simpa only [hg] using modelHom_blocks (modelEquiv.symm g) i

theorem a6SynthemeQuotientHom_blocks (g : a6SynthemeStabilizer) (i : Fin 3) :
    (block i).image g.val.val = block (a6SynthemeQuotientHom g i) := by
  have hg : modelHom (evenModelEquiv.symm g).val = g.val.val :=
    congrArg (fun h : a6SynthemeStabilizer => h.val.val) (evenModelEquiv.apply_symm_apply g)
  change (block i).image g.val.val = block ((evenModelEquiv.symm g).val.right i)
  simpa only [hg] using modelHom_blocks (evenModelEquiv.symm g).val i

/-- Intrinsic characterization as the permutations fixing each block setwise. -/
theorem mem_synthemeCore_iff_fix_blocks (g : synthemeStabilizer) :
    g ∈ pCore 2 synthemeStabilizer ↔ ∀ i : Fin 3, (block i).image g.val = block i := by
  rw [← synthemeQuotientHom_ker, MonoidHom.mem_ker]
  constructor
  · intro h i
    rw [synthemeQuotientHom_blocks, h]
    rfl
  · intro h
    apply Equiv.ext
    intro i
    exact block_injective ((synthemeQuotientHom_blocks g i).symm.trans (h i))

theorem mem_a6SynthemeCore_iff_fix_blocks (g : a6SynthemeStabilizer) :
    g ∈ pCore 2 a6SynthemeStabilizer ↔ ∀ i : Fin 3, (block i).image g.val.val = block i := by
  rw [← a6SynthemeQuotientHom_ker, MonoidHom.mem_ker]
  constructor
  · intro h i
    rw [a6SynthemeQuotientHom_blocks, h]
    rfl
  · intro h
    apply Equiv.ext
    intro i
    exact block_injective ((a6SynthemeQuotientHom_blocks g i).symm.trans (h i))

/-- Independent swaps, embedded in the actual syntheme stabilizer. -/
noncomputable def synthemeSwapVector : Binary →* synthemeStabilizer :=
  modelEquiv.toMonoidHom.comp SemidirectProduct.inl

/-- The intrinsic two-core is exactly the set of independent within-block swaps. -/
theorem mem_synthemeCore_iff_swaps (g : synthemeStabilizer) :
    g ∈ pCore 2 synthemeStabilizer ↔ ∃ v : Binary, synthemeSwapVector v = g := by
  rw [mem_synthemeCore_iff]
  constructor
  · intro hg
    refine ⟨(modelEquiv.symm g).left, ?_⟩
    apply modelEquiv.symm.injective
    change modelEquiv.symm (modelEquiv (SemidirectProduct.inl _)) = _
    rw [MulEquiv.symm_apply_apply]
    apply SemidirectProduct.ext
    · rfl
    · exact hg.symm
  · rintro ⟨v,rfl⟩
    change (modelEquiv.symm (modelEquiv (SemidirectProduct.inl v))).right = 1
    rw [MulEquiv.symm_apply_apply]
    rfl

/-- The alternating core consists precisely of the even-parity swap vectors. -/
theorem mem_a6SynthemeCore_iff_even_swaps (g : a6SynthemeStabilizer) :
    g ∈ pCore 2 a6SynthemeStabilizer ↔ ∃ v : Binary,
      v.toAdd 0 + v.toAdd 1 + v.toAdd 2 = 0 ∧ (synthemeSwapVector v).val = g.val.val := by
  rw [mem_a6SynthemeCore_iff]
  have hg : modelHom (evenModelEquiv.symm g).val = g.val.val :=
    congrArg (fun h : a6SynthemeStabilizer => h.val.val) (evenModelEquiv.apply_symm_apply g)
  constructor
  · intro hr
    refine ⟨(evenModelEquiv.symm g).val.left,
      (mem_evenModel _).mp (evenModelEquiv.symm g).property, ?_⟩
    change modelHom (SemidirectProduct.inl _) = _
    have hm : SemidirectProduct.inl (evenModelEquiv.symm g).val.left =
        (evenModelEquiv.symm g).val := by
      apply SemidirectProduct.ext
      · rfl
      · exact hr.symm
    rw [hm, hg]
  · rintro ⟨v, _hv, he⟩
    have hm : SemidirectProduct.inl v = (evenModelEquiv.symm g).val :=
      modelHom_injective (he.trans hg.symm)
    exact (congrArg SemidirectProduct.right hm).symm

/-- The parabolic conjugates a swap vector by permuting its block coordinates. -/
theorem synthemeSwapVector_conjugate (g : synthemeStabilizer) (v : Binary) :
    g * synthemeSwapVector v * g⁻¹ =
      synthemeSwapVector (permute (synthemeQuotientHom g) v) := by
  change g * modelEquiv (SemidirectProduct.inl v) * g⁻¹ =
    modelEquiv (SemidirectProduct.inl (permute (modelEquiv.symm g).right v))
  have h := congrArg modelEquiv (conjugate_inl (modelEquiv.symm g) v)
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using h

/-- These coordinates act by the indicated independent within-block swaps. -/
theorem synthemeSwapVector_apply (v : Binary) (i : Fin 3) (b : ZMod 2) :
    (synthemeSwapVector v).val (letterEquiv (i,b)) =
      letterEquiv (i, b + v.toAdd i) :=
  modelHom_apply (SemidirectProduct.inl v) i b

/-- The simultaneous within-block swap as an element of the actual parabolic. -/
@[expose] def synthemeTripleSwap : synthemeStabilizer :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5, by decide +kernel⟩

theorem synthemeTripleSwap_val : synthemeTripleSwap.val =
    Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 := rfl

theorem synthemeInvariantLine_eq_zpowers :
    synthemeInvariantLine = Subgroup.zpowers synthemeTripleSwap := by
  change invariantLine.map modelEquiv.toMonoidHom = _
  rw [invariantLine_eq_zpowers, MonoidHom.map_zpowers]
  congr 1
  apply Subtype.ext
  change modelHom diagonal = _
  decide +kernel

end Theory.SpecificGroups.SymmetricSix
