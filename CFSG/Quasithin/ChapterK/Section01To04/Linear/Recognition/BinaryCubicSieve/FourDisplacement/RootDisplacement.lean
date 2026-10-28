module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.RootDifferences
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.NormalizerExtension

/-!
# Central-root displacement for adjacent binary SL₄ supports

Two adjacent active roots produce an eight-vector rank-two configuration.
Four of those vectors are independent images of the central-root difference,
so that root has fixed codimension at least four. The same bound holds for an
actor containing any component conjugate of the root, inside the full linear
normalizer. In particular its rank-one strict displacement inequality follows.

The extraction proof adapts the private calculation in
`FourSmallModules/AdjacentSupport.lean`, preserving that shared module. It uses
only a nonzero local highest vector; faithfulness, irreducibility and cubicity
are unnecessary for this part. No conclusion about arbitrary actors of ranks
two through four is asserted here.

Source: Aschbacher–Smith, K.3.2, printed pp.454–455, citing GM04 Table 7;
the rank-two root calculation is also used in G.9.3(11)–(12).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement

open Representation Representation.BinaryOffender
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem lift_independent {ι : Type*} [Fintype ι]
    (D : V →ₗ[ZMod 2] V) (f : ι → V)
    (hD : ∀ k, D (D (f k)) = 0)
    (hf : LinearIndependent (ZMod 2) (fun k => D (f k))) :
    LinearIndependent (ZMod 2) (Sum.elim f (fun k => D (f k))) := by
  rw [Fintype.linearIndependent_iff] at hf ⊢
  intro c hc
  have he := congrArg D hc
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_add,
    map_sum, map_smul, hD, smul_zero, Finset.sum_const_zero, add_zero, map_zero] at he
  have hl := hf (fun k => c (.inl k)) he
  have hr : ∀ k, c (.inr k) = 0 := by
    apply hf
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      hl, zero_smul, Finset.sum_const_zero, zero_add] using hc
  intro k
  cases k with
  | inl k => exact hl k
  | inr k => exact hr k

private theorem independent_eight (A B C : V →ₗ[ZMod 2] V)
    (hAA : ∀ x, A (A x) = 0) (hBB : ∀ x, B (B x) = 0)
    (hCC : ∀ x, C (C x) = 0)
    (hAC : ∀ x, A (C x) = C (A x))
    (hBC : ∀ x, B (C x) = C (B x))
    (hAB : ∀ x, B (A (C x)) = A (B (C x)))
    (w : V) (hv : A (B (C w)) ≠ 0) :
    let f := Sum.elim (Sum.elim (fun _ : Unit => w) (fun _ : Unit => B w))
        (Sum.elim (fun _ : Unit => A w) (fun _ : Unit => A (B w)))
    LinearIndependent (ZMod 2) (Sum.elim f (fun k => C (f k))) := by
  -- First construct the four-vector image under C.
  have hpair : LinearIndependent (ZMod 2)
      (Sum.elim (fun _ : Unit => A (C w)) (fun _ : Unit => B (A (C w)))) := by
    apply lift_independent B (fun _ : Unit => A (C w)) (fun _ => hBB _)
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have he : c () • B (A (C w)) = 0 := by simpa using hc
    exact (smul_eq_zero.mp he).resolve_right (by rwa [hAB])
  have hfour : LinearIndependent (ZMod 2)
      (Sum.elim (Sum.elim (fun _ : Unit => C w) (fun _ : Unit => B (C w)))
        (Sum.elim (fun _ : Unit => A (C w)) (fun _ : Unit => A (B (C w))))) := by
    have he := lift_independent A
      (Sum.elim (fun _ : Unit => C w) (fun _ : Unit => B (C w)))
      (fun _ => hAA _) (by
        convert hpair using 1
        funext k
        cases k <;> simp [hAB])
    convert he using 1
    funext k
    cases k <;> simp only [Sum.elim_inl, Sum.elim_inr]
    rename_i k
    cases k <;> rfl
  dsimp only
  apply lift_independent C _ (fun _ => hCC _)
  convert hfour using 1
  funext k
  rcases k with (k | k) | (k | k) <;> simp [← hAC, ← hBC]

def adjacentCentralRoot (i j : Fin 3) : Group :=
  simpleUpper i * simpleUpper j * simpleUpper i * simpleUpper j

private def longestExchange (i j : Fin 3) : Group := simpleSwap i * simpleSwap j * simpleSwap i

private def rootSum (ρ : Representation (ZMod 2) Group V) (g : Group) : V →ₗ[ZMod 2] V :=
  ρ g + LinearMap.id

private theorem binary_add_self (x : V) : x + x = 0 := by
  have hh : (1 : ZMod 2) + 1 = 0 := by decide
  simpa only [add_smul, one_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • x) hh

private theorem rootSum_apply (ρ : Representation (ZMod 2) Group V) (g : Group) (x : V) :
    rootSum ρ g x = ρ g x + x := rfl

private theorem act_mul (ρ : Representation (ZMod 2) Group V) (g k : Group) (x : V) :
    ρ g (ρ k x) = ρ (g * k) x := by rw [map_mul]; rfl

private theorem rootSum_square (ρ : Representation (ZMod 2) Group V)
    {g : Group} (hg : g * g = 1) (x : V) : rootSum ρ g (rootSum ρ g x) = 0 := by
  simp only [rootSum_apply, map_add, act_mul, hg, map_one, Module.End.one_apply]
  calc
    _ = (x + x) + (ρ g x + ρ g x) := by abel
    _ = 0 := by rw [binary_add_self, binary_add_self, add_zero]

private theorem rootSum_move (ρ : Representation (ZMod 2) Group V)
    {g k t : Group} (he : g * t = t * k) (x : V) :
    rootSum ρ g (ρ t x) = ρ t (rootSum ρ k x) := by
  simp only [rootSum_apply, map_add, act_mul, he]

private theorem rootSum_commute (ρ : Representation (ZMod 2) Group V)
    {g k : Group} (he : g * k = k * g) (x : V) :
    rootSum ρ g (rootSum ρ k x) = rootSum ρ k (rootSum ρ g x) := by
  simp only [rootSum_apply, map_add, act_mul, he]
  abel

private theorem upper_square (i : Fin 3) : simpleUpper i * simpleUpper i = 1 := by
  revert i
  decide

private theorem long_square (i j : Fin 3) (hij : i.val + 1 = j.val) :
    adjacentCentralRoot i j * adjacentCentralRoot i j = 1 := by
  revert i j
  decide

private theorem long_left (i j : Fin 3) (hij : i.val + 1 = j.val) :
    simpleUpper i * adjacentCentralRoot i j = adjacentCentralRoot i j * simpleUpper i := by
  revert i j
  decide

private theorem long_right (i j : Fin 3) (hij : i.val + 1 = j.val) :
    simpleUpper j * adjacentCentralRoot i j = adjacentCentralRoot i j * simpleUpper j := by
  revert i j
  decide

private theorem adjacent_commutator (i j : Fin 3) (hij : i.val + 1 = j.val) :
    simpleUpper j * simpleUpper i * adjacentCentralRoot i j = simpleUpper i * simpleUpper j ∧
    simpleUpper i * simpleUpper j * adjacentCentralRoot i j = simpleUpper j * simpleUpper i := by
  revert i j
  decide

private theorem conjugate_roots (i j : Fin 3) (hij : i.val + 1 = j.val) :
    simpleUpper j * simpleSwap i = simpleSwap i * adjacentCentralRoot i j ∧
    adjacentCentralRoot i j * simpleSwap i = simpleSwap i * simpleUpper j ∧
    adjacentCentralRoot i j * simpleSwap j = simpleSwap j * simpleUpper i := by
  revert i j
  decide

private theorem sums_commute_on_long (ρ : Representation (ZMod 2) Group V)
    (i j : Fin 3) (hij : i.val + 1 = j.val) (x : V) :
    rootSum ρ (simpleUpper j) (rootSum ρ (simpleUpper i) (rootSum ρ (adjacentCentralRoot i j) x)) =
      rootSum ρ (simpleUpper i) (rootSum ρ (simpleUpper j) (rootSum ρ (adjacentCentralRoot i j) x)) := by
  simp only [rootSum_apply, map_add, act_mul, ← mul_assoc,
    (adjacent_commutator i j hij).1, (adjacent_commutator i j hij).2]
  abel

private theorem rootSum_active {ρ : Representation (ZMod 2) Group V}
    {J : Finset (Fin 3)} {v : V} (h : LocalHighestVector ρ J v)
    {i : Fin 3} (hi : i ∈ J) : rootSum ρ (simpleUpper i) (ρ (simpleSwap i) v) = v := by
  have hn (x : V) : -x = x := by
    apply add_right_cancel (b := x)
    rw [neg_add_cancel, binary_add_self]
  have hs := h.upperDifference_swap hi
  change ρ (simpleUpper i) (ρ (simpleSwap i) v) - ρ (simpleSwap i) v = v at hs
  change ρ (simpleUpper i) (ρ (simpleSwap i) v) + ρ (simpleSwap i) v = v
  simpa only [sub_eq_add_neg, hn] using hs

private theorem norm_longestExchange {ρ : Representation (ZMod 2) Group V}
    {J : Finset (Fin 3)} {v : V} (h : LocalHighestVector ρ J v)
    {i j : Fin 3} (hi : i ∈ J) (hj : j ∈ J) (hij : i.val + 1 = j.val) :
    rootSum ρ (simpleUpper i) (rootSum ρ (adjacentCentralRoot i j)
      (rootSum ρ (simpleUpper j) (ρ (longestExchange i j) v))) = v := by
  obtain ⟨hya, hza, hzb⟩ := conjugate_roots i j hij
  simp only [longestExchange, map_mul, Module.End.mul_apply]
  rw [rootSum_move ρ hya, rootSum_move ρ hza, rootSum_move ρ hzb,
    rootSum_active h hi, rootSum_active h hj, rootSum_active h hi]

/-- Four lifts of the central-root image in the adjacent rank-two module. -/
private def fourVectors (ρ : Representation (ZMod 2) Group V) (i j : Fin 3) (v : V) :=
  let w := ρ (longestExchange i j) v
  let A := rootSum ρ (simpleUpper i)
  let B := rootSum ρ (simpleUpper j)
  Sum.elim (Sum.elim (fun _ : Unit => w) (fun _ : Unit => B w))
    (Sum.elim (fun _ : Unit => A w) (fun _ : Unit => A (B w)))

/-- Eight vectors in the adjacent rank-two module. -/
private def eightVectors (ρ : Representation (ZMod 2) Group V) (i j : Fin 3) (v : V) :=
  let f := fourVectors ρ i j v
  Sum.elim f (fun k => rootSum ρ (adjacentCentralRoot i j) (f k))

private theorem independent_rankTwo {ρ : Representation (ZMod 2) Group V}
    {J : Finset (Fin 3)} {v : V} (h : LocalHighestVector ρ J v) (hv : v ≠ 0)
    {i j : Fin 3} (hi : i ∈ J) (hj : j ∈ J) (hij : i.val + 1 = j.val) :
    LinearIndependent (ZMod 2) (eightVectors ρ i j v) := by
  apply independent_eight
    (rootSum ρ (simpleUpper i)) (rootSum ρ (simpleUpper j)) (rootSum ρ (adjacentCentralRoot i j))
    (rootSum_square ρ (upper_square i)) (rootSum_square ρ (upper_square j))
    (rootSum_square ρ (long_square i j hij))
    (rootSum_commute ρ (long_left i j hij)) (rootSum_commute ρ (long_right i j hij))
    (sums_commute_on_long ρ i j hij)
  rw [rootSum_commute ρ (long_right i j hij)]
  rwa [norm_longestExchange h hi hj hij]

private theorem independent_centralImage {ρ : Representation (ZMod 2) Group V}
    {J : Finset (Fin 3)} {v : V} (h : LocalHighestVector ρ J v) (hv : v ≠ 0)
    {i j : Fin 3} (hi : i ∈ J) (hj : j ∈ J) (hij : i.val + 1 = j.val) :
    LinearIndependent (ZMod 2) (fun k => rootSum ρ (adjacentCentralRoot i j) (fourVectors ρ i j v k)) :=
  (independent_rankTwo h hv hi hj hij).comp Sum.inr Sum.inr_injective


/-- The central root in an adjacent A₂ subsystem moves at least four
dimensions. This is a displacement bound, rather than a degree bound. -/
theorem four_le_fixedCodim_adjacentCentralRoot [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) Group V} {J : Finset (Fin 3)} {v : V}
    (h : LocalHighestVector σ J v) (hv : v ≠ 0) {i j : Fin 3}
    (hi : i ∈ J) (hj : j ∈ J) (hij : i.val + 1 = j.val) :
    4 ≤ fixedCodim σ (Subgroup.zpowers (adjacentCentralRoot i j)) := by
  let C := rootSum σ (adjacentCentralRoot i j)
  let f := fourVectors σ i j v
  let g : ((Unit ⊕ Unit) ⊕ (Unit ⊕ Unit)) → LinearMap.range C :=
    fun k => ⟨C (f k), ⟨f k, rfl⟩⟩
  have hli : LinearIndependent (ZMod 2) g :=
    LinearIndependent.of_comp (LinearMap.range C).subtype
      (independent_centralImage h hv hi hj hij)
  have hd : 4 ≤ Module.finrank (ZMod 2) (LinearMap.range C) := by
    simpa using hli.fintype_card_le_finrank
  have he : C = σ (adjacentCentralRoot i j) - LinearMap.id := by
    ext x
    change σ (adjacentCentralRoot i j) x + x = σ (adjacentCentralRoot i j) x - x
    have hn : -x = x := by
      apply add_right_cancel (b := x)
      rw [neg_add_cancel, binary_add_self]
    rw [sub_eq_add_neg, hn]
  rwa [he, ← fixedCodim_zpowers_eq_displacement_rank] at hd

/-- The literal component embedding into its linear normalizer. -/
def componentEmbedding (σ : Representation (ZMod 2) Group V) :
    Group →* linearNormalizer σ :=
  σ.asGroupHom.codRestrict _ (fun g => (actionImage σ).le_normalizer ⟨g, rfl⟩)

@[simp] theorem componentEmbedding_apply (σ : Representation (ZMod 2) Group V)
    (g : Group) (v : V) :
    normalizerRepresentation σ (componentEmbedding σ g) v = σ g v := rfl

/-- An actor containing the central root inherits the four-dimensional
displacement on the original module, even if it also contains outer actors. -/
theorem four_le_fixedCodim_of_adjacentCentralRoot_mem [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) Group V} {J : Finset (Fin 3)} {v : V}
    (h : LocalHighestVector σ J v) (hv : v ≠ 0) {i j : Fin 3}
    (hi : i ∈ J) (hj : j ∈ J) (hij : i.val + 1 = j.val)
    (A : Subgroup (linearNormalizer σ))
    (ha : componentEmbedding σ (adjacentCentralRoot i j) ∈ A) :
    4 ≤ fixedCodim (normalizerRepresentation σ) A := by
  have hd := four_le_fixedCodim_adjacentCentralRoot h hv hi hj hij
  have he : fixedCodim σ (Subgroup.zpowers (adjacentCentralRoot i j)) =
      fixedCodim (normalizerRepresentation σ)
        (Subgroup.zpowers (componentEmbedding σ (adjacentCentralRoot i j))) := by
    rw [fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_eq_displacement_rank]
    rfl
  rw [he] at hd
  have hfix : fixedSpace (normalizerRepresentation σ) A ≤
      fixedSpace (normalizerRepresentation σ)
        (Subgroup.zpowers (componentEmbedding σ (adjacentCentralRoot i j))) := by
    intro x hx g
    exact hx ⟨g, (Subgroup.zpowers_le.mpr ha) g.property⟩
  have hr := Submodule.finrank_mono hfix
  have hA := fixedCodim_add_finrank (normalizerRepresentation σ) A
  have ht := fixedCodim_add_finrank (normalizerRepresentation σ)
    (Subgroup.zpowers (componentEmbedding σ (adjacentCentralRoot i j)))
  omega

/-- The same estimate applies to any actor containing a component conjugate
of the central root. The fixed codimension is transported on the full
normalizer, not just on its component subgroup. -/
theorem four_le_fixedCodim_of_conjugate_adjacentCentralRoot_mem
    [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) Group V} {J : Finset (Fin 3)} {v : V}
    (h : LocalHighestVector σ J v) (hv : v ≠ 0) {i j : Fin 3}
    (hi : i ∈ J) (hj : j ∈ J) (hij : i.val + 1 = j.val)
    (A : Subgroup (linearNormalizer σ)) (c : Group)
    (ha : componentEmbedding σ (c * adjacentCentralRoot i j * c⁻¹) ∈ A) :
    4 ≤ fixedCodim (normalizerRepresentation σ) A := by
  let a := componentEmbedding σ c
  let B := A.map (MulAut.conj a⁻¹).toMonoidHom
  have hm : componentEmbedding σ (adjacentCentralRoot i j) ∈ B := by
    refine ⟨_, ha, ?_⟩
    simp [a, map_mul, map_inv, mul_assoc]
  have hd := four_le_fixedCodim_of_adjacentCentralRoot_mem h hv hi hj hij B hm
  simpa only [B, fixedCodim_map_conj] using hd

/-- The rank-one case of the desired strict inequality is settled for actors
containing a conjugate of this root. No cubic or irreducibility assumption
is needed here. -/
theorem strict_gap_of_conjugate_adjacentCentralRoot_mem_rank_le_one
    [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) Group V} {J : Finset (Fin 3)} {v : V}
    (h : LocalHighestVector σ J v) (hv : v ≠ 0) {i j : Fin 3}
    (hi : i ∈ J) (hj : j ∈ J) (hij : i.val + 1 = j.val)
    (A : Subgroup (linearNormalizer σ)) (c : Group)
    (ha : componentEmbedding σ (c * adjacentCentralRoot i j * c⁻¹) ∈ A)
    (hr : rank A ≤ 1) :
    2 * rank A < fixedCodim (normalizerRepresentation σ) A := by
  have hd := four_le_fixedCodim_of_conjugate_adjacentCentralRoot_mem h hv hi hj hij A c ha
  omega

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
