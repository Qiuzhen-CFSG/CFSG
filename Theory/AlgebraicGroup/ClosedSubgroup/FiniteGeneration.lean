module

public import Theory.AlgebraicGroup.ClosedSubgroup.Product
public import Theory.AlgebraicGroup.ClosedSubgroup.Connected
public import Theory.AlgebraicGroup.Dimension.Strict
public import Theory.AlgebraicGroup.Irreducible.Product

universe u

/-!
Finite-word generation by connected closed algebraic subgroups.

Given an arbitrary family `H`, this module proves that its abstractly generated
subgroup is already a finite pointwise product of members of the family, and
hence is Zariski closed and connected.  The proof uses the standard finite-word
geometry for algebraic groups.  A word is realized as the range of an iterated
product morphism, so connectedness makes its closure irreducible.  Although the
index family need not be finite, finite ambient dimension bounds the dimensions
of the closures of all finite words and therefore supplies a maximal one.
Adjoining any factor on either side cannot enlarge that closure.  The closure
is thus stable under every generator and becomes a closed subgroup containing
the abstract generated subgroup.

The maximal word has constructible dense range in this irreducible closed
subgroup, hence contains a nonempty open subset.  Translating and symmetrizing
gives an open identity neighborhood contained in another finite word.  The
subgroup it generates is both open and dense, while Noetherian compactness
bounds the powers needed to cover the closed subgroup.  This yields the actual
finite product decomposition and identifies the maximal closure with the
abstract generated subgroup.

This is the general geometric input underlying the root-subgroup generation
step used around GLS3, Theorem 1.10.1(b); the proof is independent of that
theorem and of all root-system modules.
-/

namespace Theory.AlgebraicGroup

open scoped Pointwise Cardinal

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The pointwise product of a word in a family of closed subgroups. -/
@[expose]
public def closedSubgroupWordProduct {G : Variety k} [AlgebraicGroup G]
    {ι : Type*} (H : ι → ClosedSubgroup G) : List ι → Set (Variety.Point G)
  | [] => {1}
  | i :: w => (H i : Set (Variety.Point G)) * closedSubgroupWordProduct H w

omit [IsAlgClosed k] in
private lemma wordSet_append {G : Variety k} [AlgebraicGroup G]
    {ι : Type*} (H : ι → ClosedSubgroup G) (u v : List ι) :
    closedSubgroupWordProduct H (u ++ v) = closedSubgroupWordProduct H u * closedSubgroupWordProduct H v := by
  induction u with
  | nil =>
      ext x
      constructor
      · intro hx
        exact Set.mem_mul.mpr ⟨1, by simp [closedSubgroupWordProduct], x, hx, by simp⟩
      · rintro ⟨a, ha, b, hb, hab⟩
        have ha' : a = 1 := Set.mem_singleton_iff.mp (by simpa [closedSubgroupWordProduct] using ha)
        have hab' : a * b ∈ closedSubgroupWordProduct H v := by simpa [ha'] using hb
        exact hab ▸ hab'
  | cons i u ih =>
      rw [List.cons_append, closedSubgroupWordProduct, closedSubgroupWordProduct, ih]
      ext x
      constructor
      · rintro ⟨a, ha, b, ⟨c, hc, d, hd, hcd⟩, hab⟩
        refine ⟨a * c, Set.mem_mul.mpr ⟨a, ha, c, hc, rfl⟩, d, hd, ?_⟩
        calc
          (a * c) * d = a * (c * d) := by rw [mul_assoc]
          _ = a * b := congrArg (fun z => a * z) hcd
          _ = x := hab
      · rintro ⟨ac, ⟨a, ha, c, hc, hac⟩, d, hd, h⟩
        refine ⟨a, ha, c * d, Set.mem_mul.mpr ⟨c, hc, d, hd, rfl⟩, ?_⟩
        calc
          a * (c * d) = (a * c) * d := by rw [mul_assoc]
          _ = ac * d := congrArg (fun z => z * d) hac
          _ = x := h

omit [IsAlgClosed k] in
private lemma mul_image_prodSet_eq {G : Variety k} [AlgebraicGroup G]
    (S T : Set (Variety.Point G)) :
    (AlgebraicGroup.mulMorphism G).toFun '' Variety.prodSet S T = S * T := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine Set.mem_mul.mpr ⟨(Variety.prodPointEquiv G G w).1,
      hw.1, (Variety.prodPointEquiv G G w).2, hw.2, ?_⟩
    rfl
  · rintro ⟨x, hx, y, hy, rfl⟩
    refine ⟨(Variety.prodPointEquiv G G).symm (x, y), ?_, ?_⟩
    · exact ⟨hx, hy⟩
    · rfl

omit [IsAlgClosed k] in
private lemma wordSet_isIrreducible {G : Variety k} [AlgebraicGroup G]
    {ι : Type*} (H : ι → ClosedSubgroup G)
    (hconn : ∀ i, _root_.IsConnected (H i : Set (Variety.Point G))) :
    ∀ w, IsIrreducible (closedSubgroupWordProduct H w) := by
  intro w
  induction w with
  | nil => exact isIrreducible_singleton
  | cons i w ih =>
      rw [closedSubgroupWordProduct]
      rw [← mul_image_prodSet_eq]
      apply IsIrreducible.image
        (prodSet_irreducible_of_irreducible
          ((H i).isIrreducible_of_isConnected (hconn i)) ih)
        (AlgebraicGroup.mulMorphism G).toFun
        (AlgebraicGroup.mulMorphism G).continuous.continuousOn

omit [IsAlgClosed k] in
/-- A finite word in connected closed algebraic subgroups is connected. -/
public lemma closedSubgroupWordProduct_isConnected
    {G : Variety k} [AlgebraicGroup G]
    {ι : Type*} (H : ι → ClosedSubgroup G)
    (hconn : ∀ i, _root_.IsConnected (H i : Set (Variety.Point G)))
    (w : List ι) :
    _root_.IsConnected (closedSubgroupWordProduct H w) :=
  (wordSet_isIrreducible H hconn w).isConnected

private def wordVariety {G : Variety k} [AlgebraicGroup G]
    {ι : Type*} (H : ι → ClosedSubgroup G) : List ι → Variety k
  | [] => G
  | i :: w => Variety.prod (H i).carrierVariety (wordVariety H w)

private noncomputable def wordMorphism {G : Variety k} [AlgebraicGroup G]
    {ι : Type*} (H : ι → ClosedSubgroup G) :
    (w : List ι) → Variety.Morphism (wordVariety H w) G
  | [] =>
      Variety.Morphism.const (wordVariety H []) G 1
  | i :: w =>
      let left := (H i).inclusion.toVariety.comp (Variety.Morphism.fst
        (H i).carrierVariety (wordVariety H w))
      let right := (wordMorphism H w).comp (Variety.Morphism.snd
        (H i).carrierVariety (wordVariety H w))
      (AlgebraicGroup.mulMorphism G).comp (left.pair right)

omit [IsAlgClosed k] in
private lemma wordMorphism_range {G : Variety k} [AlgebraicGroup G]
    {ι : Type*} (H : ι → ClosedSubgroup G) (w : List ι) :
    Set.range (wordMorphism H w).toFun = closedSubgroupWordProduct H w := by
  induction w with
  | nil =>
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        change (1 : Variety.Point G) ∈ ({1} : Set (Variety.Point G))
        simp
      · intro hx
        have : x = 1 := by simpa [closedSubgroupWordProduct] using hx
        subst x
        refine ⟨(1 : Variety.Point G), ?_⟩
        rfl
  | cons i w ih =>
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        let p := Variety.prodPointEquiv (H i).carrierVariety (wordVariety H w) z
        have hz : (wordMorphism H (i :: w)).toFun z =
            (H i).inclusion.onPoints p.1 *
              (wordMorphism H w).toFun p.2 := by rfl
        rw [hz]
        apply Set.mem_mul.mpr
        exact ⟨(H i).inclusion.onPoints p.1,
          (H i).pointEquiv p.1 |>.property,
          (wordMorphism H w).toFun p.2,
          by rw [← ih]; exact Set.mem_range_self _, rfl⟩
      · intro hx
        rcases Set.mem_mul.mp hx with ⟨a, ha, b, hb, hab⟩
        rw [← ih] at hb
        rcases hb with ⟨y, rfl⟩
        let x0 := (H i).pointEquiv.symm ⟨a, ha⟩
        let z := (Variety.prodPointEquiv (H i).carrierVariety (wordVariety H w)).symm (x0, y)
        refine ⟨z, ?_⟩
        have haeq : (H i).inclusion.onPoints x0 = a := by
          change ((H i).pointEquiv x0).val = a
          dsimp [x0]
          rw [H i |>.pointEquiv.apply_symm_apply]
        have hz : (wordMorphism H (i :: w)).toFun z =
            (H i).inclusion.onPoints x0 * (wordMorphism H w).toFun y := by rfl
        rw [hz, haeq, hab]

private def morphism_codRestrictClosedSubgroup
    {V G : Variety k} [AlgebraicGroup G]
    (f : Variety.Morphism V G) (T : ClosedSubgroup G)
    (hmap : ∀ x, f.toFun x ∈ T.toSubgroup) :
    Variety.Morphism V T.carrierVariety where
  toFun := fun x => T.pointEquiv.symm ⟨f.toFun x, hmap x⟩
  regular := by
    intro i
    rcases f.regular i with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    intro x
    change (T.pointEquiv (T.pointEquiv.symm ⟨f.toFun x, hmap x⟩)).val.val i =
      evalPolynomial x.val p
    rw [T.pointEquiv.apply_symm_apply]
    exact hp x

omit [IsAlgClosed k] in
private lemma morphism_codRestrictClosedSubgroup_inclusion
    {V G : Variety k} [AlgebraicGroup G]
    (f : Variety.Morphism V G) (T : ClosedSubgroup G)
    (hmap : ∀ x, f.toFun x ∈ T.toSubgroup) (x : Variety.Point V) :
    T.inclusion.onPoints (morphism_codRestrictClosedSubgroup f T hmap |>.toFun x) =
      f.toFun x := by
  change (T.pointEquiv (T.pointEquiv.symm ⟨f.toFun x, hmap x⟩)).val = f.toFun x
  rw [T.pointEquiv.apply_symm_apply]

omit [IsAlgClosed k] in
private lemma wordClosureZariskiClosed {G : Variety k} [AlgebraicGroup G]
    {ι : Type*} (H : ι → ClosedSubgroup G) (w : List ι) :
    IsZariskiClosed G (closure (closedSubgroupWordProduct H w)) :=
  Variety.isClosed_iff_isZariskiClosed.mp isClosed_closure

private def wordClosureVariety {G : Variety k} [AlgebraicGroup G]
    {ι : Type*} (H : ι → ClosedSubgroup G) (w : List ι) : Variety k :=
  Variety.closedSubvariety (wordClosureZariskiClosed H w)

private noncomputable def wordDimension {G : Variety k} [AlgebraicGroup G]
    {ι : Type*} (H : ι → ClosedSubgroup G) (w : List ι) : ℕ :=
  Cardinal.toNat (Variety.dimension (wordClosureVariety H w))

omit [IsAlgClosed k] in
private lemma wordClosure_isIrreducible {G : Variety k} [AlgebraicGroup G]
    {ι : Type*} (H : ι → ClosedSubgroup G)
    (hconn : ∀ i, _root_.IsConnected (H i : Set (Variety.Point G)))
    (w : List ι) :
    IsIrreducible (closure (closedSubgroupWordProduct H w)) :=
  (wordSet_isIrreducible H hconn w).closure

omit [IsAlgClosed k] in
private lemma wordDimension_le_ambient {G : Variety k} [AlgebraicGroup G]
    {ι : Type*} (H : ι → ClosedSubgroup G) (w : List ι) :
    Variety.dimension (wordClosureVariety H w) ≤ Variety.dimension G := by
  exact closedSubvariety_dimension_le G (wordClosureZariskiClosed H w)

omit [IsAlgClosed k] in
private lemma exists_word_max_dimension {G : Variety k} [AlgebraicGroup G]
    {ι : Type*} (H : ι → ClosedSubgroup G) :
    ∃ w : List ι, ∀ v, wordDimension H v ≤ wordDimension H w := by
  let d : List ι → ℕ := wordDimension H
  let B := Cardinal.toNat (Variety.dimension G)
  have hbound : ∀ w, d w ≤ B := by
    intro w
    exact Cardinal.toNat_le_toNat (wordDimension_le_ambient H w)
      (variety_dimension_lt_aleph0 G)
  have hrange : Set.range d ⊆ Set.Iic B := by
    rintro _ ⟨w, rfl⟩
    exact hbound w
  have hfinite : (Set.range d).Finite := (Set.finite_Iic B).subset hrange
  obtain ⟨m, hm⟩ := hfinite.exists_maximal (Set.range_nonempty d)
  rcases hm.1 with ⟨w, rfl⟩
  refine ⟨w, ?_⟩
  intro v
  by_contra hle
  have hlt : d w < d v := Nat.lt_of_not_ge hle
  exact (Nat.not_lt_of_ge (hm.2 (Set.mem_range_self v) hlt.le)) hlt

omit [IsAlgClosed k] in
private lemma one_mem_wordSet {G : Variety k} [AlgebraicGroup G]
    {ι : Type*} (H : ι → ClosedSubgroup G) :
    ∀ w, (1 : Variety.Point G) ∈ closedSubgroupWordProduct H w := by
  intro w
  induction w with
  | nil => simp [closedSubgroupWordProduct]
  | cons i w ih =>
      exact Set.mem_mul.mpr ⟨1, (H i).one_mem, 1, ih, one_mul 1⟩

omit [IsAlgClosed k] in
private lemma inv_mem_wordSet_reverse {G : Variety k} [AlgebraicGroup G]
    {ι : Type*} (H : ι → ClosedSubgroup G) :
    ∀ {w : List ι} {x : Variety.Point G},
      x ∈ closedSubgroupWordProduct H w → x⁻¹ ∈ closedSubgroupWordProduct H w.reverse := by
  intro w
  induction w with
  | nil =>
      intro x hx
      have hxone : x = 1 := by simpa [closedSubgroupWordProduct] using hx
      simp [hxone, closedSubgroupWordProduct]
  | cons i w ih =>
      intro x hx
      rcases Set.mem_mul.mp hx with ⟨a, ha, b, hb, rfl⟩
      rw [List.reverse_cons, wordSet_append, mul_inv_rev]
      exact Set.mem_mul.mpr ⟨b⁻¹, ih hb, a⁻¹,
        Set.mem_mul.mpr ⟨a⁻¹, (H i).inv_mem ha, 1, by simp [closedSubgroupWordProduct], mul_one _⟩,
        rfl⟩

private def repeatWord {ι : Type*} (w : List ι) : ℕ → List ι
  | 0 => []
  | n + 1 => repeatWord w n ++ w

omit [IsAlgClosed k] in
private lemma wordSet_repeatWord {G : Variety k} [AlgebraicGroup G]
    {ι : Type*} (H : ι → ClosedSubgroup G) (w : List ι) :
    ∀ n, closedSubgroupWordProduct H (repeatWord w n) = closedSubgroupWordProduct H w ^ n := by
  intro n
  induction n with
  | zero => exact Set.singleton_one
  | succ n ih =>
      rw [repeatWord, wordSet_append, ih, pow_succ]

private lemma inv_mem_set_pow_of_inv_mem
    {G : Type*} [Group G] {W : Set G}
    (hinv : ∀ {x}, x ∈ W → x⁻¹ ∈ W) :
    ∀ {n x}, x ∈ W ^ n → x⁻¹ ∈ W ^ n := by
  intro n
  induction n with
  | zero =>
      intro x hx
      have hxone : x = 1 := by simpa using hx
      simp [hxone]
  | succ n ih =>
      intro x hx
      rw [pow_succ] at hx
      rcases Set.mem_mul.mp hx with ⟨a, ha, b, hb, rfl⟩
      have hbinv : b⁻¹ ∈ W ^ 1 := by simpa using hinv hb
      have hainv : a⁻¹ ∈ W ^ n := ih ha
      rw [mul_inv_rev]
      have := Set.mem_mul.mpr ⟨b⁻¹, hbinv, a⁻¹, hainv, rfl⟩
      have heq : W ^ 1 * W ^ n = W ^ (n + 1) := by
        rw [← pow_add, Nat.add_comm]
      exact heq ▸ this

private lemma subgroupClosure_subset_iUnion_succ_pow
    {G : Type*} [Group G] {W : Set G} (hone : 1 ∈ W)
    (hinv : ∀ {x}, x ∈ W → x⁻¹ ∈ W) :
    (Subgroup.closure W : Set G) ⊆ ⋃ n, W ^ (n + 1) := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      exact Set.mem_iUnion.mpr ⟨0, by simpa using hx⟩
  | one =>
      exact Set.mem_iUnion.mpr ⟨0, by simpa using hone⟩
  | mul x y _ _ hx hy =>
      rcases Set.mem_iUnion.mp hx with ⟨m, hm⟩
      rcases Set.mem_iUnion.mp hy with ⟨n, hn⟩
      refine Set.mem_iUnion.mpr ⟨m + n + 1, ?_⟩
      have hxy := Set.mem_mul.mpr ⟨x, hm, y, hn, rfl⟩
      have hexp : (m + 1) + (n + 1) = (m + n + 1) + 1 := by omega
      rw [← hexp, pow_add]
      exact hxy
  | inv x _ hx =>
      rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
      exact Set.mem_iUnion.mpr ⟨n, inv_mem_set_pow_of_inv_mem hinv hn⟩

omit [IsAlgClosed k] in
private lemma wordSet_subset_append_singleton {G : Variety k} [AlgebraicGroup G]
    {ι : Type*} (H : ι → ClosedSubgroup G) (w : List ι) (i : ι) :
    closedSubgroupWordProduct H w ⊆ closedSubgroupWordProduct H (w ++ [i]) := by
  rw [wordSet_append]
  intro x hx
  exact Set.mem_mul.mpr ⟨x, hx, 1, one_mem_wordSet H [i], mul_one x⟩

omit [IsAlgClosed k] in
private lemma wordSet_subset_cons {G : Variety k} [AlgebraicGroup G]
    {ι : Type*} (H : ι → ClosedSubgroup G) (w : List ι) (i : ι) :
    closedSubgroupWordProduct H w ⊆ closedSubgroupWordProduct H (i :: w) := by
  intro x hx
  exact Set.mem_mul.mpr ⟨1, (H i).one_mem, x, hx, one_mul x⟩

omit [IsAlgClosed k] in
private lemma wordClosure_eq_of_subset_of_dimension_le
    {G : Variety k} [AlgebraicGroup G] {ι : Type*}
    (H : ι → ClosedSubgroup G)
    (hconn : ∀ i, _root_.IsConnected (H i : Set (Variety.Point G)))
    (u v : List ι)
    (huv : closure (closedSubgroupWordProduct H u) ⊆ closure (closedSubgroupWordProduct H v))
    (hdim : wordDimension H v ≤ wordDimension H u) :
    closure (closedSubgroupWordProduct H u) = closure (closedSubgroupWordProduct H v) := by
  apply Set.Subset.antisymm huv
  by_contra hnot
  have hproper : closure (closedSubgroupWordProduct H u) ⊂ closure (closedSubgroupWordProduct H v) := by
    refine ⟨huv, ?_⟩
    exact hnot
  have hcard := proper_irreducible_closed_subvariety_dimension_lt
    (wordClosureZariskiClosed H u) (wordClosure_isIrreducible H hconn u)
    (wordClosureZariskiClosed H v) (wordClosure_isIrreducible H hconn v)
    hproper
  have hnat : wordDimension H u < wordDimension H v :=
    Cardinal.toNat_lt_toNat hcard
      (variety_dimension_lt_aleph0 (wordClosureVariety H v))
  exact (Nat.not_lt_of_ge hdim) hnat

omit [IsAlgClosed k] in
private lemma maximal_wordClosure_cons_eq
    {G : Variety k} [AlgebraicGroup G] {ι : Type*}
    (H : ι → ClosedSubgroup G)
    (hconn : ∀ i, _root_.IsConnected (H i : Set (Variety.Point G)))
    (w : List ι) (hmax : ∀ v, wordDimension H v ≤ wordDimension H w)
    (i : ι) :
    closure (closedSubgroupWordProduct H (i :: w)) = closure (closedSubgroupWordProduct H w) := by
  symm
  apply wordClosure_eq_of_subset_of_dimension_le H hconn w (i :: w)
    (closure_mono (wordSet_subset_cons H w i))
  exact hmax (i :: w)

omit [IsAlgClosed k] in
private lemma maximal_wordClosure_append_eq
    {G : Variety k} [AlgebraicGroup G] {ι : Type*}
    (H : ι → ClosedSubgroup G)
    (hconn : ∀ i, _root_.IsConnected (H i : Set (Variety.Point G)))
    (w : List ι) (hmax : ∀ v, wordDimension H v ≤ wordDimension H w)
    (i : ι) :
    closure (closedSubgroupWordProduct H (w ++ [i])) = closure (closedSubgroupWordProduct H w) := by
  symm
  apply wordClosure_eq_of_subset_of_dimension_le H hconn w (w ++ [i])
    (closure_mono (wordSet_subset_append_singleton H w i))
  exact hmax (w ++ [i])

omit [IsAlgClosed k] in
private lemma maximal_wordClosure_mul_left_mem
    {G : Variety k} [AlgebraicGroup G] {ι : Type*}
    (H : ι → ClosedSubgroup G)
    (hconn : ∀ i, _root_.IsConnected (H i : Set (Variety.Point G)))
    (w : List ι) (hmax : ∀ v, wordDimension H v ≤ wordDimension H w)
    {i : ι} {a x : Variety.Point G} (ha : a ∈ H i)
    (hx : x ∈ closure (closedSubgroupWordProduct H w)) :
    a * x ∈ closure (closedSubgroupWordProduct H w) := by
  have hax : a * x ∈ closure (closedSubgroupWordProduct H (i :: w)) := by
    apply map_mem_closure (AlgebraicGroup.leftMulMorphism G a).continuous hx
    intro y hy
    rw [AlgebraicGroup.leftMulMorphism_apply]
    exact Set.mem_mul.mpr ⟨a, ha, y, hy, rfl⟩
  rwa [maximal_wordClosure_cons_eq H hconn w hmax i] at hax

omit [IsAlgClosed k] in
private lemma maximal_wordClosure_mul_right_mem
    {G : Variety k} [AlgebraicGroup G] {ι : Type*}
    (H : ι → ClosedSubgroup G)
    (hconn : ∀ i, _root_.IsConnected (H i : Set (Variety.Point G)))
    (w : List ι) (hmax : ∀ v, wordDimension H v ≤ wordDimension H w)
    {i : ι} {a x : Variety.Point G} (ha : a ∈ H i)
    (hx : x ∈ closure (closedSubgroupWordProduct H w)) :
    x * a ∈ closure (closedSubgroupWordProduct H w) := by
  have hxa : x * a ∈ closure (closedSubgroupWordProduct H (w ++ [i])) := by
    apply map_mem_closure (AlgebraicGroup.rightMulMorphism G a).continuous hx
    intro y hy
    rw [AlgebraicGroup.rightMulMorphism_apply, wordSet_append]
    exact Set.mem_mul.mpr ⟨y, hy, a,
      Set.mem_mul.mpr ⟨a, ha, 1, by simp [closedSubgroupWordProduct], mul_one a⟩, rfl⟩
  rwa [maximal_wordClosure_append_eq H hconn w hmax i] at hxa

private def leftSetwiseStabilizer {G : Type*} [Group G] (C : Set G) : Subgroup G where
  carrier := {g | ∀ x, x ∈ C ↔ g * x ∈ C}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb x
    rw [hb x, ha (b * x), mul_assoc]
  inv_mem' := by
    intro a ha x
    simpa using (ha (a⁻¹ * x)).symm

private def generatedSubgroup {G : Variety k} [AlgebraicGroup G]
    {ι : Type*} (H : ι → ClosedSubgroup G) : Subgroup (Variety.Point G) :=
  Subgroup.closure (⋃ i, (H i : Set (Variety.Point G)))

omit [IsAlgClosed k] in
private lemma wordSet_subset_generatedSubgroup
    {G : Variety k} [AlgebraicGroup G] {ι : Type*}
    (H : ι → ClosedSubgroup G) :
    ∀ w, closedSubgroupWordProduct H w ⊆ generatedSubgroup H := by
  intro w
  induction w with
  | nil =>
      intro x hx
      have hxone : x = 1 := by simpa [closedSubgroupWordProduct] using hx
      exact hxone ▸ (generatedSubgroup H).one_mem
  | cons i w ih =>
      rintro x ⟨a, ha, b, hb, rfl⟩
      apply (generatedSubgroup H).mul_mem
      · exact Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨i, ha⟩)
      · exact ih hb

omit [IsAlgClosed k] in
private lemma generatedSubgroup_mul_maximal_wordClosure_mem
    {G : Variety k} [AlgebraicGroup G] {ι : Type*}
    (H : ι → ClosedSubgroup G)
    (hconn : ∀ i, _root_.IsConnected (H i : Set (Variety.Point G)))
    (w : List ι) (hmax : ∀ v, wordDimension H v ≤ wordDimension H w)
    {a x : Variety.Point G} (ha : a ∈ generatedSubgroup H)
    (hx : x ∈ closure (closedSubgroupWordProduct H w)) :
    a * x ∈ closure (closedSubgroupWordProduct H w) := by
  let C := closure (closedSubgroupWordProduct H w)
  have hfactor (i : ι) : (H i).toSubgroup ≤ leftSetwiseStabilizer C := by
    intro b hb y
    constructor
    · exact maximal_wordClosure_mul_left_mem H hconn w hmax hb
    · intro hby
      have := maximal_wordClosure_mul_left_mem H hconn w hmax
        ((H i).inv_mem hb) hby
      simpa [mul_assoc] using this
  have hgen : generatedSubgroup H ≤ leftSetwiseStabilizer C := by
    apply (Subgroup.closure_le (leftSetwiseStabilizer C)).2
    intro b hb
    rcases Set.mem_iUnion.mp hb with ⟨i, hi⟩
    exact hfactor i hi
  exact (hgen ha x).mp hx

omit [IsAlgClosed k] in
private lemma generatedSubgroup_le_maximal_wordClosure
    {G : Variety k} [AlgebraicGroup G] {ι : Type*}
    (H : ι → ClosedSubgroup G)
    (hconn : ∀ i, _root_.IsConnected (H i : Set (Variety.Point G)))
    (w : List ι) (hmax : ∀ v, wordDimension H v ≤ wordDimension H w) :
    (generatedSubgroup H : Set (Variety.Point G)) ⊆ closure (closedSubgroupWordProduct H w) := by
  intro a ha
  simpa using generatedSubgroup_mul_maximal_wordClosure_mem H hconn w hmax ha
    (subset_closure (one_mem_wordSet H w))

private noncomputable def maximalWordClosedSubgroup
    {G : Variety k} [AlgebraicGroup G] {ι : Type*}
    (H : ι → ClosedSubgroup G)
    (hconn : ∀ i, _root_.IsConnected (H i : Set (Variety.Point G)))
    (w : List ι) (hmax : ∀ v, wordDimension H v ≤ wordDimension H w) :
    ClosedSubgroup G := by
  let C := closure (closedSubgroupWordProduct H w)
  let J := generatedSubgroup H
  have hwordJ : closedSubgroupWordProduct H w ⊆ J := wordSet_subset_generatedSubgroup H w
  have hJC : (J : Set (Variety.Point G)) ⊆ C :=
    generatedSubgroup_le_maximal_wordClosure H hconn w hmax
  let K : Subgroup (Variety.Point G) :=
    { carrier := C
      one_mem' := subset_closure (one_mem_wordSet H w)
      mul_mem' := by
        intro x y hx hy
        have hxJ : x ∈ closure (J : Set (Variety.Point G)) :=
          closure_mono hwordJ hx
        apply (Set.MapsTo.closure_left ?_
          (AlgebraicGroup.rightMulMorphism G y).continuous isClosed_closure) hxJ
        intro a ha
        rw [AlgebraicGroup.rightMulMorphism_apply]
        exact generatedSubgroup_mul_maximal_wordClosure_mem H hconn w hmax ha hy
      inv_mem' := by
        intro x hx
        have hxJ : x ∈ closure (J : Set (Variety.Point G)) :=
          closure_mono hwordJ hx
        apply (Set.MapsTo.closure_left ?_
          (AlgebraicGroup.invMorphism G).continuous isClosed_closure) hxJ
        intro a ha
        exact hJC (J.inv_mem ha) }
  exact ClosedSubgroup.ofSubgroup K (wordClosureZariskiClosed H w)

omit [IsAlgClosed k] in
private lemma maximalWordClosedSubgroup_carrier
    {G : Variety k} [AlgebraicGroup G] {ι : Type*}
    (H : ι → ClosedSubgroup G)
    (hconn : ∀ i, _root_.IsConnected (H i : Set (Variety.Point G)))
    (w : List ι) (hmax : ∀ v, wordDimension H v ≤ wordDimension H w) :
    (maximalWordClosedSubgroup H hconn w hmax : Set (Variety.Point G)) =
      closure (closedSubgroupWordProduct H w) := rfl

private lemma exists_wordProduct_eq_maximal_wordClosure
    {G : Variety k} [AlgebraicGroup G] {ι : Type*}
    (H : ι → ClosedSubgroup G)
    (hconn : ∀ i, _root_.IsConnected (H i : Set (Variety.Point G)))
    (w : List ι) (hmax : ∀ v, wordDimension H v ≤ wordDimension H w) :
  ∃ v : List ι,
      closedSubgroupWordProduct H v =
        closure (closedSubgroupWordProduct H w) := by
  let C := maximalWordClosedSubgroup H hconn w hmax
  have hmap (x : Variety.Point (wordVariety H w)) :
      (wordMorphism H w).toFun x ∈ C.toSubgroup := by
    change (wordMorphism H w).toFun x ∈ closure (closedSubgroupWordProduct H w)
    apply subset_closure
    rw [← wordMorphism_range H w]
    exact Set.mem_range_self x
  let f := morphism_codRestrictClosedSubgroup (wordMorphism H w) C hmap
  let eC := Variety.closedSubvarietyPointHomeomorph C.isZariskiClosed
  have hCinc : C.inclusion.onPoints =
      (fun x : Variety.Point C.carrierVariety => (eC x).1) := rfl
  have hCinducing : Topology.IsInducing C.inclusion.onPoints := by
    rw [hCinc]
    exact Topology.IsInducing.subtypeVal.comp eC.isInducing
  have hfimage : C.inclusion.onPoints '' Set.range f.toFun = closedSubgroupWordProduct H w := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      rw [morphism_codRestrictClosedSubgroup_inclusion]
      rw [← wordMorphism_range H w]
      exact Set.mem_range_self z
    · intro hx
      rw [← wordMorphism_range H w] at hx
      rcases hx with ⟨z, rfl⟩
      refine ⟨f.toFun z, Set.mem_range_self z, ?_⟩
      exact morphism_codRestrictClosedSubgroup_inclusion _ _ _ z
  let : Nonempty (Variety.Point C.carrierVariety) := by
    exact ⟨C.pointEquiv.symm ⟨1, by
      change (1 : Variety.Point G) ∈ closure (closedSubgroupWordProduct H w)
      exact subset_closure (one_mem_wordSet H w)⟩⟩
  have hCirr : IsIrreducible (C : Set (Variety.Point G)) := by
    change IsIrreducible (closure (closedSubgroupWordProduct H w))
    exact wordClosure_isIrreducible H hconn w
  let : IrreducibleSpace {x : Variety.Point G // x ∈ (C : Set _)} :=
    Subtype.irreducibleSpace hCirr
  have hCirrSpace : IrreducibleSpace (Variety.Point C.carrierVariety) :=
    eC.irreducibleSpace_iff.mpr inferInstance
  let : IrreducibleSpace (Variety.Point C.carrierVariety) := hCirrSpace
  have hfdense : Dense (Set.range f.toFun) := by
    rw [hCinducing.dense_iff]
    intro x
    rw [hfimage]
    change C.inclusion.onPoints x ∈ (C : Set (Variety.Point G))
    exact (C.pointEquiv x).property
  obtain ⟨U, hUopen, hUne, hUsub⟩ :=
    f.exists_nonempty_open_subset_range_of_dense hfdense
  have hUword : C.inclusion.onPoints '' U ⊆ closedSubgroupWordProduct H w := by
    intro x hx
    rw [← hfimage]
    rcases hx with ⟨y, hyU, rfl⟩
    exact ⟨y, hUsub hyU, rfl⟩
  obtain ⟨a, haU⟩ := hUne
  have haWord : C.inclusion.onPoints a ∈ closedSubgroupWordProduct H w :=
    hUword ⟨a, haU, rfl⟩
  let V : Set (Variety.Point C.carrierVariety) :=
    (Homeomorph.mulLeft a⁻¹) '' U
  have hVopen : IsOpen V :=
    (Homeomorph.mulLeft a⁻¹).isOpenMap U hUopen
  have hVone : (1 : Variety.Point C.carrierVariety) ∈ V := by
    exact ⟨a, haU, by simp [Homeomorph.mulLeft]⟩
  let q := w.reverse ++ w
  have hVword : C.inclusion.onPoints '' V ⊆ closedSubgroupWordProduct H q := by
    rintro z ⟨x, hxV, rfl⟩
    change x ∈ (Homeomorph.mulLeft a⁻¹) '' U at hxV
    rcases hxV with ⟨y, hyU, rfl⟩
    rw [show q = w.reverse ++ w by rfl, wordSet_append]
    refine Set.mem_mul.mpr ⟨(C.inclusion.onPoints a)⁻¹,
      inv_mem_wordSet_reverse H haWord, C.inclusion.onPoints y,
      hUword ⟨y, hyU, rfl⟩, ?_⟩
    simp [Homeomorph.mulLeft]
  let invHomeomorph : Variety.Point C.carrierVariety ≃ₜ
      Variety.Point C.carrierVariety :=
    { toEquiv := Equiv.inv (Variety.Point C.carrierVariety)
      continuous_toFun := (AlgebraicGroup.invMorphism C.carrierVariety).continuous
      continuous_invFun := (AlgebraicGroup.invMorphism C.carrierVariety).continuous }
  let W := V ∩ V⁻¹
  have hVinvOpen : IsOpen V⁻¹ := by
    change IsOpen (invHomeomorph ⁻¹' V)
    exact hVopen.preimage invHomeomorph.continuous
  have hWopen : IsOpen W := hVopen.inter hVinvOpen
  have hWone : (1 : Variety.Point C.carrierVariety) ∈ W := by
    refine ⟨hVone, ?_⟩
    have : (1 : Variety.Point C.carrierVariety)⁻¹ ∈ V⁻¹ :=
      Set.inv_mem_inv.mpr hVone
    simpa using this
  have hWinv : ∀ {x : Variety.Point C.carrierVariety}, x ∈ W → x⁻¹ ∈ W := by
    intro x hx
    refine ⟨?_, Set.inv_mem_inv.mpr hx.1⟩
    apply Set.inv_mem_inv.mp
    simpa using hx.2
  let L : Subgroup (Variety.Point C.carrierVariety) := Subgroup.closure W
  have hLopen : IsOpen (L : Set (Variety.Point C.carrierVariety)) :=
    Subgroup.isOpen_of_mem_nhds L
      (Filter.mem_of_superset (hWopen.mem_nhds hWone) Subgroup.subset_closure)
  have hLdense : Dense (L : Set (Variety.Point C.carrierVariety)) :=
    hLopen.dense ⟨1, L.one_mem⟩
  have hLclosed : IsClosed (L : Set (Variety.Point C.carrierVariety)) :=
    Subgroup.isClosed_of_isOpen L hLopen
  have hLeq : (L : Set (Variety.Point C.carrierVariety)) = Set.univ := by
    rw [← hLdense.closure_eq, hLclosed.closure_eq]
  have hcover : (Set.univ : Set (Variety.Point C.carrierVariety)) ⊆
      ⋃ n, W ^ (n + 1) := by
    rw [← hLeq]
    exact subgroupClosure_subset_iUnion_succ_pow hWone hWinv
  have hpowersOpen : ∀ n : ℕ, IsOpen (W ^ (n + 1)) := by
    intro n
    rw [pow_succ]
    exact hWopen.mul_left
  have hpowersMono : Monotone (fun n : ℕ => W ^ (n + 1)) := by
    intro m n hmn
    exact Set.pow_subset_pow_right hWone (Nat.add_le_add_right hmn 1)
  obtain ⟨n, hn⟩ :=
    (TopologicalSpace.NoetherianSpace.isCompact
      (Set.univ : Set (Variety.Point C.carrierVariety))).elim_directed_cover
      (fun n : ℕ => W ^ (n + 1)) hpowersOpen hcover hpowersMono.directed_le
  have hWword : C.inclusion.onPoints '' W ⊆ closedSubgroupWordProduct H q := by
    rintro x ⟨y, hyW, rfl⟩
    exact hVword ⟨y, hyW.1, rfl⟩
  let v := repeatWord q (n + 1)
  refine ⟨v, Set.Subset.antisymm ?_ ?_⟩
  · exact (wordSet_subset_generatedSubgroup H v).trans
      (generatedSubgroup_le_maximal_wordClosure H hconn w hmax)
  intro x hxC
  obtain ⟨y, hy⟩ := C.range_inclusion.ge hxC
  have hyPow : y ∈ W ^ (n + 1) := hn (Set.mem_univ y)
  have hxImage : x ∈ C.inclusion.onPoints '' (W ^ (n + 1)) :=
    ⟨y, hyPow, hy⟩
  rw [Set.image_pow] at hxImage
  have hxWordPow : x ∈ closedSubgroupWordProduct H q ^ (n + 1) :=
    Set.pow_subset_pow_left hWword hxImage
  rw [← wordSet_repeatWord H q (n + 1)] at hxWordPow
  exact hxWordPow

/-- An arbitrary family of connected closed algebraic subgroups generates its
abstract subgroup after one finite word of factors. -/
public theorem exists_closedSubgroupWordProduct_eq_closure_iUnion
    {G : Variety k} [AlgebraicGroup G] {ι : Type*}
    (H : ι → ClosedSubgroup G)
    (hconn : ∀ i, _root_.IsConnected (H i : Set (Variety.Point G))) :
    ∃ w : List ι,
      closedSubgroupWordProduct H w =
        (Subgroup.closure (⋃ i, (H i : Set (Variety.Point G))) :
          Set (Variety.Point G)) := by
  obtain ⟨u, hu⟩ := exists_word_max_dimension H
  obtain ⟨w, hw⟩ := exists_wordProduct_eq_maximal_wordClosure H hconn u hu
  refine ⟨w, ?_⟩
  let J := generatedSubgroup H
  have hJC : (J : Set (Variety.Point G)) ⊆
      closure (closedSubgroupWordProduct H u) :=
    generatedSubgroup_le_maximal_wordClosure H hconn u hu
  have hCJ : closure (closedSubgroupWordProduct H u) ⊆ J := by
    rw [← hw]
    exact wordSet_subset_generatedSubgroup H w
  change closedSubgroupWordProduct H w = (J : Set (Variety.Point G))
  rw [hw]
  exact Set.Subset.antisymm hCJ hJC

/-- The subgroup generated by any family of connected closed algebraic
subgroups is Zariski closed. -/
public theorem closure_iUnion_connected_closedSubgroup_isZariskiClosed
    {G : Variety k} [AlgebraicGroup G] {ι : Type*}
    (H : ι → ClosedSubgroup G)
    (hconn : ∀ i, _root_.IsConnected (H i : Set (Variety.Point G))) :
    IsZariskiClosed G
      (Subgroup.closure (⋃ i, (H i : Set (Variety.Point G))) :
        Set (Variety.Point G)) := by
  obtain ⟨u, hu⟩ := exists_word_max_dimension H
  obtain ⟨w, hw⟩ := exists_wordProduct_eq_maximal_wordClosure H hconn u hu
  have hJC := generatedSubgroup_le_maximal_wordClosure H hconn u hu
  have hCJ : closure (closedSubgroupWordProduct H u) ⊆ generatedSubgroup H := by
    rw [← hw]
    exact wordSet_subset_generatedSubgroup H w
  have heq : (generatedSubgroup H : Set (Variety.Point G)) =
      closure (closedSubgroupWordProduct H u) :=
    Set.Subset.antisymm hJC hCJ
  change IsZariskiClosed G (generatedSubgroup H : Set (Variety.Point G))
  rw [heq]
  exact wordClosureZariskiClosed H u

/-- The subgroup generated by any family of connected closed algebraic
subgroups is connected. -/
public theorem closure_iUnion_connected_closedSubgroup_isConnected
    {G : Variety k} [AlgebraicGroup G] {ι : Type*}
    (H : ι → ClosedSubgroup G)
    (hconn : ∀ i, _root_.IsConnected (H i : Set (Variety.Point G))) :
    _root_.IsConnected
      (Subgroup.closure (⋃ i, (H i : Set (Variety.Point G))) :
        Set (Variety.Point G)) := by
  obtain ⟨w, hw⟩ :=
    exists_closedSubgroupWordProduct_eq_closure_iUnion H hconn
  rw [← hw]
  exact closedSubgroupWordProduct_isConnected H hconn w

end Theory.AlgebraicGroup
