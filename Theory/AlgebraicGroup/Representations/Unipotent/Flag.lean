module

public import Theory.AlgebraicGroup.Representations.Unipotent.Basic

universe u v w

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

/-- A full finite-dimensional submodule chain admits a basis whose first `m`
vectors span the `m`th member of the chain. -/
public lemma exists_basis_adapted_to_full_submodule_chain
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (F : ℕ → Submodule k V) (hmono : Monotone F)
    (hdim : ∀ i, Module.finrank k (F i) = min i (Module.finrank k V)) :
    ∃ b : Module.Basis (Fin (Module.finrank k V)) k V,
      ∀ (m : ℕ) (hm : m ≤ Module.finrank k V),
        F m = Submodule.span k (Set.range fun i : Fin m =>
          b (Fin.castLE hm i)) := by
  let n := Module.finrank k V
  have hstrict (i : Fin n) : F i < F (i + 1) := by
    apply lt_of_le_of_ne (hmono (Nat.le_succ i))
    intro heq
    have heqdim := congrArg (fun W : Submodule k V => Module.finrank k W) heq
    rw [hdim, hdim, Nat.min_eq_left (Nat.le_of_lt i.isLt),
      Nat.min_eq_left (by omega)] at heqdim
    omega
  choose vec hvecmem hvecnot using fun i : Fin n => SetLike.exists_of_lt (hstrict i)
  have hliPrefix : ∀ m : ℕ, ∀ hm : m ≤ n,
      LinearIndependent k (fun i : Fin m => vec (Fin.castLE hm i)) := by
    intro m
    induction m with
    | zero =>
        intro hm
        exact linearIndependent_empty_type
    | succ m ih =>
        intro hm
        rw [linearIndependent_finSucc']
        constructor
        · convert ih (Nat.le_trans (Nat.le_succ m) hm) using 1
          ext i
          rfl
        · have hspanle : Submodule.span k
              (Set.range (Fin.init (fun i : Fin (m + 1) => vec (Fin.castLE hm i)))) ≤ F m := by
            rw [Submodule.span_le]
            rintro x ⟨i, rfl⟩
            exact hmono (Nat.succ_le_iff.mpr i.isLt)
              (hvecmem (Fin.castLE hm (Fin.castSucc i)))
          intro hlast
          apply hvecnot (Fin.castLE hm (Fin.last m))
          exact hspanle hlast
  have hli : LinearIndependent k vec := by
    simpa [n] using hliPrefix n le_rfl
  let b : Module.Basis (Fin n) k V :=
    basisOfLinearIndependentOfCardEqFinrank' vec hli (by simp [n])
  refine ⟨b, ?_⟩
  intro m hm
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']
    exact hmono (show (Fin.castLE hm i : ℕ) + 1 ≤ m by
      exact Nat.succ_le_of_lt i.isLt) (hvecmem (Fin.castLE hm i))
  · have hli' : LinearIndependent k (fun i : Fin m =>
        b (Fin.castLE hm i)) := by
      rw [coe_basisOfLinearIndependentOfCardEqFinrank']
      convert hli.comp (Fin.castLE hm) (Fin.castLE_injective hm) using 1
      funext i
      rfl
    rw [finrank_span_eq_card hli', Fintype.card_fin, hdim,
      Nat.min_eq_left hm]

end

namespace Subrepresentation

section

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [Group Γ] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- Pulling back a one-dimensional quotient subrepresentation produces a
strict invariant extension whose finrank is exactly one larger. -/
private lemma exists_strictSuper_finrank_succ_of_quotient_finrank_eq_one
    (ρ : Representation k Γ V) (σ : _root_.Subrepresentation ρ)
    (τ : _root_.Subrepresentation
      (ρ.quotient σ.toSubmodule
        (fun g => σ.apply_mem_toSubmodule g)))
    (hτdim : Module.finrank k τ.toSubmodule = 1) :
    ∃ υ : _root_.Subrepresentation ρ,
      σ < υ ∧ Module.finrank k υ.toSubmodule =
        Module.finrank k σ.toSubmodule + 1 := by
  let W : Submodule k V := τ.toSubmodule.comap σ.toSubmodule.mkQ
  have hW (g : Γ) : W ≤ W.comap (ρ g) := by
    intro v hv
    change σ.toSubmodule.mkQ (ρ g v) ∈ τ.toSubmodule
    have hτv := τ.apply_mem_toSubmodule g hv
    simpa [Representation.quotient] using hτv
  let υ : _root_.Subrepresentation ρ :=
    { toSubmodule := W
      apply_mem_toSubmodule := hW }
  have hσυ : σ ≤ υ := by
    intro v hv
    change σ.toSubmodule.mkQ v ∈ τ.toSubmodule
    have hvzero : σ.toSubmodule.mkQ v = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact hv
    rw [hvzero]
    exact τ.toSubmodule.zero_mem
  have hτne : τ.toSubmodule ≠ ⊥ := by
    intro hτ
    have hzero : Module.finrank k τ.toSubmodule = 0 :=
      Submodule.finrank_eq_zero.mpr hτ
    omega
  let : Nontrivial τ.toSubmodule :=
    Submodule.nontrivial_iff_ne_bot.mpr hτne
  obtain ⟨z, hz⟩ := exists_ne (0 : τ.toSubmodule)
  obtain ⟨v, hv⟩ := σ.toSubmodule.mkQ_surjective z
  have hstrict : σ < υ := by
    refine SetLike.lt_iff_le_and_exists.mpr ⟨hσυ, v, ?_, ?_⟩
    · change σ.toSubmodule.mkQ v ∈ τ.toSubmodule
      rw [hv]
      exact z.property
    · intro hvσ
      have hvzero : σ.toSubmodule.mkQ v = 0 := by
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
        exact hvσ
      apply hz
      apply Subtype.ext
      simpa [hvzero] using hv.symm
  let f₀ : W →ₗ[k] (V ⧸ σ.toSubmodule) :=
    σ.toSubmodule.mkQ.comp W.subtype
  let f : W →ₗ[k] τ.toSubmodule :=
    f₀.codRestrict τ.toSubmodule (fun x => x.property)
  have hf0range : LinearMap.range f₀ = τ.toSubmodule := by
    apply le_antisymm
    · rintro z ⟨x, rfl⟩
      exact x.property
    · intro z hz
      obtain ⟨v, hv⟩ := σ.toSubmodule.mkQ_surjective z
      have hvW : v ∈ W := by
        change σ.toSubmodule.mkQ v ∈ τ.toSubmodule
        rw [hv]
        exact hz
      exact ⟨⟨v, hvW⟩, by simp [f₀, hv]⟩
  have hfrange : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro x
    have hx : x.1 ∈ LinearMap.range f₀ := by
      rw [hf0range]
      exact x.property
    rcases hx with ⟨w, hw⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    exact hw
  have hfker : LinearMap.ker f = σ.toSubmodule.comap W.subtype := by
    ext x
    constructor
    · intro hx
      change x.1 ∈ σ.toSubmodule
      have hf₀x : f₀ x = 0 := by
        exact congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      have hmk : σ.toSubmodule.mkQ x.1 = 0 := by
        simpa [f₀] using hf₀x
      rw [← LinearMap.mem_ker] at hmk
      rwa [Submodule.ker_mkQ] at hmk
    · intro hx
      apply LinearMap.mem_ker.mpr
      have hmk : σ.toSubmodule.mkQ x.1 = 0 := by
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
        exact hx
      apply Subtype.ext
      exact hmk
  have hσW : σ.toSubmodule ≤ W := by
    intro v hv
    change σ.toSubmodule.mkQ v ∈ τ.toSubmodule
    rw [show σ.toSubmodule.mkQ v = 0 by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact hv]
    exact τ.toSubmodule.zero_mem
  have hkerdim : Module.finrank k (LinearMap.ker f) =
      Module.finrank k σ.toSubmodule := by
    rw [hfker]
    exact (Submodule.comapSubtypeEquivOfLe hσW).finrank_eq
  have hdim := LinearMap.finrank_range_add_finrank_ker f
  have hυdim : Module.finrank k υ.toSubmodule =
      Module.finrank k σ.toSubmodule + 1 := by
    calc
      Module.finrank k υ.toSubmodule =
          Module.finrank k (LinearMap.range f) +
            Module.finrank k (LinearMap.ker f) := by
        rw [show υ.toSubmodule = W from rfl]
        exact hdim.symm
      _ = Module.finrank k τ.toSubmodule +
            Module.finrank k σ.toSubmodule := by
        rw [hfrange, finrank_top, hkerdim]
      _ = Module.finrank k σ.toSubmodule + 1 := by
        rw [hτdim, Nat.add_comm]
  exact ⟨υ, hstrict, hυdim⟩

end

section

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [IsAlgClosed k] [Group Γ]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A pointwise-unipotent representation strictly extends every invariant
subrepresentation of smaller finrank by exactly one dimension. -/
private lemma exists_strictSuper_finrank_succ_of_finrank_lt_of_pointwise_unipotent
    (ρ : Representation k Γ V) (σ : _root_.Subrepresentation ρ)
    (hunipotent : ∀ g : Γ, IsNilpotent (ρ g - 1))
    (hσdim : Module.finrank k σ.toSubmodule < Module.finrank k V) :
    ∃ υ : _root_.Subrepresentation ρ,
      σ < υ ∧ Module.finrank k υ.toSubmodule =
        Module.finrank k σ.toSubmodule + 1 := by
  let q := ρ.quotient σ.toSubmodule
    (fun g => σ.apply_mem_toSubmodule g)
  have hqfin : 0 < Module.finrank k (V ⧸ σ.toSubmodule) := by
    have hsum := Submodule.finrank_quotient_add_finrank σ.toSubmodule
    omega
  let : Nontrivial (V ⧸ σ.toSubmodule) := Module.finrank_pos_iff.mp hqfin
  have hqUnipotent : ∀ g : Γ, IsNilpotent (q g - 1) :=
    Representation.isNilpotent_quotient_sub_one ρ σ.toSubmodule
      (fun g => σ.apply_mem_toSubmodule g) hunipotent
  obtain ⟨τ, hτdim⟩ :=
    unipotentRepresentation_exists_oneDimensional_subrepresentation q hqUnipotent
  exact exists_strictSuper_finrank_succ_of_quotient_finrank_eq_one ρ σ τ hτdim

end

section

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [IsAlgClosed k] [Group Γ]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A pointwise-unipotent representation admits a strictly increasing stable
chain indexed by all dimensions from zero to the ambient finrank. -/
public lemma exists_finrank_strictMono_chain_of_pointwise_unipotent
    (ρ : Representation k Γ V)
    (hunipotent : ∀ g : Γ, IsNilpotent (ρ g - 1)) :
    ∃ F : Fin (Module.finrank k V + 1) → _root_.Subrepresentation ρ,
      (∀ i, Module.finrank k (F i).toSubmodule = i) ∧ StrictMono F := by
  let n := Module.finrank k V
  let step : _root_.Subrepresentation ρ → _root_.Subrepresentation ρ := fun σ =>
    if h : Module.finrank k σ.toSubmodule < n then
      (exists_strictSuper_finrank_succ_of_finrank_lt_of_pointwise_unipotent
        ρ σ hunipotent h).choose
    else ⊤
  have hstep (σ : _root_.Subrepresentation ρ)
      (hσ : Module.finrank k σ.toSubmodule < n) :
      Module.finrank k (step σ).toSubmodule =
        Module.finrank k σ.toSubmodule + 1 := by
    let υ := (exists_strictSuper_finrank_succ_of_finrank_lt_of_pointwise_unipotent
      ρ σ hunipotent hσ).choose
    have hυ : step σ = υ := by
      dsimp [step, υ]
      rw [dif_pos hσ]
    rw [hυ]
    exact (exists_strictSuper_finrank_succ_of_finrank_lt_of_pointwise_unipotent
      ρ σ hunipotent hσ).choose_spec.2
  let F : ℕ → _root_.Subrepresentation ρ :=
    Nat.rec ({ toSubmodule := ⊥, apply_mem_toSubmodule := by simp })
      (fun _ σ => step σ)
  have hF : ∀ m : ℕ, m ≤ n →
      Module.finrank k (F m).toSubmodule = m := by
    intro m
    induction m with
    | zero =>
        intro hm
        dsimp [F]
        exact finrank_bot k V
    | succ m ih =>
        intro hm
        have hm' : m ≤ n := le_trans (Nat.le_succ m) hm
        have hmlt : Module.finrank k (F m).toSubmodule < n := by
          rw [ih hm']
          omega
        rw [show F (m + 1) = step (F m) by rfl,
          hstep (F m) hmlt, ih hm']
  have hsucc : ∀ m : ℕ, m < n → F m < F (m + 1) := by
    intro m hm
    have hdim := hF m (Nat.le_of_lt hm)
    have hstepdim := hF (m + 1) (Nat.succ_le_iff.mpr hm)
    apply lt_of_le_of_ne (show F m ≤ F (m + 1) from by
      rw [show F (m + 1) = step (F m) by rfl]
      dsimp [step]
      split
      · rename_i h
        exact (exists_strictSuper_finrank_succ_of_finrank_lt_of_pointwise_unipotent
          ρ (F m) hunipotent h).choose_spec.1.le
      · rename_i h
        exact False.elim (h (by rw [hdim]; omega)))
    intro heq
    have := congrArg
      (fun σ : _root_.Subrepresentation ρ => Module.finrank k σ.toSubmodule) heq
    omega
  refine ⟨fun i => F i, ?_, ?_⟩
  · intro i
    exact hF i (Nat.le_of_lt_succ i.isLt)
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    exact hsucc i i.isLt

end

section

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [Group Γ] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

omit [FiniteDimensional k V] in
/-- Stability of the adapted initial spans forces each basis vector's image into
its corresponding prefix span. -/
private lemma representation_map_basisVector_mem_prefixSpan
    (ρ : Representation k Γ V)
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (F : ℕ → Submodule k V)
    (hstable : ∀ (i : ℕ) (g : Γ), F i ≤ (F i).comap (ρ g))
    (hb : ∀ (m : ℕ) (hm : m ≤ n),
      F m = Submodule.span k (Set.range fun i : Fin m =>
        b (Fin.castLE hm i)))
    (j : Fin n) (g : Γ) :
    ρ g (b j) ∈ Submodule.span k (Set.range fun i : Fin (j + 1) =>
      b (Fin.castLE (Nat.succ_le_of_lt j.isLt) i)) := by
  have hjmem : b j ∈ F (j + 1) := by
    rw [hb (j + 1) (Nat.succ_le_of_lt j.isLt)]
    refine Submodule.subset_span ⟨Fin.last j.val, ?_⟩
    congr 1
  have hmap : ρ g (b j) ∈ F (j + 1) :=
    hstable (j + 1) g hjmem
  rw [hb (j + 1) (Nat.succ_le_of_lt j.isLt)] at hmap
  exact hmap

end

section

variable {k : Type u} {V : Type w}
  [Field k] [AddCommGroup V] [Module k V]

/-- A basis vector image has zero coordinates strictly below its diagonal position. -/
private lemma representation_map_basisVector_coord_eq_zero_of_lt
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    {j i : Fin n} (hji : j < i)
    {x : V}
    (hx : x ∈ Submodule.span k (Set.range fun l : Fin (j + 1) =>
      b (Fin.castLE (Nat.succ_le_of_lt j.isLt) l))) :
    (b.coord i) x = 0 := by
  refine Submodule.span_induction (R := k)
    (s := Set.range fun l : Fin (j + 1) =>
      b (Fin.castLE (Nat.succ_le_of_lt j.isLt) l))
    (p := fun x _ => (b.coord i) x = 0) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨l, rfl⟩
    rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    have hne : (Fin.castLE (Nat.succ_le_of_lt j.isLt) l : Fin n) ≠ i := by
      intro heq
      have hlj : (Fin.castLE (Nat.succ_le_of_lt j.isLt) l : ℕ) ≤ j := by
        change l.val ≤ j.val
        omega
      have hli : (Fin.castLE (Nat.succ_le_of_lt j.isLt) l : ℕ) < i :=
        lt_of_le_of_lt hlj hji
      exact (ne_of_lt hli) (congrArg Fin.val heq)
    simp [hne]
  · simp
  · intro x y hx hy hx' hy'
    simpa [map_add] using congrArg₂ (· + ·) hx' hy'
  · intro a x hx hx'
    simpa [map_smul] using congrArg (a * ·) hx'

end

section

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [Group Γ] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

omit [FiniteDimensional k V] in
/-- The matrix of a representation preserving an adapted stable chain is
upper triangular in the adapted basis. -/
private lemma representation_map_basisVector_coord_eq_zero_of_lt_of_stable_chain
    (ρ : Representation k Γ V)
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (F : ℕ → Submodule k V)
    (hstable : ∀ (m : ℕ) (g : Γ), F m ≤ (F m).comap (ρ g))
    (hb : ∀ (m : ℕ) (hm : m ≤ n),
      F m = Submodule.span k (Set.range fun l : Fin m =>
        b (Fin.castLE hm l)))
    {j i : Fin n} (hji : j < i) (g : Γ) :
    (b.coord i) (ρ g (b j)) = 0 := by
  apply representation_map_basisVector_coord_eq_zero_of_lt b hji
  exact representation_map_basisVector_mem_prefixSpan ρ b F hstable hb j g

end

section

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [Group Γ] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

omit [FiniteDimensional k V] in
/-- The matrix of a stable-chain representation has no entries below the
diagonal in the adapted basis. -/
public lemma representation_toMatrix_basis_belowDiagonal_eq_zero
    (ρ : Representation k Γ V)
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (F : ℕ → Submodule k V)
    (hstable : ∀ (m : ℕ) (g : Γ), F m ≤ (F m).comap (ρ g))
    (hb : ∀ (m : ℕ) (hm : m ≤ n),
      F m = Submodule.span k (Set.range fun l : Fin m =>
        b (Fin.castLE hm l)))
    (g : Γ) {j i : Fin n} (hji : j < i) :
    (LinearMap.toMatrix b b (ρ g)) i j = 0 := by
  rw [LinearMap.toMatrix_apply, ← Module.Basis.coord_apply]
  exact representation_map_basisVector_coord_eq_zero_of_lt_of_stable_chain
    ρ b F hstable hb hji g

end

end Subrepresentation

end Theory.AlgebraicGroup
