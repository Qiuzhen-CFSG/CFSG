/-
Authors: Tianjiao Nie
-/

module

public import FeitThompson.BGsection1.Defs

open scoped commutatorElement

variable {G : Type _} [Group G] (p : ℕ) (S : Sylow p G)

/-- The focal subgroup `F` as defined in Theorem 1.17. -/
def focalSubgroup : Subgroup G :=
  Subgroup.closure {z : G | ∃ x : G, x ∈ (S : Subgroup G) ∧ ∃ y : G, y ∈ (S : Subgroup G) ∧
    IsConj x y ∧ z = x⁻¹ * y}

/-- The focal subgroup is contained in the Sylow subgroup `S`. -/
lemma focalSubgroup_le_sylow : focalSubgroup p S ≤ (S : Subgroup G) := by
  unfold focalSubgroup
  apply (Subgroup.closure_le (K := (S : Subgroup G))).2
  intro z hz
  rcases hz with ⟨x, hx, y, hy, _, rfl⟩
  exact (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hx) hy

/-- Conjugation preserves the relation `IsConj`. -/
lemma isConj_conj {x y : G} (h : IsConj x y) (g : G) : IsConj (g * x * g⁻¹) (g * y * g⁻¹) := by
  simpa using MonoidHom.map_isConj (f := (MulAut.conj g).toMonoidHom) h

/-- The focal subgroup is normal in `S`. -/
instance focalSubgroup_normal_in_sylow : ((focalSubgroup p S).subgroupOf (S : Subgroup G)).Normal := by
  have hF_le : focalSubgroup p S ≤ S := focalSubgroup_le_sylow p S
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hF_le).mpr ?_
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro f
  have conj_mem : ∀ h, h ∈ (S : Subgroup G) → ∀ x, x ∈ focalSubgroup p S → h * x * h⁻¹ ∈ focalSubgroup p S := by
    intro h hh x hx
    unfold focalSubgroup at hx
    refine Subgroup.closure_induction (p := fun z hz => h * z * h⁻¹ ∈ focalSubgroup p S) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with ⟨a, ha, b, hb, hab, rfl⟩
      refine Subgroup.subset_closure ⟨h * a * h⁻¹, ?_, h * b * h⁻¹, ?_, isConj_conj hab h, ?_⟩
      · exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hh ha) ((S : Subgroup G).inv_mem hh)
      · exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hh hb) ((S : Subgroup G).inv_mem hh)
      · group
    · -- one
      simp
    · -- multiplication
      intro a b ha hb ha' hb'
      simpa [mul_assoc] using (focalSubgroup p S).mul_mem ha' hb'
    · -- inverse
      intro a ha ha'
      simpa [mul_assoc] using (focalSubgroup p S).inv_mem ha'
  constructor
  · intro hf
    exact conj_mem g hg f hf
  · intro hf'
    have hg_inv : g⁻¹ ∈ (S : Subgroup G) := (S : Subgroup G).inv_mem hg
    have := conj_mem g⁻¹ hg_inv (g * f * g⁻¹) hf'
    -- compute: g⁻¹ * (g * f * g⁻¹) * (g⁻¹)⁻¹ = f
    have H : g⁻¹ * (g * f * g⁻¹) * (g⁻¹)⁻¹ = f := by group
    rw [H] at this
    exact this

/-- For any `a, b ∈ S`, the element `(a b)⁻¹ * (b a)` belongs to `F`. -/
lemma commutator_mem_focalSubgroup (a b : G) (ha : a ∈ (S : Subgroup G)) (hb : b ∈ (S : Subgroup G)) :
    (a * b)⁻¹ * (b * a) ∈ focalSubgroup p S := by
  exact Subgroup.subset_closure ⟨a * b, (S : Subgroup G).mul_mem ha hb, b * a,
    (S : Subgroup G).mul_mem hb ha, isConj_iff.mpr ⟨b, by group⟩, rfl⟩


/-- The quotient group `S / F` is a commutative group. -/
instance commGroupQuotient : CommGroup ((S : Subgroup G) ⧸ (focalSubgroup p S).subgroupOf (S : Subgroup G)) := by
  haveI h_normal : ((focalSubgroup p S).subgroupOf (S : Subgroup G)).Normal := focalSubgroup_normal_in_sylow p S
  have h_comm : ∀ x y : (S : Subgroup G) ⧸ (focalSubgroup p S).subgroupOf (S : Subgroup G), x * y = y * x := by
    intro x y
    refine QuotientGroup.induction_on x ?_
    intro a
    refine QuotientGroup.induction_on y ?_
    intro b
    apply QuotientGroup.eq.mpr
    exact Subgroup.mem_subgroupOf.2 (commutator_mem_focalSubgroup p S a.1 b.1 a.2 b.2)
  exact { mul_comm := h_comm }

/-- The canonical projection from `S` to the quotient by its focal subgroup. -/
def π : (S : Subgroup G) →* (S : Subgroup G) ⧸ (focalSubgroup p S).subgroupOf (S : Subgroup G) :=
  QuotientGroup.mk' ((focalSubgroup p S).subgroupOf (S : Subgroup G))

/-- The projection `π` sends elements of the focal subgroup to the identity. -/
lemma π_focal (f : G) (hf : f ∈ focalSubgroup p S) (hfS : f ∈ (S : Subgroup G)) :
    π p S ⟨f, hfS⟩ = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.2 hf)

/-- Equality in the quotient: two elements of `S` that differ by an element of the focal subgroup have equal images under `π`. -/
lemma π_eq_of_diff_mem_focal (a b : G) (ha : a ∈ (S : Subgroup G)) (hb : b ∈ (S : Subgroup G))
    (h : a⁻¹ * b ∈ focalSubgroup p S) : π p S ⟨a, ha⟩ = π p S ⟨b, hb⟩ :=
  QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 h)


section Transfer

/-- The transfer homomorphism `G →* (S : Subgroup G) ⧸ (focalSubgroup p S).subgroupOf (S : Subgroup G)`. -/
noncomputable def transferHom [Finite G] [Fact p.Prime] :
    G →* (S : Subgroup G) ⧸ (focalSubgroup p S).subgroupOf (S : Subgroup G) :=
  MonoidHom.transfer (π p S)

/-- The derived subgroup of `G` is contained in the kernel of `transferHom`. -/
theorem derivedSubgroup_le_ker_transferHom [Finite G] [Fact p.Prime] :
    derivedSubgroup G ≤ (transferHom p S).ker :=
  Abelianization.commutator_subset_ker (transferHom p S)

/-- In `S/F`, conjugate elements of `S` have the same class under `π`. -/
lemma π_conj_eq (a : G) (ha : a ∈ (S : Subgroup G)) (g : G)
    (hg : g⁻¹ * a * g ∈ (S : Subgroup G)) :
    π p S ⟨g⁻¹ * a * g, hg⟩ = π p S ⟨a, ha⟩ := by
  apply π_eq_of_diff_mem_focal p S (g⁻¹ * a * g) a hg ha
  exact Subgroup.subset_closure ⟨g⁻¹ * a * g, hg, a, ha,
    isConj_iff.mpr ⟨g, by group⟩, rfl⟩

/-- The transfer of an element `s ∈ S` equals `π (s ^ index)`. -/
theorem transferHom_eq_focalQuotientProj_pow_index [Finite G] [Fact p.Prime]
    (s : G) (hs : s ∈ (S : Subgroup G)) :
    transferHom p S s = π p S ⟨s ^ (S : Subgroup G).index, (S : Subgroup G).pow_mem hs _⟩ := by
  classical
  let Q := G ⧸ (S : Subgroup G)
  haveI : Fintype Q := Subgroup.fintypeQuotientOfFiniteIndex
  haveI : MulAction.QuotientAction G (S : Subgroup G) := MulAction.left_quotientAction (H := (S : Subgroup G))
  let orbitQ := Quotient (MulAction.orbitRel (Subgroup.zpowers s) Q)
  haveI : Fintype orbitQ := Quotient.fintype _
  rw [transferHom, MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  -- Express each factor as π (s ^ m)
  rw [Finset.prod_congr rfl (fun q hq => by
    exact π_conj_eq p S (s ^ Function.minimalPeriod (s • ·) (Quotient.out q))
      ((S : Subgroup G).pow_mem hs _) (Quotient.out (Quotient.out q))
      (QuotientGroup.out_conj_pow_minimalPeriod_mem (H := (S : Subgroup G)) s (Quotient.out q)))]
  -- A lemma that π sends a power to a power
  have π_pow (n : ℕ) : π p S ⟨s ^ n, (S : Subgroup G).pow_mem hs n⟩ = (π p S ⟨s, hs⟩) ^ n := by
    simpa using map_pow (π p S) (⟨s, hs⟩ : (S : Subgroup G)) n
  simp_rw [π_pow]
  -- product of powers in a commutative group
  rw [Finset.prod_pow_eq_pow_sum]
  -- sum of minimal periods equals index
  have hsum : ∑ q : orbitQ, Function.minimalPeriod (s • ·) (Quotient.out q) =
      (S : Subgroup G).index := by
    simpa [orbitQ, Q] using (Subgroup.index_eq_sum_minimalPeriod (H := (S : Subgroup G)) s).symm
  rw [hsum]

/-- If an element `s` of a Sylow `p`-subgroup `S` satisfies `s ^ index ∈ F`, then `s` itself lies in `F`. -/
lemma mem_focalSubgroup_of_pow_index_mem [Finite G] [Fact p.Prime] (s : G) (hs : s ∈ (S : Subgroup G))
    (hpow : s ^ (S : Subgroup G).index ∈ focalSubgroup p S) : s ∈ focalSubgroup p S := by
  have hS : IsPGroup p (S : Subgroup G) := S.isPGroup'
  have hn : ¬ p ∣ (S : Subgroup G).index := Sylow.not_dvd_index S
  -- The quotient `Q = S / F` is a p‑group.
  let Q := (S : Subgroup G) ⧸ (focalSubgroup p S).subgroupOf (S : Subgroup G)
  have hQ : IsPGroup p Q := hS.to_quotient _
  -- The map `x ↦ x ^ index` is an automorphism of `Q`.
  let h_pow_equiv := hQ.powEquiv' hn
  -- Compute `π (s ^ index)` in two ways.
  have hπ_pow_eq : π p S ⟨s ^ (S : Subgroup G).index, (S : Subgroup G).pow_mem hs _⟩ =
      (π p S ⟨s, hs⟩) ^ (S : Subgroup G).index := by
    simpa using map_pow (π p S) ⟨s, hs⟩ (S : Subgroup G).index
  have hπ_pow_one : π p S ⟨s ^ (S : Subgroup G).index, (S : Subgroup G).pow_mem hs _⟩ = 1 :=
    π_focal p S (s ^ (S : Subgroup G).index) hpow ((S : Subgroup G).pow_mem hs _)
  rw [hπ_pow_eq] at hπ_pow_one
  -- Hence `(π s) ^ index = 1`.
  have h_πs_pow : (π p S ⟨s, hs⟩) ^ (S : Subgroup G).index = 1 := hπ_pow_one
  -- Because `powEquiv` is injective, `π s` must be 1.
  have h_πs_one : π p S ⟨s, hs⟩ = 1 := by
    have h_eq : h_pow_equiv (π p S ⟨s, hs⟩) = h_pow_equiv (1 : Q) := by
      dsimp [h_pow_equiv]
      rw [h_πs_pow]
      simp
    exact (h_pow_equiv.apply_eq_iff_eq (x := π p S ⟨s, hs⟩) (y := 1)).mp h_eq
  -- `π s = 1` means `s` belongs to the kernel of the projection, i.e. to `F`.
  haveI := focalSubgroup_normal_in_sylow p S
  have h_mem : (⟨s, hs⟩ : (S : Subgroup G)) ∈ (focalSubgroup p S).subgroupOf (S : Subgroup G) :=
    (QuotientGroup.eq_one_iff (N := (focalSubgroup p S).subgroupOf (S : Subgroup G)) (x := (⟨s, hs⟩ : (S : Subgroup G)))).mp h_πs_one
  rw [Subgroup.mem_subgroupOf] at h_mem
  exact h_mem

end Transfer

/-
**Kind**: Theorem
**Note**: Theorem 1.17
**Stmt**:
Let $G$ be a finite group.
Let $p$ be a prime.
Let $S$ be a Sylow $p$-subgroup of $G$.
Then
\[ S \cap G' = \langle x^{-1} y | x, y \in S and x is conjugate to y in G \rangle. \]
-/

/-- If `x` and `y` are conjugate, then `x⁻¹ * y` lies in the derived subgroup of `G`. -/
public lemma isConj_diff_mem_derivedSubgroup {x y : G} (hxy : IsConj x y) :
    x⁻¹ * y ∈ derivedSubgroup G := by
  have h_abel : Abelianization.of (x⁻¹ * y) = 1 := by
    rcases hxy with ⟨c, hc⟩
    have hc' := congr_arg Abelianization.of hc
    simp [map_mul] at hc'
    -- hc' : of c * of x * (of c)⁻¹ = of y
    -- Since Abelianization G is abelian, we can rearrange
    have hxy' : Abelianization.of x = Abelianization.of y := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hc'
    calc
      Abelianization.of (x⁻¹ * y) = (Abelianization.of x)⁻¹ * Abelianization.of y := by simp
      _ = (Abelianization.of x)⁻¹ * Abelianization.of x := by rw [hxy']
      _ = 1 := by simp
  have h_mem : x⁻¹ * y ∈ (Abelianization.of : G →* Abelianization G).ker := by
    rw [MonoidHom.mem_ker]
    exact h_abel
  rw [Abelianization.ker_of] at h_mem
  exact h_mem

public theorem sylow_inf_derivedSubgroup_eq_focalSubgroup {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (S : Sylow p G) :
    ((S : Subgroup G) ⊓ derivedSubgroup G) =
      Subgroup.closure {z : G | ∃ x : G, x ∈ (S : Subgroup G) ∧ ∃ y : G, y ∈ (S : Subgroup G) ∧
        IsConj x y ∧ z = x⁻¹ * y} := by
  set F := focalSubgroup p S
  have hF_le_S : F ≤ (S : Subgroup G) := focalSubgroup_le_sylow p S
  have hF_le_G' : F ≤ derivedSubgroup G := by
    apply (Subgroup.closure_le (K := derivedSubgroup G)).2
    intro z hz
    rcases hz with ⟨x, hx, y, hy, hxy, rfl⟩
    exact isConj_diff_mem_derivedSubgroup hxy
  have h_left : ((S : Subgroup G) ⊓ derivedSubgroup G) ≤ F := by
    intro s hs
    rcases hs with ⟨hsS, hsG'⟩
    have h_pi_eq_one : π p S ⟨s ^ (S : Subgroup G).index, (S : Subgroup G).pow_mem hsS _⟩ = 1 := by
      have hV : transferHom p S s = 1 := by
        exact (MonoidHom.mem_ker.mp (derivedSubgroup_le_ker_transferHom p S hsG'))
      rw [transferHom_eq_focalQuotientProj_pow_index p S s hsS] at hV
      exact hV
    have h_pow : s ^ (S : Subgroup G).index ∈ F := by
      haveI := focalSubgroup_normal_in_sylow p S
      have h_mem : (⟨s ^ (S : Subgroup G).index, (S : Subgroup G).pow_mem hsS _⟩ : (S : Subgroup G)) ∈
          (focalSubgroup p S).subgroupOf (S : Subgroup G) :=
        (QuotientGroup.eq_one_iff (N := (focalSubgroup p S).subgroupOf (S : Subgroup G)) (x := (⟨s ^ (S : Subgroup G).index, (S : Subgroup G).pow_mem hsS _⟩ : (S : Subgroup G)))).mp h_pi_eq_one
      exact Subgroup.mem_subgroupOf.mp h_mem
    exact mem_focalSubgroup_of_pow_index_mem p S s hsS h_pow
  have h_right : F ≤ ((S : Subgroup G) ⊓ derivedSubgroup G) :=
    le_inf hF_le_S hF_le_G'
  simpa [F, focalSubgroup] using le_antisymm h_left h_right
