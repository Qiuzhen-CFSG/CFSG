module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.OmegaGeometry.Covered
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.OmegaGeometry.AlignFactors
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.OmegaGeometry.KernelAction.Realization

/-!
# The centralizing kernel and involution actions of a covered Suzuki pair

The full omega image meets both marked factors nontrivially, so an element
centralizing it cannot swap the factors. A factor-preserving two-action has
an inner representative in T₀ by the action-realization theorem. Dividing
by that representative leaves the full ambient kernel C_{Tᵥ}(K₀), proving
C_{Tᵥ}(Ω₁(T₀)) = C_{T₀}(Ω₁(T₀)) C_{Tᵥ}(K₀).

For square-one actors fixing K, the representative can itself be chosen
square-one. It therefore belongs to the elementary group Ω₁(T₀) and
centralizes that group. The final corollary applies the kernel decomposition
to the actual lifted Borel and proves normalization of C_{Tᵥ}(Ω₁(T₀)).
The elementary-center and single-factor involution-lifting inputs remain
explicit; nontrivial Sz(8) covers and the ambient action kernel are retained.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927 / PDF p.944;
the earlier cover input is I.2.2(4), printed pp.409–411 / PDF pp.420–422.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
variable {G : Type*} [Group G] [Finite G] {T K : Subgroup G} {v : G}

omit [Finite G] in
private theorem omega_le_orbit : omega T K v ≤ orbit T K v :=
  (omegaOneAmbient_le (intersection T K v)).trans inf_le_right

/-- A pointwise fixer of the full paired omega cannot interchange its two factors. -/
theorem PairFactors.centralizing_omega_normalizes {d : Marking T K v} (c : PairFactors d)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hKG : K ≤ Gv v) (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (center K)]
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q)
    (ha : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter))
    (x : Tv T v) (hx : (x : G) ∈ centralizer (omega T K v : Set G)) :
    (x : G) ∈ normalizer (K : Set G) := by
  rcases c.permutation x with h | h
  · exact mem_normalizer_iff_map_conj_eq.mpr h.1
  · have hcard : 1 < Nat.card (omegaOneAmbient (SuzukiRootSubgroup d.parameter)) := by
      rw [suzukiRootSubgroup_omega_card d.parameter d.positive]
      exact one_lt_pow₀ (by decide) (by omega)
    have hne : omegaOneAmbient (SuzukiRootSubgroup d.parameter) ≠ ⊥ := by
      intro he
      rw [he, card_bot] at hcard
      omega
    obtain ⟨q, hq⟩ := ne_bot_iff_exists_ne_one.mp hne
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (center K) (c.firstEquiv.symm q)
    have hqk : c.firstEquiv (QuotientGroup.mk' (center K) k) = q := by
      rw [hk, c.firstEquiv.apply_symm_apply]
    have hkω : (k : G) ∈ omega T K v := by
      rw [c.omega_eq_preimage P hP hKG hK hlift ha]
      refine ⟨firstEmbedding T K v k, ?_, rfl⟩
      change d.quotientMap (firstEmbedding T K v k) ∈
        (omegaOneAmbient (SuzukiRootSubgroup d.parameter)).prod
          (omegaOneAmbient (SuzukiRootSubgroup d.parameter))
      rw [c.first_eq, hqk]
      exact ⟨q.property, one_mem _⟩
    have hfix : MulAut.conj (x : G) (k : G) = k := by
      rw [MulAut.conj_apply, ← hx k hkω, mul_inv_cancel_right]
    have hkm : (k : G) ∈ K.map (MulAut.conj (c.moving : G)).toMonoidHom := by
      rw [← h.1, ← hfix]
      exact mem_map_of_mem _ k.property
    obtain ⟨l, hl, hel⟩ := hkm
    have he : secondEmbedding T K v c.moving ⟨l, hl⟩ = firstEmbedding T K v k :=
      Subtype.ext hel
    have hqe := congrArg d.quotientMap he
    rw [c.second_eq, c.first_eq, hqk] at hqe
    exact (hq (Subtype.ext (congrArg Prod.fst hqe).symm)).elim

/-- The full centralizing kernel in Tᵥ is retained when realizing the action in T₀. -/
theorem PairFactors.centralizing_kernel_decomposition {d : Marking T K v} (c : PairFactors d)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hKG : K ≤ Gv v) (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (center K)]
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q)
    (ha : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter)) :
    Tv T v ⊓ centralizer (omega T K v : Set G) =
      (intersection T K v ⊓ centralizer (omega T K v : Set G)) ⊔
        (Tv T v ⊓ centralizer (orbit T K v : Set G)) := by
  apply le_antisymm
  · rintro x ⟨hxT, hxC⟩
    let u : Tv T v := ⟨x, hxT⟩
    have hn := c.centralizing_omega_normalizes P hP hKG hK hlift ha u hxC
    obtain ⟨a, haT, hact, _⟩ := c.normalizing_action_realization P hP hKG hK hlift ha u hn
    let aT : Tv T v := ⟨a, haT⟩
    have haAct : orbitAction T K v aT = MulAut.conj a := by
      apply MulEquiv.ext
      intro y
      apply Subtype.ext
      rfl
    have haC : (a : G) ∈ centralizer (omega T K v : Set G) := by
      intro y hy
      have he := congrArg (fun z : orbit T K v => (z : G))
        (DFunLike.congr_fun hact ⟨y, omega_le_orbit hy⟩)
      change x * y * x⁻¹ = (a : G) * y * (a : G)⁻¹ at he
      rw [← hxC y hy, mul_inv_cancel_right] at he
      exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
    have hz : ((aT⁻¹ * u : Tv T v) : G) ∈ centralizer (orbit T K v : Set G) := by
      have hh : aT⁻¹ * u ∈ (orbitAction T K v).ker := by
        change orbitAction T K v (aT⁻¹ * u) = 1
        rw [map_mul, map_inv, haAct, hact, inv_mul_cancel]
      rw [orbitAction_kernel] at hh
      exact hh
    have hh := ((intersection T K v ⊓ centralizer (omega T K v : Set G)) ⊔
        (Tv T v ⊓ centralizer (orbit T K v : Set G))).mul_mem
      (mem_sup_left (show (a : G) ∈ intersection T K v ⊓ centralizer (omega T K v : Set G) from
        ⟨⟨haT, a.property⟩, haC⟩))
      (mem_sup_right (show ((aT⁻¹ * u : Tv T v) : G) ∈
        Tv T v ⊓ centralizer (orbit T K v : Set G) from ⟨(aT⁻¹ * u).property, hz⟩))
    simpa only [coe_mul, coe_inv, aT, u, mul_inv_cancel_left] using hh
  · exact sup_le (inf_le_inf inf_le_left le_rfl)
      (inf_le_inf le_rfl (centralizer_le omega_le_orbit))

/-- Every square-one actor in Tᵥ which fixes K centralizes the actual covered omega. -/
theorem PairFactors.square_one_normalizer_centralizes_omega {d : Marking T K v} (c : PairFactors d)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hKG : K ≤ Gv v) (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (center K)]
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q)
    (ha : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter))
    (x : G) (hx : x ∈ Tv T v) (hx2 : x ^ 2 = 1) (hn : x ∈ normalizer (K : Set G)) :
    x ∈ centralizer (omega T K v : Set G) := by
  let := c.omega_elementary P hP hKG hK hlift ha
  obtain ⟨a, haT, hact, ha2⟩ :=
    c.normalizing_action_realization P hP hKG hK hlift ha ⟨x, hx⟩ hn
  have haω : (a : G) ∈ omega T K v :=
    (omegaOneAmbient_le_iff (intersection T K v) (omega T K v)).mp le_rfl
      (a : G) ⟨haT, a.property⟩
      (congrArg (fun z : orbit T K v => (z : G)) (ha2 hx2))
  have haC : (a : G) ∈ centralizer (omega T K v : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance haω
  intro y hy
  have he := congrArg (fun z : orbit T K v => (z : G))
    (DFunLike.congr_fun hact ⟨y, omega_le_orbit hy⟩)
  change x * y * x⁻¹ = (a : G) * y * (a : G)⁻¹ at he
  rw [← haC y hy, mul_inv_cancel_right] at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- Apply the kernel decomposition to the lifted Borel, with its ambient action intact. -/
theorem PairFactors.borel_normalizes_centralizer {d : Marking T K v} (c : PairFactors d)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hKG : K ≤ Gv v) (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (center K)]
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q)
    (ha : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter)) :
    d.borel ≤ normalizer
      ((Tv T v ⊓ centralizer (omega T K v : Set G) : Subgroup G) : Set G) := by
  let := c.orbit_center_elementary hKG hK
  rw [c.centralizing_kernel_decomposition P hP hKG hK hlift ha]
  have hk : d.borel ≤ normalizer
      ((Tv T v ⊓ centralizer (orbit T K v : Set G) : Subgroup G) : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    exact d.borel_le_orbit.trans (le_centralizer_iff.mp inf_le_right)
  exact (le_inf (d.borel_normalizes_intersection_centralizer P hP hKG
    (IsElementaryAbelian.isPGroup 2 _) ha) hk).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
