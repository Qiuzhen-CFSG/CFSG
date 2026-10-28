module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Transvections
public import Theory.SpecificGroups.BinaryLinear.NestedRadicals
public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# Returning transvections in binary linear Sylow subgroups

A nonidentity element central in a binary linear Sylow subgroup is a
transvection. All nonidentity transvections form one conjugacy class.
The coordinate transvections I+E₀₁ and I+E₁₂ lie in the join of the radicals
of the line spanned by e₀ and the hyperplane ker(coord₂). Nested-radical
normalization makes this join a two-group. The two transvections do not
commute, as their products differ on e₂. Sylow conjugacy supplies such a
pair in every Sylow, in the class of the original central marker.

Source application: Aschbacher--Smith 1.1.5(3)(a), Theorem C(4), and the
component inspection in Proposition 2.2.2, printed pp.33, 501--503 and
519--520 (combined 1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
namespace BinaryLinear.MarkedStrongClosure
open OuterCyclic

private theorem exists_two_group_transvection_pair {n : ℕ} (hn : 3 ≤ n) :
    ∃ (P : Sylow 2 (LinearGroup n)) (a b : LinearGroup n),
      a ∈ P ∧ b ∈ P ∧ IsTransvection a ∧ IsTransvection b ∧ ¬Commute a b := by
  let : Finite (LinearGroup n) :=
    Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n))
      DFunLike.coe_injective
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let k : Fin n := ⟨2, by omega⟩
  have hij : i ≠ j := by intro he; have := congrArg Fin.val he; simp [i, j] at this
  have hik : i ≠ k := by intro he; have := congrArg Fin.val he; simp [i, k] at this
  have hjk : j ≠ k := by intro he; have := congrArg Fin.val he; simp [j, k] at this
  let W : Submodule (ZMod 2) (Space n) := Submodule.span (ZMod 2) {Pi.single i 1}
  let H : Submodule (ZMod 2) (Space n) := (LinearMap.proj k).ker
  have hWj : W ≤ (LinearMap.proj j).ker := by
    apply Submodule.span_le.mpr
    intro v hv
    obtain rfl := Set.mem_singleton_iff.mp hv
    simp [hij]
  have hWH : W ≤ H := by
    apply Submodule.span_le.mpr
    intro v hv
    obtain rfl := Set.mem_singleton_iff.mp hv
    simp [H, hik]
  have hwi : Pi.single i (1 : ZMod 2) ∈ W := Submodule.mem_span_singleton_self _
  have hwj : Pi.single j (1 : ZMod 2) ∈ H := by simp [H, hjk]
  let a : LinearGroup n := transvection (Pi.single i 1) (LinearMap.proj j) (hWj hwi)
  let b : LinearGroup n := transvection (Pi.single j 1) (LinearMap.proj k) hwj
  have haW : a ∈ radical W := transvection_mem hwi hWj
  have hbH : b ∈ radical H := transvection_mem hwj le_rfl
  have hnorm : radical H ≤ normalizer (radical W : Set (LinearGroup n)) :=
    (radical_le_smaller_parabolic hWH).trans (parabolic_le_normalizer W)
  have htwo : IsPGroup 2 (radical W ⊔ radical H : Subgroup (LinearGroup n)) :=
    (radical_two W).to_sup_of_normal_left' (radical_two H) hnorm
  obtain ⟨P, hP⟩ := htwo.exists_le_sylow
  have hsingle (s : Fin n) : (Pi.single s (1 : ZMod 2) : Space n) ≠ 0 := by
    intro he
    have hh := congrFun he s
    simp at hh
  have hproj (s : Fin n) : (LinearMap.proj s : Space n →ₗ[ZMod 2] ZMod 2) ≠ 0 := by
    intro he
    have hh := LinearMap.congr_fun he (Pi.single s 1)
    simp at hh
  refine ⟨P, a, b, hP (mem_sup_left haW), hP (mem_sup_right hbH),
    ⟨Pi.single i 1, LinearMap.proj j, hsingle i, hproj j, _, rfl⟩,
    ⟨Pi.single j 1, LinearMap.proj k, hsingle j, hproj k, _, rfl⟩, ?_⟩
  have ha (v : Space n) (s : Fin n) : a v s = v s + if s = i then v j else 0 := by
    change v s + v j * (Pi.single i (1 : ZMod 2) : Space n) s = _
    by_cases hs : s = i <;> simp [hs]
  have hb (v : Space n) (s : Fin n) : b v s = v s + if s = j then v k else 0 := by
    change v s + v k * (Pi.single j (1 : ZMod 2) : Space n) s = _
    by_cases hs : s = j <;> simp [hs]
  intro hc
  have he := congrArg (fun g : LinearGroup n => g (Pi.single k 1) i) hc.eq
  change a (b (Pi.single k 1)) i = b (a (Pi.single k 1)) i at he
  simp only [ha, hb] at he
  simp [hij, hik, hjk] at he

/-- Every Sylow in binary dimensions four and five contains noncommuting
conjugates of the actual two-central marker. -/
theorem sylow_noncommuting_conjugates {n : ℕ} (hn : n = 4 ∨ n = 5)
    (v : LinearGroup n) (hv : IsSylowCentralInvolution v)
    (R : Sylow 2 (LinearGroup n)) :
    ∃ a b : R, IsConj v (a : LinearGroup n) ∧
      IsConj v (b : LinearGroup n) ∧ ¬Commute a b := by
  let : Finite (LinearGroup n) :=
    Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n))
      DFunLike.coe_injective
  obtain ⟨ho, Pv, _, hc⟩ := hv
  have hv1 : v ≠ 1 := by intro he; simp [he] at ho
  have hcard : 2 ∣ Nat.card (Space n) := by
    change 2 ∣ Nat.card (Fin n → ZMod 2)
    rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, ZMod.card]
    exact dvd_pow_self 2 (by omega)
  have hdim : 1 < Module.finrank (ZMod 2) (Space n) := by
    simpa [Space] using (show 1 < n by omega)
  have hvt : IsTransvection v := isTransvection_of_central_sylow hcard hdim Pv hv1
    (fun x hx => mem_centralizer_singleton_iff.mp (hc hx))
  obtain ⟨P, x, y, hxP, hyP, hxt, hyt, hxy⟩ :=
    exists_two_group_transvection_pair (show 3 ≤ n by omega)
  obtain ⟨gx, hgx⟩ := transvections_conjugate hvt hxt
  obtain ⟨gy, hgy⟩ := transvections_conjugate hvt hyt
  have hvx : IsConj v x := isConj_iff.mpr ⟨gx, hgx⟩
  have hvy : IsConj v y := isConj_iff.mpr ⟨gy, hgy⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (LinearGroup n) P R
  have hm : (P : Subgroup (LinearGroup n)).map (MulAut.conj g).toMonoidHom =
      (R : Subgroup (LinearGroup n)) := congrArg Sylow.toSubgroup hg
  let a : R := ⟨MulAut.conj g x, by
    change MulAut.conj g x ∈ (R : Subgroup (LinearGroup n))
    rw [← hm]
    exact mem_map_of_mem _ hxP⟩
  let b : R := ⟨MulAut.conj g y, by
    change MulAut.conj g y ∈ (R : Subgroup (LinearGroup n))
    rw [← hm]
    exact mem_map_of_mem _ hyP⟩
  refine ⟨a, b, hvx.trans (isConj_iff.mpr ⟨g, rfl⟩),
    hvy.trans (isConj_iff.mpr ⟨g, rfl⟩), ?_⟩
  intro hab
  apply hxy
  apply (MulAut.conj g).injective
  have he := congrArg Subtype.val hab.eq
  exact ((MulAut.conj g).map_mul _ _).trans (he.trans ((MulAut.conj g).map_mul _ _).symm)

end BinaryLinear.MarkedStrongClosure
