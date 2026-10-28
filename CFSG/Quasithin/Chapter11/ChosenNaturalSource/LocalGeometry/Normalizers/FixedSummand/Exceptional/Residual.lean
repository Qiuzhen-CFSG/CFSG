module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Exceptional.Parameters
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.Representation.GoldschmidtONan.ExceptionalOrbit

/-!
# The order-seven residual in the exceptional point-radical action

The exceptional faithful action is transitive on the seven nonzero vectors
of Z₁. Its fixed space has exactly one nonzero vector, so the stabilizer has
index seven. Pulling back through the literal quotient map identifies this
stabilizer with Y intersect M. A subgroup of index seven together with
O^{7′}(Y) generates Y, since the latter has index prime to seven.

The last theorem applies this equality to the original seed normalizer.
It reduces the SL₃ contradiction to the action of O^{7′}(Y) on the literal
chief sections in field degree two. That action, the Sp₄ branch, and the
Cartan–TI construction remain with `qt-d-1222-natural-point-fixed-summand`;
this module does not assert that source 11.1.5 is complete.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
the final paragraph of 11.1.5, printed p.766.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.GoldschmidtONan
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
variable {G : Type*} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

private theorem primeResidual_sup_eq_top_of_prime_index
    {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (H : Subgroup A) (hi : H.index = p) : primeToResidual p A ⊔ H = ⊤ := by
  apply Subgroup.index_eq_one.mp
  have hd : (primeToResidual p A ⊔ H).index ∣ p :=
    (index_dvd_of_le (show H ≤ primeToResidual p A ⊔ H from le_sup_right)).trans (hi ▸ dvd_refl p)
  have hc : Nat.Coprime p (primeToResidual p A ⊔ H).index :=
    (primeToResidual_index_coprime p).of_dvd_right
      (index_dvd_of_le (show primeToResidual p A ≤ primeToResidual p A ⊔ H from le_sup_left))
  exact Nat.eq_one_of_dvd_coprimes hc hd (dvd_refl _)

variable {A W : Type*} [Group A] [Finite A] [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W]
    {ρ : Representation (ZMod 2) A W} {X : Subgroup A}

@[instance_reducible] private def nonzeroAction : MulAction A {v : W // v ≠ 0} where
  smul a v := ⟨ρ a v, fun he => v.property
    (Representation.GoldschmidtONan.action_injective (ρ := ρ) a (he.trans (map_zero _).symm))⟩
  one_smul v := Subtype.ext (by change ρ 1 v = v; simp)
  mul_smul a b v := Subtype.ext (by change ρ (a*b) v = ρ a (ρ b v); rw [map_mul]; rfl)

/-- In the exceptional case the fixed-space stabilizer has index seven.
This is computed for the given action, before returning to ambient G. -/
theorem exceptional_stabilizer_index
    (h : Input ρ X) (he : ExceptionalCase ρ X) :
    (subspaceStabilizer ρ (fixedSpace ρ X)).index = 7 := by
  classical
  let F := fixedSpace ρ X
  let : Nontrivial F := Submodule.nontrivial_iff_ne_bot.mpr h.fixed_nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  have hvW : (v : W) ≠ 0 := fun h => hv (Subtype.ext h)
  have huniq (w : F) (hw : w ≠ 0) : w = v := by
    obtain ⟨r, hr⟩ := exists_smul_eq_of_finrank_eq_one he.1 hv w
    change r • v = w at hr
    rcases (show ∀ t : ZMod 2, t = 0 ∨ t = 1 from by decide) r with rfl | rfl
    · rw [zero_smul] at hr
      exact (hw hr.symm).elim
    · rw [one_smul] at hr
      exact hr.symm
  let := nonzeroAction (ρ := ρ)
  let : MulAction.IsPretransitive A {v : W // v ≠ 0} := ⟨by
    intro x y
    obtain ⟨a, ha⟩ := h.nonzeroTransitive_of_exceptional he x.val x.property y.val y.property
    exact ⟨a, Subtype.ext ha⟩⟩
  let v' : {w : W // w ≠ 0} := ⟨v, hvW⟩
  have hstab : subspaceStabilizer ρ F = MulAction.stabilizer A v' := by
    ext a
    constructor
    · intro ha
      have hmem : ρ a v ∈ F := (ha v).mpr v.property
      have hne : (⟨ρ a v, hmem⟩ : F) ≠ 0 := by
        intro hz
        exact hvW (Representation.GoldschmidtONan.action_injective (ρ := ρ) a
          ((congrArg Subtype.val hz).trans (map_zero _).symm))
      change a • v' = v'
      apply Subtype.ext
      change ρ a (v : W) = (v : W)
      exact congrArg Subtype.val (huniq ⟨ρ a v, hmem⟩ hne)
    · intro ha
      have hav : ρ a v = v := congrArg Subtype.val ha
      rw [mem_subspaceStabilizer_iff_map]
      apply le_antisymm
      · rintro _ ⟨w, hw, rfl⟩
        by_cases hz : w = 0
        · simp only [hz, map_zero, Submodule.zero_mem]
        · have hwv : w = (v : W) := congrArg Subtype.val
            (huniq ⟨w, hw⟩ (fun he => hz (congrArg Subtype.val he)))
          rw [hwv, hav]
          exact v.property
      · intro w hw
        by_cases hz : w = 0
        · simp only [hz, Submodule.zero_mem]
        · have hwv : w = (v : W) := congrArg Subtype.val
            (huniq ⟨w, hw⟩ (fun he => hz (congrArg Subtype.val he)))
          rw [hwv]
          exact ⟨v, v.property, hav⟩
  rw [hstab, MulAction.index_stabilizer_of_transitive A v']
  let := Fintype.ofFinite W
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    ← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod, he.2.1]
  decide

/-- The literal source stabilizer Y intersect M has index seven in Y. -/
theorem chosen_exceptional_intersection_index
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) (X : Subgroup G)
    (h : Input (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X)) :
    ((normalizer (L : Set G)).subgroupOf (normalizer (f.Ri 0 : Set G))).index = 7 := by
  have hne : radicalFixedCenter (f.Ri 0) L ≠ ⊥ := by
    intro hz
    have hn := h.fixed_nontrivial
    rw [hfixed] at hn
    apply hn
    ext z
    change z.toMul.val ∈ radicalFixedCenter (f.Ri 0) L ↔ z = 0
    rw [hz, mem_bot]
    exact ⟨fun he => Additive.toMul.injective (Subtype.ext he),
      fun he => congrArg (fun w : Additive (radicalOmegaCenter (f.Ri 0)) => w.toMul.val) he⟩
  have hstab := congrArg (fun U : Subgroup G => U.subgroupOf (normalizer (f.Ri 0 : Set G)))
    (chosen_fixed_stabilizer D S f hne)
  simp only [inf_subgroupOf_left] at hstab
  have hi := exceptional_stabilizer_index h he
  rw [hfixed] at hi
  rw [← (subspaceStabilizer (representation (f.Ri 0)) (fixedSubspace (f.Ri 0) L)).index_comap_of_surjective
    (f := projection (f.Ri 0)) (QuotientGroup.mk'_surjective (kernel (f.Ri 0))),
    stabilizer_comap, hstab] at hi
  exact hi

/-- The source O^{7′}(Y) generation step on the original relative subgroup.
No global normality or replacement quotient is used. -/
theorem chosen_exceptional_sevenResidual_sup
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) (X : Subgroup G)
    (h : Input (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X)) :
    (primeToResidual 7 (normalizer (f.Ri 0 : Set G))).map
        (normalizer (f.Ri 0 : Set G)).subtype ⊔
      (normalizer (f.Ri 0 : Set G) ⊓ normalizer (L : Set G)) = normalizer (f.Ri 0 : Set G) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hh := primeResidual_sup_eq_top_of_prime_index _
    (chosen_exceptional_intersection_index D S f X h hfixed he)
  have hm := congrArg (map (normalizer (f.Ri 0 : Set G)).subtype) hh
  simpa only [Subgroup.map_sup, subgroupOf_map_subtype, inf_comm,
    ← MonoidHom.range_eq_map, range_subtype] using hm

/-- Application of the generation step to the actual SL3 seed normalizer.
The remaining premise is precisely the chief-section action of O^{7′}(Y). -/
theorem chosen_exceptional_normalizes_seed_of_sevenResidual
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) (X : Subgroup G)
    (hspan : V = Source.conjugateSpan (normalizer (L : Set G)) V)
    (h : Input (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hseven : (primeToResidual 7 (normalizer (f.Ri 0 : Set G))).map
      (normalizer (f.Ri 0 : Set G)).subtype ≤ normalizer (V : Set G)) :
    normalizer (f.Ri 0 : Set G) ≤ normalizer (V : Set G) := by
  rw [← chosen_exceptional_sevenResidual_sup D S f X h hfixed he]
  apply sup_le hseven
  apply inf_le_right.trans
  rw [hspan]
  exact le_normalizer_componentOrbit V (normalizer (L : Set G))


/-- The SL3 exceptional branch is reduced to its literal chief-section
action in field degree two. The numerical reduction and O^{7′} generation
are discharged here, before applying maximal-local uniqueness to V. -/
theorem chosen_exceptional_escape_of_sevenResidual
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) (X : Subgroup G)
    (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))
    (hspan : V = Source.conjugateSpan (normalizer (L : Set G)) V)
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (h : Input (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hseven : S.field.degree = 2 →
      (primeToResidual 7 (normalizer (f.Ri 0 : Set G))).map
        (normalizer (f.Ri 0 : Set G)).subtype ≤ normalizer (V : Set G)) : False := by
  have hn := (chosen_exceptional_parameters D S f X hcenter hfixed he).1
  exact hescape ((chosen_exceptional_normalizes_seed_of_sevenResidual D S f X
    hspan h hfixed he (hseven hn)).trans (chosen_seed_normalizer_le D S))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
