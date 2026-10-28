module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite characteristically-simple groups

A nontrivial finite group with no proper nontrivial characteristic subgroups is
isomorphic to a positive finite direct power of a simple subgroup.

Choose a minimal nontrivial normal subgroup `N`. The join of its automorphic
images is characteristic, so it is the whole group. Distinct images commute
with `N`; consequently any normal subgroup of `N` is normal in the whole group,
and minimality makes `N` simple. Choose a maximal normal subgroup isomorphic to
a positive power of `N`. An automorphic image not contained in that subgroup
has trivial intersection with it. Multiplication gives an explicit equivalence
from their external direct product onto their join, contradicting maximality.
Thus this power is the whole group. Disjointness is required from the entire
previous product, not merely from its individual factors.

This is the finite characteristically-simple structure theorem used in
Aschbacher--Smith, *The Classification of Quasithin Groups*, E.1.10(5), printed
p.211, citing Aschbacher (1986), 8.2. The chief-factor reduction and composition
factor witness belong to the importing parent module.
-/

namespace CharacteristicallySimple
open Subgroup
universe u
variable {H : Type u} [Group H]

private theorem automorphic_span_eq_top
    (hchar : ∀ C : Subgroup H, C.Characteristic → C = ⊥ ∨ C = ⊤)
    (N : Subgroup H) (hN : N ≠ ⊥) :
    (⨆ φ : H ≃* H, N.map φ.toMonoidHom) = ⊤ := by
  let C : Subgroup H := ⨆ φ : H ≃* H, N.map φ.toMonoidHom
  have hC : C.Characteristic := by
    apply characteristic_iff_map_le.mpr
    intro ψ
    dsimp [C]
    rw [map_iSup]
    refine iSup_le fun φ => ?_
    rw [map_map]
    exact le_iSup (fun φ : H ≃* H => N.map φ.toMonoidHom) (φ.trans ψ)
  obtain he | he := hchar C hC
  · exfalso
    apply hN
    apply le_bot_iff.mp
    calc
      N = N.map (MulEquiv.refl H).toMonoidHom := by simp
      _ ≤ C := le_iSup (fun φ : H ≃* H => N.map φ.toMonoidHom) (MulEquiv.refl H)
      _ = ⊥ := he
  · exact he

/-- Pull back the intersection to the chosen minimal normal subgroup. -/
private theorem image_disjoint_or_le (N : Subgroup H)
    (hmin : ∀ K : Subgroup H, K.Normal → K ≤ N → K = ⊥ ∨ K = N)
    [N.Normal] (M : Subgroup H) [M.Normal] (φ : H ≃* H) :
    Disjoint (N.map φ.toMonoidHom) M ∨ N.map φ.toMonoidHom ≤ M := by
  obtain he | he := hmin (N ⊓ M.comap φ.toMonoidHom) inferInstance inf_le_left
  · left
    apply Subgroup.disjoint_def.mpr
    rintro x ⟨y, hy, rfl⟩ hx
    have hy1 : y = 1 := by
      have hyK : y ∈ N ⊓ M.comap φ.toMonoidHom := ⟨hy, hx⟩
      simpa only [he, mem_bot] using hyK
    simp [hy1]
  · right
    rintro x ⟨y, hy, rfl⟩
    have : y ∈ N ⊓ M.comap φ.toMonoidHom := he.symm ▸ hy
    exact this.2

private theorem minimal_normal_isSimple [Finite H]
    (hchar : ∀ C : Subgroup H, C.Characteristic → C = ⊥ ∨ C = ⊤)
    (N : Subgroup H) [N.Normal] (hN : N ≠ ⊥)
    (hmin : ∀ K : Subgroup H, K.Normal → K ≤ N → K = ⊥ ∨ K = N) :
    IsSimpleGroup N := by
  let : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hN
  constructor
  intro C hC
  let := hC
  let D := C.map N.subtype
  have hnormalizer : (⨆ φ : H ≃* H, N.map φ.toMonoidHom) ≤ normalizer D := by
    refine iSup_le fun φ => ?_
    obtain hd | hl := image_disjoint_or_le N hmin N φ
    · apply le_normalizer_iff.mpr
      intro a ha c hc
      have hcN : c ∈ N := (map_subtype_le C) hc
      have hnφ : (N.map φ.toMonoidHom).Normal :=
        Subgroup.Normal.map inferInstance _ φ.surjective
      have hcomm := commute_of_normal_of_disjoint _ _ hnφ inferInstance hd a c ha hcN
      simpa only [hcomm.eq, mul_inv_cancel_right] using hc
    · have he : N.map φ.toMonoidHom = N :=
        Subgroup.eq_of_le_of_card_ge hl
          (Nat.card_congr (N.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv).le
      rw [he]
      have hle := le_normalizer_map (H := C) N.subtype
      simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] using hle
  rw [automorphic_span_eq_top hchar N hN] at hnormalizer
  have hD : D.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp hnormalizer)
  obtain he | he := hmin D hD (map_subtype_le C)
  · left
    exact (map_eq_bot_iff_of_injective C N.subtype_injective).mp he
  · right
    apply Subgroup.map_injective N.subtype_injective
    simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using he

/-- Multiplication identifies disjoint normal factors with their join. -/
private noncomputable def prodSupEquiv (M A : Subgroup H)
    [M.Normal] [A.Normal] (hd : Disjoint M A) : M × A ≃* (M ⊔ A : Subgroup H) := by
  let f : M × A →* (M ⊔ A : Subgroup H) :=
    { toFun := fun x => ⟨(x.1 : H) * x.2, mul_mem_sup x.1.property x.2.property⟩
      map_one' := by apply Subtype.ext; exact one_mul 1
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact (commute_of_normal_of_disjoint M A inferInstance inferInstance hd
          y.1 x.2 y.1.property x.2.property).mul_mul_mul_comm x.1 y.2 }
  apply MulEquiv.ofBijective f
  constructor
  · intro x y hxy
    exact mul_injective_of_disjoint hd (congrArg Subtype.val hxy)
  · intro x
    obtain ⟨m, hm, a, ha, hma⟩ := mem_sup_of_normal_right.mp x.property
    exact ⟨(⟨m, hm⟩, ⟨a, ha⟩), Subtype.ext hma⟩

private def powerSuccEquiv (N : Subgroup H) (n : ℕ) :
    (Fin (n + 1) → N) ≃* (Fin n → N) × N where
  __ := Fin.succFunEquiv N n
  map_mul' _ _ := rfl

/-- A nontrivial finite characteristically-simple group is isomorphic to a
positive finite direct power of one of its simple subgroups. -/
public theorem exists_simple_subgroup_power [Finite H] [Nontrivial H]
    (hchar : ∀ C : Subgroup H, C.Characteristic → C = ⊥ ∨ C = ⊤) :
    ∃ S : Subgroup H, IsSimpleGroup S ∧
      ∃ n : ℕ, 0 < n ∧ Nonempty (H ≃* (Fin n → S)) := by
  obtain ⟨N, hN, hminimal⟩ := exists_minimal_of_wellFoundedLT
    (fun N : Subgroup H => N.Normal ∧ N ≠ ⊥) ⟨⊤, inferInstance, top_ne_bot⟩
  let : N.Normal := hN.1
  have hmin (K : Subgroup H) (hK : K.Normal) (hKN : K ≤ N) : K = ⊥ ∨ K = N := by
    by_cases hbot : K = ⊥
    · exact Or.inl hbot
    · exact Or.inr (le_antisymm hKN (hminimal ⟨hK, hbot⟩ hKN))
  have hsimple := minimal_normal_isSimple hchar N hN.2 hmin
  obtain ⟨M, hM, hmaximal⟩ := exists_maximal_of_wellFoundedGT
    (fun M : Subgroup H => M.Normal ∧
      ∃ n : ℕ, 0 < n ∧ Nonempty (M ≃* (Fin n → N)))
    ⟨N, inferInstance, 1, Nat.zero_lt_succ 0,
      ⟨(MulEquiv.piUnique (fun _ : Fin 1 => N)).symm⟩⟩
  let : M.Normal := hM.1
  have hMtop : M = ⊤ := by
    have hspan : (⨆ φ : H ≃* H, N.map φ.toMonoidHom) ≤ M := by
      refine iSup_le fun φ => ?_
      obtain hd | hl := image_disjoint_or_le N hmin M φ
      · let A := N.map φ.toMonoidHom
        let : A.Normal := Subgroup.Normal.map inferInstance _ φ.surjective
        obtain ⟨n, _, ⟨e⟩⟩ := hM.2
        let eA : A ≃* N := (N.equivMapOfInjective φ.toMonoidHom φ.injective).symm
        let eprod : (M ⊔ A : Subgroup H) ≃* (Fin (n + 1) → N) :=
          ((prodSupEquiv M A hd.symm).symm.trans (e.prodCongr eA)).trans
            (powerSuccEquiv N n).symm
        have hle : M ⊔ A ≤ M := hmaximal
          ⟨inferInstance, n + 1, Nat.zero_lt_succ n, ⟨eprod⟩⟩ le_sup_left
        exact le_sup_right.trans hle
      · exact hl
    rw [automorphic_span_eq_top hchar N hN.2] at hspan
    exact top_le_iff.mp hspan
  obtain ⟨n, hn, ⟨e⟩⟩ := hM.2
  exact ⟨N, hsimple, n, hn,
    ⟨((MulEquiv.subgroupCongr hMtop).trans Subgroup.topEquiv).symm.trans e⟩⟩

end CharacteristicallySimple
