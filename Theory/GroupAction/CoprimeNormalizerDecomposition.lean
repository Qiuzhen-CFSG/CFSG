module

public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.NormalizingActor
public import Theory.GroupAction.NormalizingFixedPoints

/-!
# Restricting a coprime normalizer to the moving summand

For a coprime automorphism subgroup A of a finite abelian group E, the
normalizer preserves E = C_E(A) × [E,A]. Restriction is faithful on these
two factors together. The restriction of A to [E,A] is itself faithful,
and the normalizer restricts to its normalizer there. Consequently the
normalizer order divides the product of the fixed-factor automorphism
order and the moving-factor normalizer order.

This is the elementary coprime splitting argument used for the small
linear normalizers in Parrott, A Characterization of the Tits' Simple
Group (1972), printed p.673, properties (5) and (6).
-/

open scoped IsMulCommutative
open Subgroup

/-- Coprime splitting bounds a normalizer by its actions on the fixed and
moving factors; the actor subgroup retains its full order on the moving factor. -/
public theorem exists_restricted_coprime_normalizer
    {E : Type*} [Group E] [Finite E] [IsMulCommutative E]
    (A : Subgroup (MulAut E)) (hcop : Nat.Coprime (Nat.card A) (Nat.card E)) :
    ∃ D : Subgroup (MulAut (commutatorAction A E)),
      Nat.card D = Nat.card A ∧
      Nat.card (normalizer (A : Set (MulAut E))) ∣
        Nat.card (MulAut (FixedPoints.subgroup A E)) *
          Nat.card (normalizer (D : Set (MulAut (commutatorAction A E)))) := by
  let F := FixedPoints.subgroup A E
  let C := commutatorAction A E
  let N := normalizer (A : Set (MulAut E))
  let A₀ := A.subgroupOf N
  let : IsInvariant N E F := fixedPoints_isInvariant_of_normalizing_actor N A le_rfl
  let : IsInvariant N E C := commutatorAction_isInvariant_of_normalizing_actor N A le_rfl
  have hcompl : IsCompl F C :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm (fun a b : E => mul_comm a b)) hcop inferInstance
  have hext (a : MulAut E) (hF : ∀ x : F, a (x : E) = x)
      (hC : ∀ x : C, a (x : E) = x) : a = 1 := by
    apply MulEquiv.ext
    intro x
    obtain ⟨f, hf, c, hc, rfl⟩ := Subgroup.mem_sup.mp
      (show x ∈ F ⊔ C by rw [hcompl.sup_eq_top]; trivial)
    change a (f * c) = f * c
    rw [map_mul, hF ⟨f, hf⟩, hC ⟨c, hc⟩]
  let f := MulDistribMulAction.toMulAut N C
  let r := MulDistribMulAction.toMulAut N F
  let a := f.comp A₀.subtype
  have ha : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff a).mp
    apply eq_bot_iff.mpr
    intro x hx
    apply mem_bot.mpr
    apply Subtype.ext
    apply Subtype.ext
    apply hext
    · intro y
      exact y.property ⟨x.val.val, x.property⟩
    · intro y
      exact congrArg Subtype.val (MulEquiv.congr_fun (MonoidHom.mem_ker.mp hx) y)
  let D := A₀.map f
  have hD : Nat.card D = Nat.card A := by
    have heq : D = a.range := by
      rw [MonoidHom.range_comp, A₀.range_subtype]
    rw [heq, ← Nat.card_congr (MonoidHom.ofInjective ha).toEquiv]
    exact Nat.card_congr (subgroupOfEquivOfLe A.le_normalizer).toEquiv
  have hnorm : f.range ≤ normalizer (D : Set (MulAut C)) := by
    have hh := A₀.le_normalizer_map f
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map] using hh
  let g : N →* MulAut F × normalizer (D : Set (MulAut C)) :=
    r.prod (f.codRestrict _ (fun x => hnorm ⟨x, rfl⟩))
  have hg : Function.Injective g := by
    apply (MonoidHom.ker_eq_bot_iff g).mp
    apply eq_bot_iff.mpr
    intro x hx
    apply mem_bot.mpr
    apply Subtype.ext
    have hh := MonoidHom.mem_ker.mp hx
    apply hext
    · intro y
      exact congrArg Subtype.val (MulEquiv.congr_fun (congrArg Prod.fst hh) y)
    · intro y
      exact congrArg Subtype.val
        (MulEquiv.congr_fun (congrArg (fun z => (z.2 : MulAut C)) hh) y)
  refine ⟨D, hD, ?_⟩
  simpa only [Nat.card_prod] using Subgroup.card_dvd_of_injective g hg
