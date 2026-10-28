module

public import Theory.SpecificGroups.PSL2.SplitCentralizerElementaryCard
public import Theory.SpecificGroups.PSL2.SquareFieldInvolutionLayers

/-!
# Linear actors inside the actual intermediate centralizer

The squares of the full split torus belong to the inner component. Their
image is normal in every intermediate involution centralizer. The original
elementary two-core actor normalized by a Sylow fixes its squares, hence
the fourth powers in the full torus. A linear actor with this property
lies in the cyclic torus, so its elementary group has order at most two.
Source application: Aschbacher–Smith E.2.7, printed pp.218–219.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2
 theorem split_subcentralizer_linear_elementary_card_le_two
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (hp : 3 < p)
    (A : Subgroup (PGammaL2 F))
    (hsq : ∀ a : Fˣ, (SemidirectProduct.inl (pGammaL2FullSplitTorus F (a ^ 2)) : PGammaL2 F) ∈ A) :
    let C := centralizer ({(SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) : PGammaL2 F)} : Set (PGammaL2 F))
    let B := A.subgroupOf C
    ∀ T : Sylow 2 B, ∀ V : Subgroup B, V ≤ pCore 2 B →
      (T : Subgroup B) ≤ normalizer (V : Set B) → (∀ v ∈ V, v ^ 2 = 1) →
      (∀ v ∈ V, v.val.val.right = 1) → Nat.card V ≤ 2 := by
  intro C B T V hV hVN hpow hlinear
  let : Finite (PGL2 F) := Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective
  let : Finite (PGammaL2 F) := Finite.of_injective (fun x : PGammaL2 F => (x.left, x.right))
    (fun _ _ he => SemidirectProduct.ext (congrArg Prod.fst he) (congrArg Prod.snd he))
  let i : Fˣ →* PGammaL2 F := (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp (pGammaL2FullSplitTorus F)
  have hiC (a : Fˣ) : i a ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    change i a * i (-1) = i (-1) * i a
    rw [← map_mul, ← map_mul, mul_comm]
  let f : Fˣ →* B := {
    toFun a := ⟨⟨i (a ^ 2), hiC _⟩, hsq a⟩
    map_one' := by apply Subtype.ext; apply Subtype.ext; simp only [one_pow, map_one]; rfl
    map_mul' a b := by apply Subtype.ext; apply Subtype.ext; exact (congrArg i (mul_pow a b 2)).trans (map_mul i _ _) }
  let j : B →* PGammaL2 F := C.subtype.comp B.subtype
  have hj : Function.Injective j := C.subtype_injective.comp B.subtype_injective
  have hjf (a : Fˣ) : j (f a) = i (a ^ 2) := rfl
  let R := f.range
  let : IsCyclic R := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p, 2, Fact.out, ho, by decide, hF⟩
  let : R.Normal := ⟨by
    intro r hr g
    obtain ⟨a, rfl⟩ := hr
    have hpowU : Units.map g.val.val.right.toMonoidHom (a ^ 2) =
        (Units.map g.val.val.right.toMonoidHom a) ^ 2 := by
      apply Units.ext
      exact map_pow g.val.val.right (a : F) 2
    obtain ha | ha := split_involution_centralizer_torus_action hodd g.val.val
      (mem_centralizer_singleton_iff.mp g.val.property)
    · refine ⟨Units.map g.val.val.right.toMonoidHom a, ?_⟩
      apply hj
      simp only [map_mul, map_inv, hjf]
      have hh := (ha (a ^ 2)).symm
      change i (Units.map g.val.val.right.toMonoidHom (a ^ 2)) =
        j g * i (a ^ 2) * (j g)⁻¹ at hh
      rw [hpowU] at hh
      exact hh
    · refine ⟨(Units.map g.val.val.right.toMonoidHom a)⁻¹, ?_⟩
      apply hj
      simp only [map_mul, map_inv, hjf]
      have hh := (ha (a ^ 2)).symm
      rw [map_inv] at hh
      change (i (Units.map g.val.val.right.toMonoidHom (a ^ 2)))⁻¹ =
        j g * i (a ^ 2) * (j g)⁻¹ at hh
      rw [hpowU] at hh
      simpa only [inv_pow, map_inv] using hh⟩
  have hc := Theory.GroupTheory.elementary_core_commute_normal_abelian_squares T V R hV hVN hpow
  have hle : V.map j ≤ i.range := by
    rintro x ⟨v, hv, rfl⟩
    apply linear_centralizer_mem_split_torus_of_fourth_fixed hodd
      (by rw [hF]; nlinarith) v.val.val (hlinear v hv)
      (mem_centralizer_singleton_iff.mp v.val.property)
    intro a
    have hh := congrArg j (hc v hv (f a) ⟨a, rfl⟩).eq
    change Commute (j v) (i a ^ 4)
    change j v * i a ^ 4 = i a ^ 4 * j v
    simpa only [map_mul, map_pow, hjf, ← pow_mul] using hh
  let : IsCyclic i.range := isCyclic_of_surjective i.rangeRestrict i.rangeRestrict_surjective
  let : IsCyclic (V.map j) := Subgroup.isCyclic_of_le hle
  let : IsCyclic V := (V.equivMapOfInjective j hj).isCyclic.mpr inferInstance
  have hd : Nat.card V ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro v
    exact Subtype.ext (hpow v v.property)
  exact Nat.le_of_dvd (by decide : 0 < 2) hd
end Theory.PSL2
