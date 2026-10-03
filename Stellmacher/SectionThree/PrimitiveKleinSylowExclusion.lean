module

public import Stellmacher.SectionThree.SolvablePrimitiveTwoLocal
public import Theory.GroupTheory.IrreducibleKleinComplementExclusion

/-!
# A core-free solvable local group cannot have a Klein-four Sylow subgroup

Let a finite solvable group have trivial two-core and a unique maximal
subgroup containing its specified Sylow two-subgroup. That Sylow cannot be
elementary abelian of order four. These are the native group hypotheses,
without an assumed representation or primitive quotient. This exclusion is
used in the terminal core quotient of Stellmacher (9.1), Journal of Algebra
190 (1997), p.48, via the primitive structure theorem (3.3).

The solvable primitive theorem places the normal core of the maximal subgroup
inside an odd-prime residual. It therefore intersects the specified Sylow
trivially, preserving its order and elementary structure in the normal-core
quotient. The core-free quotient theorem supplies a normal irreducible
complement. The mapped Sylow is core-free because it lies in the core-free
image of the maximal subgroup. The independent Klein-complement exclusion
now applies: every nonidentity Sylow actor would be a fixed-point-free
involution on the complement, so all three would act by inversion, contrary
to faithfulness. Every quotient and image uses the actual supplied subgroups.
-/

namespace Stellmacher.SectionThree
open scoped IsMulCommutative
universe u

private theorem primitive_quotient_data
    {X : Type u} [Group X] [Finite X]
    (hsolv : Group.IsSolvable X) (hcore : pCore 2 X = ⊥)
    (P : Sylow 2 X) (hP : IsElementaryAbelian 2 P) (hcard : Nat.card P = 4)
    (M : Subgroup X) (hM : IsCoatom M) (hPM : (P : Subgroup X) ≤ M)
    (huniq : ∀ L : Subgroup X, IsCoatom L → (P : Subgroup X) ≤ L → L = M) :
    let S := (P : Subgroup X).map (QuotientGroup.mk' M.normalCore)
    IsElementaryAbelian 2 S ∧ Nat.card S = 4 ∧ S.normalCore = ⊥ ∧
      ∃ K : Subgroup (X ⧸ M.normalCore), K.Normal ∧ K ⊔ S = ⊤ ∧
        (∀ A : Subgroup (X ⧸ M.normalCore), A ≤ K →
          (∀ s : S, ∀ a : X ⧸ M.normalCore, a ∈ A →
            (s : X ⧸ M.normalCore) * a * (s : X ⧸ M.normalCore)⁻¹ ∈ A) →
          A = ⊥ ∨ A = K) := by
  classical
  let := hP
  let N := M.normalCore
  let q : X →* X ⧸ N := QuotientGroup.mk' N
  let S := (P : Subgroup X).map q
  let B := M.map q
  have hqsur : Function.Surjective q := QuotientGroup.mk'_surjective N
  obtain ⟨p, hp, hpodd, hRp, hN, _⟩ :=
    solvable_primitive_two_local (P : Subgroup X) M P rfl hM hPM huniq hcore hsolv
  let : Fact p.Prime := ⟨hp⟩
  have hpne : 2 ≠ p := by
    intro he
    rw [← he] at hpodd
    exact (by decide : ¬ Odd (2 : ℕ)) hpodd
  have hNp : IsPGroup p N := hRp.to_le (by
    change M.normalCore ≤ twoResidualAmbient (⊤ : Subgroup X)
    rw [hN]
    exact Subgroup.map_subtype_le _)
  have hdis : Disjoint (P : Subgroup X) N :=
    IsPGroup.disjoint_of_ne 2 p hpne _ _ P.isPGroup' hNp
  let pq : P →* X ⧸ N := q.comp (P : Subgroup X).subtype
  have hpq : Function.Injective pq := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro x hx
    apply Subtype.ext
    apply hdis.le_bot
    exact ⟨x.property, (QuotientGroup.eq_one_iff (N := N) (x : X)).mp hx⟩
  have hSq : S = pq.range := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hScard : Nat.card S = 4 := by
    rw [hSq, ← Nat.card_congr (MonoidHom.ofInjective hpq).toEquiv]
    exact hcard
  have hSelem : IsElementaryAbelian 2 S := IsElementaryAbelian.map q
  have hcomapB : B.comap q = M := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr M.normalCore_le]
  have hBcore : B.normalCore = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨y, rfl⟩ := hqsur x
    have hnormal : (B.normalCore.comap q).Normal := inferInstance
    have hleM : B.normalCore.comap q ≤ M :=
      (Subgroup.comap_mono B.normalCore_le).trans hcomapB.le
    have hleN : B.normalCore.comap q ≤ N :=
      @Subgroup.normal_le_normalCore X _ M _ hnormal |>.mpr hleM
    exact (QuotientGroup.eq_one_iff (N := N) y).mpr (hleN hx)
  have hSB : S ≤ B := Subgroup.map_mono hPM
  have hScore : S.normalCore = ⊥ := by
    apply bot_unique
    have hle : S.normalCore ≤ B.normalCore :=
      Subgroup.normal_le_normalCore.mpr (S.normalCore_le.trans hSB)
    exact hle.trans hBcore.le
  obtain ⟨r, K, hr, hrodd, hKn, hKe, hKB, hKS, hirred⟩ :=
    quotientCoreFree_data (P : Subgroup X) M P rfl hM hPM huniq hsolv
  have hrne : r ≠ 2 := by
    intro he
    rw [he] at hrodd
    exact (by decide : ¬ Odd (2 : ℕ)) hrodd
  let : Fact r.Prime := ⟨hr⟩
  let := hKe
  have hKp : IsPGroup r K := IsElementaryAbelian.isPGroup r K
  have hres : twoResidualAmbient (⊤ : Subgroup (X ⧸ N)) = K :=
    twoResidualAmbient_top_eq_of_normal_complement_sylow_two hr hrne K S
      (P.mapSurjective hqsur) rfl hKn hKp hKS
  refine ⟨hSelem, hScard, hScore, K, hKn, hKS, ?_⟩
  obtain ⟨hNnormal, hirred⟩ := hirred
  change IsIrreducibleSection S ⊥ (twoResidualAmbient (⊤ : Subgroup (X ⧸ N))) at hirred
  rw [hres] at hirred
  intro A hA hstable
  exact hirred.2.2 A bot_le hA hstable

/-- A finite solvable group with trivial two-core and a unique maximal
subgroup above its Sylow two-subgroup cannot have an elementary Sylow of order four. -/
public theorem not_elementary_four_sylow_of_unique_maximal
    {X : Type u} [Group X] [Finite X]
    (hsolv : Group.IsSolvable X) (hcore : pCore 2 X = ⊥)
    (P : Sylow 2 X) (hP : IsElementaryAbelian 2 P) (hcard : Nat.card P = 4)
    (M : Subgroup X) (hM : IsCoatom M) (hPM : (P : Subgroup X) ≤ M)
    (huniq : ∀ L : Subgroup X, IsCoatom L → (P : Subgroup X) ≤ L → L = M) :
    False := by
  obtain ⟨hS, hScard, hScore, K, hKn, hKS, hirred⟩ :=
    primitive_quotient_data hsolv hcore P hP hcard M hM hPM huniq
  let := hS
  let := hKn
  exact Theory.GroupTheory.not_elementary_four_corefree_irreducible_complement K
    ((P : Subgroup X).map (QuotientGroup.mk' M.normalCore)) hScard hKS hScore hirred

end Stellmacher.SectionThree
