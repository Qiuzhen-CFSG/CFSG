module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Definitions
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.SylowNormalIntersection
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.Fintype.Perm

/-!
# The rank-two shadow obstructs cyclic three-subgroups in a Borel

Let D be normal in X with a Sylow two-subgroup as supplement. Every
three-subgroup of X lies in D, since X/D is a two-group. If M meets D
properly and contains the Sylow two-subgroup of X, rank-one proper-overgroup
uniqueness places M ∩ D in a Borel. Cyclicity of the Borel's three-subgroups
therefore makes the Sylow three-subgroups of YS cyclic whenever YS ≤ M.

The genuine shadow YS/O₂,Φ(YS) ≅ S₃ × S₃ contradicts this: a surjective
image of a cyclic Sylow three-subgroup is cyclic, while its order is divisible
by nine and its exponent divides six. No replacement of O₂,Φ by O₂ and
no additional assumption on the kernel of the shadow projection is used.
Normality here is relative to X, the source's component-action quotient.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.41(2),
printed p.1138, and the initial selection in the final proof of 15.3.35, p.1139.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.RankOne

private theorem three_le_of_two_quotient {X : Type*} [Group X]
    (D A : Subgroup X) [D.Normal] (hD : IsPGroup 2 (X ⧸ D))
    (hA : IsPGroup 3 A) : A ≤ D := by
  let q := QuotientGroup.mk' D
  have hd : Disjoint (A.map q) ⊤ :=
    (hA.map q).disjoint_of_coprime (hD.to_subgroup ⊤) (by decide : Nat.Coprime 3 2)
  have hle : A ≤ q.ker := (map_eq_bot_iff A).mp (disjoint_top.mp hd)
  simpa only [q, QuotientGroup.ker_mk'] using hle

private theorem not_shadow_of_cyclic {X : Type*} [Group X] [Finite X]
    (Y S : Subgroup X) (hs : RankTwoShadow Y S)
    (hc : ∀ A : Subgroup (Y ⊔ S : Subgroup X), IsPGroup 3 A → IsCyclic A) : False := by
  obtain ⟨e⟩ := hs
  let H := Y ⊔ S
  let P : Sylow 3 H := Sylow.nonempty.some
  let : IsCyclic P := hc P P.isPGroup'
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (twoFrattiniCore H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective hf
  let : IsCyclic Q := isCyclic_of_surjective (f.subgroupMap (P : Subgroup H))
    (f.subgroupMap_surjective (P : Subgroup H))
  have hcard : 9 ∣ Nat.card Q := Q.pow_dvd_card_of_pow_dvd_card (n := 2) (by
    norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial])
  have hpow : ∀ x : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), x ^ 6 = 1 := by
    decide +kernel
  have he : Monoid.exponent Q ∣ 6 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    (fun x => Subtype.ext (hpow x))
  rw [IsCyclic.exponent_eq_card] at he
  exact (by decide : ¬ 9 ∣ 6) (hcard.trans he)

/-- A proper intersection in a rank-one component cannot support the rank-two shadow.
The normal component has a two-group supplement; its proper Sylow overgroups
have cyclic three-subgroups. -/
theorem no_shadow_of_borel_three_cyclic {X : Type*} [Group X] [Finite X]
    (D M Y S : Subgroup X) [D.Normal]
    (hgen : D ⊔ S = ⊤) (hc : LocalConfiguration D M Y S)
    (hproper : M ⊓ D < D)
    (hb : ∀ T : Sylow 2 D,
      (∀ U : Subgroup D, (T : Subgroup D) ≤ U → U < ⊤ →
        U ≤ normalizer ((T : Subgroup D) : Set D)) ∧
      (∀ A : Subgroup D, IsPGroup 3 A →
        A ≤ normalizer ((T : Subgroup D) : Set D) → IsCyclic A)) : False := by
  obtain ⟨P, hP⟩ := hc.sylow
  obtain ⟨T, hT⟩ := P.exists_subgroupOf_eq_of_normal D
  rw [hP] at hT
  have hMD : M.subgroupOf D < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    have hDM := subgroupOf_eq_top.mp he
    exact hproper.not_ge (le_inf hDM le_rfl)
  have hTM : (T : Subgroup D) ≤ M.subgroupOf D := by
    rw [hT]
    intro x hx
    exact hc.sylow_le hx
  have hMB := (hb T).1 (M.subgroupOf D) hTM hMD
  have hquot : IsPGroup 2 (X ⧸ D) :=
    isPGroup_quotient_of_sup_eq_top D S (hP ▸ P.isPGroup') hgen
  let H := Y ⊔ S
  have hHM : H ≤ M := sup_le (hc.yplus_le.trans inf_le_left) hc.sylow_le
  apply not_shadow_of_cyclic Y S hc.shadow
  intro A hA
  let K := A.map H.subtype
  have hK : IsPGroup 3 K := hA.map H.subtype
  have hKD : K ≤ D := three_le_of_two_quotient D K hquot hK
  have hKM : K ≤ M := (map_subtype_le A).trans hHM
  have hKN : K.subgroupOf D ≤ normalizer ((T : Subgroup D) : Set D) :=
    (subgroupOf_mono D hKM).trans hMB
  have hcK : IsCyclic (K.subgroupOf D) := (hb T).2 _ hK.comap_subtype hKN
  have hcK' : IsCyclic K := (subgroupOfEquivOfLe hKD).isCyclic.mp hcK
  exact (A.equivMapOfInjective H.subtype H.subtype_injective).isCyclic.mpr hcK'

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.RankOne
