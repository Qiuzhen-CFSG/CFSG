module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.QuotientGeometry.Descent
public import Theory.GroupTheory.SylowElementConjugacy


/-!
# Root-four Sylow placement and fusion in five-centralizers

Let E have order five in the centralizer of the selected root involution t,
and put M = C_G(E). The marked normalizer of U(t) identifies E with a subgroup
of its A₅ factor. Assuming that order-five subgroups of A₅ are self-centralizing,
N_M(U(t)) embeds in A₄ × E, so its order divides sixty. The normalizer criterion
then makes the literal U(t).subgroupOf M a Sylow two-subgroup of M.

The root involution lies in U(t): its A₅ coordinate in C_G(t) is central, hence
trivial. The A₄ factor centralizes E and conjugates any two involutions in U(t).
Sylow conjugacy therefore gives fusion inside M. The final application descends
this result to M/E, keeping the separately produced centralizer bounds explicit.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2(2), printed p.261,
using the marked normalizer geometry of 47.1. The concrete A₅ premise and the
centralizer bounds are discharged by the parent quotient-geometry assembly.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent
open InvolutionGeometry
namespace SylowFusion
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

private def embedding (S : SelectedGeometry D) : A4 × A5 →* G :=
  (normalizer (rootCore S.t : Set G)).subtype.comp S.normalizerEquiv.symm.toMonoidHom

private theorem embedding_injective (S : SelectedGeometry D) :
    Function.Injective (embedding S) :=
  Subtype.val_injective.comp S.normalizerEquiv.symm.injective

private theorem five_placement (S : SelectedGeometry D) (E : Subgroup G)
    (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer S.t)
    {x : G} (hx : x ∈ E) : ∃ b : A5, embedding S (1, b) = x := by
  have hc := five_le_fiveFactor S.model E hE hEt hx
  rw [← S.component_eq, ← S.normalizer_component] at hc
  obtain ⟨⟨a, b⟩, ha, hab⟩ := hc
  have ha1 : a = 1 := ha.1
  exact ⟨b, by simpa [ha1, embedding] using hab⟩

private def fiveEmbedding (S : SelectedGeometry D) : A5 →* G :=
  (embedding S).comp (MonoidHom.inr A4 A5)

private def fivePreimage (S : SelectedGeometry D) (E : Subgroup G) : Subgroup A5 :=
  E.comap (fiveEmbedding S)

private theorem fivePreimage_card (S : SelectedGeometry D) (E : Subgroup G)
    (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer S.t) :
    Nat.card (fivePreimage S E) = 5 := by
  let f : fivePreimage S E →* E :=
    ((fiveEmbedding S).comp (fivePreimage S E).subtype).codRestrict E (fun b => b.property)
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      have hh : embedding S (1, a.val) = embedding S (1, b.val) :=
        congrArg (fun x : E => (x : G)) hab
      exact Prod.mk.inj (embedding_injective S hh) |>.2
    · intro x
      obtain ⟨b, hb⟩ := five_placement S E hE hEt x.property
      exact ⟨⟨b, by change embedding S (1, b) ∈ E; rw [hb]; exact x.property⟩,
        Subtype.ext hb⟩
  exact (Nat.card_congr (MulEquiv.ofBijective f hf).toEquiv).trans hE

private theorem fst_factor_centralizes (S : SelectedGeometry D) (E : Subgroup G)
    (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer S.t) (a : A4) :
    embedding S (a, 1) ∈ centralizer (E : Set G) := by
  intro x hx
  obtain ⟨b, rfl⟩ := five_placement S E hE hEt hx
  rw [← map_mul, ← map_mul]
  congr 1

/-- The selected root involution belongs to the intrinsic marked root four-group. -/
theorem root_mem_rootCore (S : SelectedGeometry D) : S.t ∈ rootCore S.t := by
  let tC : involutionCentralizer S.t := ⟨S.t, mem_centralizer_singleton_iff.mpr rfl⟩
  apply (S.model.mem_rootCore_iff tC).mpr
  have hc : (S.model.equiv tC).2 ∈ center A5 := by
    rw [mem_center_iff]
    intro b
    let y := S.model.equiv.symm (1, b)
    have ht : y * tC = tC * y := by
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp y.property
    have hh := congrArg (fun v => (S.model.equiv v).2) ht
    simpa [y] using hh
  rw [alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 5))] at hc
  exact hc

/-- A single kernel-checked calculation in the twelve-element alternating group. -/
private theorem a4_fusion : ∀ a b : A4, a ^ 2 = 1 → a ≠ 1 →
    b ^ 2 = 1 → b ≠ 1 → ∃ c : A4, c * a * c⁻¹ = b := by
  decide +kernel

private theorem relative_normalizer_card_dvd (S : SelectedGeometry D)
    (h5 : ∀ F : Subgroup A5, Nat.card F = 5 → centralizer (F : Set A5) = F)
    (E : Subgroup G) (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer S.t) :
    Nat.card (normalizer ((rootCore S.t).subgroupOf (centralizer (E : Set G)) :
      Set (centralizer (E : Set G)))) ∣ 60 := by
  let M := centralizer (E : Set G)
  let R := (rootCore S.t).subgroupOf M
  let N := normalizer (rootCore S.t : Set G)
  have hRM := rootCore_le_centralizer S.model E hEt
  let j : normalizer (R : Set M) →* N :=
    { toFun := fun x => ⟨x.val.val, by
        have hh := congrArg (fun H : Subgroup M => x.val ∈ H)
          (subgroupOf_normalizer_eq hRM)
        exact hh.mpr x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let f := S.normalizerEquiv.toMonoidHom.comp j
  have hf (x : normalizer (R : Set M)) : embedding S (f x) = x.val.val := by
    simp [embedding, f, j]
  have hfmem (x : normalizer (R : Set M)) : (f x).2 ∈ fivePreimage S E := by
    rw [← h5 _ (fivePreimage_card S E hE hEt)]
    intro b hb
    have hh : (1, b) * f x = f x * (1, b) := by
      apply embedding_injective S
      rw [map_mul, map_mul, hf]
      exact x.val.property _ hb
    exact congrArg Prod.snd hh
  let f' := f.codRestrict ((⊤ : Subgroup A4).prod (fivePreimage S E))
    (fun x => ⟨mem_top _, hfmem x⟩)
  have hinj : Function.Injective f' := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have hh : f x = f y := congrArg Subtype.val hxy
    simpa only [hf] using congrArg (embedding S) hh
  have hd := card_dvd_of_injective f' hinj
  rw [Nat.card_congr (prodEquiv (⊤ : Subgroup A4) (fivePreimage S E)).toEquiv,
    Nat.card_prod, Nat.card_congr topEquiv.toEquiv,
    nat_card_alternatingGroup, fivePreimage_card S E hE hEt] at hd
  norm_num at hd
  exact hd

/-- The literal root four-subgroup is a Sylow subgroup of the five-centralizer. -/
theorem rootCore_isSylow (S : SelectedGeometry D)
    (h5 : ∀ F : Subgroup A5, Nat.card F = 5 → centralizer (F : Set A5) = F)
    (E : Subgroup G) (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer S.t) :
    ∃ P : Sylow 2 (centralizer (E : Set G)),
      (P : Subgroup (centralizer (E : Set G))) =
        (rootCore S.t).subgroupOf (centralizer (E : Set G)) := by
  let M := centralizer (E : Set G)
  let R := (rootCore S.t).subgroupOf M
  have hR : Nat.card R = 2 ^ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (rootCore_le_centralizer S.model E hEt)).toEquiv, S.model.rootCore_card]
    rfl
  have hn : ¬ 2 ∣ R.index := by
    intro hi
    have hd : 2 ^ (2 + 1) ∣ Nat.card M := by
      rw [← R.card_mul_index, hR]
      exact Nat.mul_dvd_mul_left 4 hi
    have hn := Sylow.prime_pow_dvd_card_normalizer hd hR
    have hh := hn.trans (relative_normalizer_card_dvd S h5 E hE hEt)
    norm_num at hh
  exact ⟨(IsPGroup.of_card hR).toSylow hn, rfl⟩

private theorem root_coordinates (S : SelectedGeometry D) {u : G}
    (hu : u ∈ rootCore S.t) : ∃ a : A4, embedding S (a, 1) = u := by
  rw [← S.normalizer_core] at hu
  obtain ⟨⟨a, b⟩, hab, hu⟩ := hu
  have hb : b = 1 := hab.2
  exact ⟨a, by simpa [embedding, hb] using hu⟩

private theorem root_fusion (S : SelectedGeometry D)
    (E : Subgroup G) (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer S.t)
    (x : centralizer (E : Set G)) (hx : orderOf x = 2)
    (hxR : (x : G) ∈ rootCore S.t) : IsConj x (rootInCentralizer E S.t hEt) := by
  obtain ⟨a, ha⟩ := root_coordinates S hxR
  obtain ⟨b, hb⟩ := root_coordinates S (root_mem_rootCore S)
  have ha2 : a ^ 2 = 1 := by
    have hh : ((a, 1) : A4 × A5) ^ 2 = 1 := by
      apply embedding_injective S
      rw [map_pow, map_one, ha]
      exact congrArg Subtype.val (hx ▸ pow_orderOf_eq_one x)
    exact congrArg Prod.fst hh
  have hb2 : b ^ 2 = 1 := by
    have hh : ((b, 1) : A4 × A5) ^ 2 = 1 := by
      apply embedding_injective S
      rw [map_pow, map_one, hb]
      exact S.other.1 ▸ pow_orderOf_eq_one S.t
    exact congrArg Prod.fst hh
  have ha1 : a ≠ 1 := by
    intro ha1
    have hx1 : x = 1 := by
      apply Subtype.ext
      rw [← ha, ha1]
      exact map_one (embedding S)
    simp [hx1] at hx
  have hb1 : b ≠ 1 := by
    intro hb1
    have ht1 : S.t = 1 := by
      rw [← hb, hb1]
      exact map_one (embedding S)
    have ht := S.other.1
    simp [ht1] at ht
  obtain ⟨c, hc⟩ := a4_fusion a b ha2 ha1 hb2 hb1
  refine isConj_iff.mpr ⟨⟨embedding S (c, 1), fst_factor_centralizes S E hE hEt c⟩, ?_⟩
  apply Subtype.ext
  change embedding S (c, 1) * (x : G) * (embedding S (c, 1))⁻¹ = S.t
  rw [← ha, ← hb, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Prod.ext hc (by simp)

/-- All involutions of the literal five-centralizer fuse to its root involution. -/
theorem localInvolutionFusion (S : SelectedGeometry D)
    (h5 : ∀ F : Subgroup A5, Nat.card F = 5 → centralizer (F : Set A5) = F) :
    LocalInvolutionFusion S.t := by
  intro E hE hEt x hx
  obtain ⟨P, hP⟩ := rootCore_isSylow S h5 E hE hEt
  obtain ⟨y, hxy⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
  have hy : orderOf (y : centralizer (E : Set G)) = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hxy
    change MulAut.conj g x = (y : centralizer (E : Set G)) at hg
    rw [← hg, MulEquiv.orderOf_eq, hx]
  have hyR : ((y : centralizer (E : Set G)) : G) ∈ rootCore S.t := by
    have hh : (y : centralizer (E : Set G)) ∈ (P : Subgroup _) := y.property
    simp only [hP] at hh
    exact hh
  exact hxy.trans (root_fusion S E hE hEt y hy hyR)

/-- Application to the literal quotient: only the separate centralizer bounds remain. -/
theorem quotientInvolutionData (S : SelectedGeometry D)
    (h5 : ∀ F : Subgroup A5, Nat.card F = 5 → centralizer (F : Set A5) = F)
    (hC : LocalCentralizerBounds S.t) (E : Subgroup G) (hE : Nat.card E = 5)
    (hEt : E ≤ involutionCentralizer S.t) : Nonempty (QuotientInvolutionData E S.t hEt) :=
  quotientInvolutionData_of_local S.t S.other.1 hC (localInvolutionFusion S h5) E hE hEt

end SylowFusion
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent
