module

public import CFSG.Quasithin.ChapterI.Section06To08.TightPGroup.Frattini
public import Theory.GroupTheory.PGroup.UniqueInvolution
public import Theory.Frattini.PGroup

/-!
# Cyclic-four fusion in the exceptional A₈ branch

A cyclic four V normalized by the centralizer of its involution t is TI:
a nontrivial intersection contains the unique involution of both conjugates.
We construct TightPGroupSetup with K=Q=V and H=G, prove Φ(V)≠1, and apply
I.7.5 to centralize every conjugate of V contained in T. A square identity
inside S and the earlier central-involution fusion rule then give exactly
V and Vˣ as that family. The two possible images of t exhibit the two
cosets of C_T(t)=S, giving |T|=512 when |S|=256.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 2.5.26, printed p.569, second paragraph.
These results do not yet construct V from the exceptional A₈ alternative.
The square condition is an explicit finite-model input; the order theorem
requires it only inside S, not for arbitrary ambient elements.
-/

public section

open Subgroup
open CFSG.Quasithin.ChapterI.Section06To08
namespace CFSG.Quasithin.Chapter2.A6ShadowRankOne
variable {G : Type*} [Group G] [Finite G]

/-- A cyclic four normalized by its involution centralizer is a TI subgroup. -/
theorem cyclicFour_ti (V : Subgroup G) (hV : Nat.card V = 4) [IsCyclic V]
    (t : G) (ht : t ∈ V) (ht2 : orderOf t = 2)
    (hn : centralizer ({t} : Set G) ≤ normalizer V) : IsTISubgroup V := by
  apply (isTISubgroup_iff V).mpr
  intro g hg a ha hga
  by_contra ha1
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) hV
  have ha2 : orderOf (a ^ (orderOf a / 2)) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos a).ne'
      (by simpa using hVp.dvd_orderOf (show (⟨a, ha⟩ : V) ≠ 1 from fun h => ha1 (congrArg Subtype.val h)))
  have hau : a ^ (orderOf a / 2) = t := by
    exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
      (show orderOf (⟨a ^ (orderOf a / 2), V.pow_mem ha _⟩ : V) = 2 by simpa using ha2)
      (show orderOf (⟨t, ht⟩ : V) = 2 by simpa using ht2))
  have hgu : MulAut.conj g (a ^ (orderOf a / 2)) ∈ V := by
    simpa only [map_pow, MulAut.conj_apply] using V.pow_mem hga (orderOf a / 2)
  have hgt : MulAut.conj g t = t := by
    rw [hau] at hgu
    exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
      (show orderOf (⟨MulAut.conj g t, hgu⟩ : V) = 2 by
        rw [← Subgroup.orderOf_coe, (MulAut.conj g).orderOf_eq, ht2])
      (show orderOf (⟨t, ht⟩ : V) = 2 by simpa using ht2))
  apply hg
  apply hn
  rw [mem_centralizer_singleton_iff]
  exact mul_inv_eq_iff_eq_mul.mp hgt

omit [Finite G] in
/-- Construct the exact I.7 setup with K=Q=V and H=G. The Sylow condition
inside H∩K is automatic because V itself is a two-group. -/
theorem cyclicFour_tightSetup (V T : Subgroup G)
    (hV : Nat.card V = 4) (hTI : IsTISubgroup V)
    (hT : IsPGroup 2 T) (hVT : V ≤ T) : TightPGroupSetup V ⊤ V T := by
  have hp : IsPGroup 2 V := IsPGroup.of_card (n := 2) hV
  have hn : V ≠ ⊥ := by
    intro he
    rw [he, Subgroup.card_bot] at hV
    contradiction
  have hemb : Theory.GroupTheory.IsTightlyEmbedded V := by
    refine ⟨by rw [hV]; decide, ?_⟩
    intro g hg
    have he : V ⊓ conjSubgroup V g = ⊥ := by
      apply eq_bot_iff.mpr
      intro y hy
      obtain ⟨a, ha, rfl⟩ := hy.2
      exact hTI g hg ⟨hy.1, a, ha, rfl⟩
    change Odd (Nat.card ↥(V ⊓ conjSubgroup V g))
    rw [he]
    simp
  exact ⟨hemb, hp, hn, le_inf le_top le_rfl,
    fun _ _ hr _ => hr.trans inf_le_right, hT, le_top, hVT⟩

/-- I.7.5 applies non-vacuously to a cyclic four: its Frattini subgroup is
nontrivial. Every conjugate contained in T therefore centralizes V. -/
theorem conjugate_cyclicFour_centralizes (V T : Subgroup G)
    (hV : Nat.card V = 4) [IsCyclic V] (hTI : IsTISubgroup V)
    (hT : IsPGroup 2 T) (hVT : V ≤ T) {g : G}
    (hg : conjSubgroup V g ≤ T) : conjSubgroup V g ≤ centralizer (V : Set G) := by
  have h := cyclicFour_tightSetup V T hV hTI hT hVT
  let : Fact (IsPGroup 2 V) := ⟨h.hQp⟩
  have hphi : frattini V ≠ ⊥ := by
    intro he
    let : IsElementaryAbelian 2 V := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp he
    have hd := IsElementaryAbelian.exponent_dvd_p 2 V
    rw [IsCyclic.exponent_eq_card, hV] at hd
    norm_num at hd
  by_cases he : conjSubgroup V g = V
  · rw [he]
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  · exact (lemma_I_7_5_commuting h hphi ⟨hg, g, mem_top _, rfl⟩ h.mem_family he).2

/-- The finite-model square condition and the genuine central fusion rule
reduce the entire conjugate family in T to V and Vˣ. -/
theorem conjugate_cyclicFour_eq_or_eq_conjugate
    (V T : Subgroup G) (v t z x : G)
    (hV : V = zpowers v) (hv : orderOf v = 4) (ht : v ^ 2 = t)
    (hT : IsPGroup 2 T) (hVT : V ≤ T)
    (hn : centralizer ({t} : Set G) ≤ normalizer V)
    (hsquares : ∀ a : G, a ∈ T → a ∈ centralizer (V : Set G) →
      orderOf a = 4 → a ^ 2 ∈ zpowers t ⊔ zpowers z)
    (hfusion : ∀ g : G, MulAut.conj g t ∈ zpowers t ⊔ zpowers z →
      MulAut.conj g t = t ∨ MulAut.conj g t = MulAut.conj x t)
    {g : G} (hg : conjSubgroup V g ≤ T) :
    conjSubgroup V g = V ∨ conjSubgroup V g = conjSubgroup V x := by
  have hvV : v ∈ V := hV ▸ mem_zpowers v
  have htV : t ∈ V := ht ▸ V.pow_mem hvV 2
  have ht2 : orderOf t = 2 := by rw [← ht, orderOf_pow, hv]; decide
  have hcard : Nat.card V = 4 := by rw [hV, Nat.card_zpowers, hv]
  let : IsCyclic V := hV ▸ inferInstance
  have hTI := cyclicFour_ti V hcard t htV ht2 hn
  have hc := conjugate_cyclicFour_centralizes V T hcard hTI hT hVT hg
  have hvg : MulAut.conj g v ∈ conjSubgroup V g := mem_map_of_mem _ hvV
  have hs := hsquares _ (hg hvg) (hc hvg) ((MulAut.conj g).orderOf_eq v |>.trans hv)
  rw [← map_pow, ht] at hs
  have hfix (y : G) (hy : MulAut.conj y t = t) : conjSubgroup V y = V := by
    apply mem_normalizer_iff_map_conj_eq.mp
    apply hn
    rw [mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp hy
  rcases hfusion g hs with he | he
  · exact Or.inl (hfix g he)
  · right
    have hy : MulAut.conj (x⁻¹ * g) t = t := by
      change x⁻¹ * g * t * (x⁻¹ * g)⁻¹ = t
      have hh := congrArg (MulAut.conj x⁻¹) he
      simpa only [MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc,
        inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel, mul_one] using hh
    have hh := congrArg (fun A => conjSubgroup A x) (hfix (x⁻¹ * g) hy)
    simpa only [conjSubgroup_conjSubgroup, mul_inv_cancel_left] using hh

/-- The full cyclic-four conjugate family and the Sylow order in the A₈
branch. The order follows by exhibiting the two cosets of C_T(t); neither
the two-conjugate conclusion nor the order of T is assumed. -/
theorem cyclicFour_conjugate_family_and_card
    (V T S : Subgroup G) (v t z x : G)
    (hV : V = zpowers v) (hv : orderOf v = 4) (ht : v ^ 2 = t)
    (hT : IsPGroup 2 T) (hVT : V ≤ T)
    (hn : centralizer ({t} : Set G) ≤ normalizer V)
    (hsquares : ∀ a : G, a ∈ S → a ∈ centralizer (V : Set G) →
      orderOf a = 4 → a ^ 2 ∈ zpowers t ⊔ zpowers z)
    (hfusion : ∀ g : G, MulAut.conj g t ∈ zpowers t ⊔ zpowers z →
      MulAut.conj g t = t ∨ MulAut.conj g t = MulAut.conj x t)
    (hCT : T ⊓ centralizer ({t} : Set G) = S)
    (hx : x ∈ T) (hxS : x ∉ S) (hS : Nat.card S = 256) :
    tightConjugateFamily ⊤ V T = {V, conjSubgroup V x} ∧ Nat.card T = 512 := by
  have htV : t ∈ V := ht ▸ V.pow_mem (hV ▸ mem_zpowers v) 2
  have hsquaresT : ∀ a : G, a ∈ T → a ∈ centralizer (V : Set G) →
      orderOf a = 4 → a ^ 2 ∈ zpowers t ⊔ zpowers z := by
    intro a ha hca ho
    apply hsquares a _ hca ho
    rw [← hCT]
    exact ⟨ha, mem_centralizer_singleton_iff.mpr (hca t htV).symm⟩
  have hconj (g : G) (hg : g ∈ T) : conjSubgroup V g ≤ T := by
    have hnT : conjSubgroup T g = T := mem_normalizer_iff_map_conj_eq.mp (T.le_normalizer hg)
    exact (conjSubgroup_mono hVT g).trans_eq hnT
  constructor
  · ext W
    constructor
    · rintro ⟨hWT, g, _, rfl⟩
      rcases conjugate_cyclicFour_eq_or_eq_conjugate V T v t z x hV hv ht hT hVT
        hn hsquaresT hfusion hWT with he | he <;> simp [he]
    · intro hW
      rcases Set.mem_insert_iff.mp hW with rfl | hW
      · exact ⟨hVT, 1, mem_top _, conjSubgroup_one _⟩
      · have he : W = conjSubgroup V x := Set.mem_singleton_iff.mp hW
        subst W
        exact ⟨hconj x hx, x, mem_top _, rfl⟩
  · have hvV : v ∈ V := hV ▸ mem_zpowers v
    have htV : t ∈ V := ht ▸ V.pow_mem hvV 2
    have ht2 : orderOf t = 2 := by rw [← ht, orderOf_pow, hv]; decide
    have hcard : Nat.card V = 4 := by rw [hV, Nat.card_zpowers, hv]
    let : IsCyclic V := hV ▸ inferInstance
    have hTI := cyclicFour_ti V hcard t htV ht2 hn
    have hroot (g : G) (hg : g ∈ T) :
        MulAut.conj g t = t ∨ MulAut.conj g t = MulAut.conj x t := by
      have hgV := hconj g hg
      have hc := conjugate_cyclicFour_centralizes V T hcard hTI hT hVT hgV
      have hvg : MulAut.conj g v ∈ conjSubgroup V g := mem_map_of_mem _ hvV
      apply hfusion
      have hh := hsquaresT _ (hgV hvg) (hc hvg) ((MulAut.conj g).orderOf_eq v |>.trans hv)
      simpa only [← map_pow, ht] using hh
    have hfix (g : G) (hg : g ∈ T) (he : MulAut.conj g t = t) : g ∈ S := by
      rw [← hCT]
      exact ⟨hg, mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)⟩
    have hind : S.relIndex T = 2 := by
      apply relIndex_eq_two_iff_exists_notMem_and'.mpr
      refine ⟨x⁻¹, T.inv_mem hx, fun hh => hxS (by simpa only [inv_inv] using S.inv_mem hh), ?_⟩
      intro g hg
      rcases hroot g hg with he | he
      · exact Or.inr (hfix g hg he)
      · left
        apply hfix (x⁻¹ * g) (T.mul_mem (T.inv_mem hx) hg)
        have hh := congrArg (MulAut.conj x⁻¹) he
        simpa only [MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc,
          inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel, mul_one] using hh
    have hST : S ≤ T := hCT ▸ inf_le_left
    have hcount := relIndex_mul_relIndex (⊥ : Subgroup G) S T bot_le hST
    simpa only [relIndex_bot_left, hind, hS] using hcount.symm

end CFSG.Quasithin.Chapter2.A6ShadowRankOne
