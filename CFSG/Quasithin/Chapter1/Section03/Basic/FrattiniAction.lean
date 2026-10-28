module

public import Theory.GroupAction.OddInvolutionFrattini

/-!
# The Frattini action step for solvable uniqueness subgroups

This proves the action argument for Aschbacher–Smith, *The Classification of
Quasithin Groups*, combined manuscript of 1 March 2004, Lemma 1.3.2(4),
printed p. 509. If the Frattini subgroup of a two-group acts trivially on an
abelian irreducible section, the action consists of commuting involutions.
Each fixed subgroup is invariant, so each actor is either identity or inversion.
Every cyclic subgroup is then invariant, forcing the section to be cyclic.

Apply this to the image of [P, Φ(S)] in P/Φ(P). Irreducibility and noncyclicity
force that image to be the whole quotient; Frattini nongeneration gives
[P, Φ(S)] = P. Thus the argument needs no classification of two-dimensional
representations and no faithfulness assumption.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter1.XiAction

/-- Commuting involutions have only cyclic irreducible abelian sections. -/
theorem isCyclic_of_irreducible_involutive
    {S V : Type*} [Group S] [Group V] [IsMulCommutative V]
    (f : S →* MulAut V) (hpow : ∀ s, f s ^ 2 = 1)
    (hirr : ∀ A : Subgroup V,
      (∀ s : S, ∀ a ∈ A, f s a ∈ A) → A = ⊥ ∨ A = ⊤) : IsCyclic V := by
  have hinv (s : S) : (f s)⁻¹ = f s :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hpow s)
  have hcomm (s t : S) : f s * f t = f t * f s := by
    calc
      f s * f t = (f s * f t)⁻¹ := by simpa only [map_mul] using (hinv (s * t)).symm
      _ = f t * f s := by rw [mul_inv_rev, hinv, hinv]
  have hsign (s : S) : (∀ v, f s v = v) ∨ (∀ v, f s v = v⁻¹) := by
    let C := (f s).toMonoidHom.eqLocus (MonoidHom.id V)
    have hC : ∀ t : S, ∀ v ∈ C, f t v ∈ C := by
      intro t v hv
      change f s (f t v) = f t v
      have h := DFunLike.congr_fun (hcomm s t) v
      change f s (f t v) = f t (f s v) at h
      exact h.trans (congrArg (f t) hv)
    rcases hirr C hC with hb | ht
    · right
      intro v
      have hv : f s v * v ∈ C := by
        change f s (f s v * v) = f s v * v
        rw [map_mul]
        have hh := DFunLike.congr_fun (hpow s) v
        change f s (f s v) = v at hh
        rw [hh, mul_comm]
      exact mul_eq_one_iff_eq_inv.mp (Subgroup.mem_bot.mp (hb ▸ hv))
    · exact Or.inl (fun v => show v ∈ C from ht.symm ▸ mem_top v)
  by_cases hV : Subsingleton V
  · let _ := hV
    infer_instance
  · have : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
    obtain ⟨v, hv⟩ := exists_ne (1 : V)
    have hstable : ∀ s : S, ∀ a ∈ zpowers v, f s a ∈ zpowers v := by
      intro s a ha
      rcases hsign s with h | h
      · simpa only [h] using ha
      · simpa only [h] using (zpowers v).inv_mem ha
    rcases hirr (zpowers v) hstable with hb | ht
    · exact False.elim (hv (Subgroup.mem_bot.mp (hb ▸ mem_zpowers v)))
    · exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨v, ht⟩

/-- If a two-group acts irreducibly on a noncyclic p-group's Frattini quotient,
its Frattini displacements cannot lie in a proper invariant subgroup. -/
theorem eq_top_of_frattini_displacements
    {S K : Type*} [Group S] [Group K] [Finite S] [Finite K]
    (hS : IsPGroup 2 S) {p : ℕ} [Fact p.Prime] (hK : IsPGroup p K)
    (hnc : ¬ IsCyclic K) (f : S →* MulAut K)
    (hirr : ∀ A : Subgroup (K ⧸ frattini K),
      (∀ s : S, ∀ a ∈ A, ((quotientAut (frattini K)).comp f) s a ∈ A) →
        A = ⊥ ∨ A = ⊤)
    (D : Subgroup K) (hD : ∀ s : S, ∀ d ∈ D, f s d ∈ D)
    (hdisp : ∀ s ∈ frattini S, ∀ k : K, k⁻¹ * f s k ∈ D) : D = ⊤ := by
  let _ : Fact (IsPGroup 2 S) := ⟨hS⟩
  let _ : Fact (IsPGroup p K) := ⟨hK⟩
  let _ : IsElementaryAbelian p (K ⧸ frattini K) := isElementaryAbelian_quotient_frattini
  let q := QuotientGroup.mk' (frattini K)
  let fq := (quotientAut (frattini K)).comp f
  have hA : ∀ s : S, ∀ a ∈ D.map q, fq s a ∈ D.map q := by
    rintro s a ⟨d, hd, rfl⟩
    exact ⟨f s d, hD s d hd, (quotientAut_apply_mk _ _ _).symm⟩
  rcases hirr (D.map q) hA with hb | ht
  · have hfix : ∀ s ∈ frattini S, fq s = 1 := by
      intro s hs
      apply MulEquiv.ext
      intro v
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (frattini K) v
      have hh : q (k⁻¹ * f s k) = 1 := Subgroup.mem_bot.mp (hb ▸ mem_map_of_mem q (hdisp s hs k))
      rw [map_mul, map_inv] at hh
      change quotientAut (frattini K) (f s) (QuotientGroup.mk' (frattini K) k) = _
      rw [quotientAut_apply_mk]
      exact (inv_mul_eq_one.mp hh).symm
    have hpow : ∀ s, fq s ^ 2 = 1 := by
      intro s
      rw [← map_pow]
      exact hfix _ (pth_power_mem_frattini_of_isPGroup (p := 2) s)
    exact False.elim (OddInvolutionFrattini.noncyclic_frattini_quotient hnc
      (isCyclic_of_irreducible_involutive fq hpow hirr))
  · apply frattini_nongenerating
    have hh := congrArg (Subgroup.comap q) ht
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh

end CFSG.Quasithin.Chapter1.XiAction

namespace CFSG.Quasithin.Chapter1

variable {G : Type*} [Group G]

/-- Conjugation on the actual Frattini quotient of a normalized subgroup. -/
def frattiniConjugationAction (S P : Subgroup G) (hn : S ≤ normalizer (P : Set G)) :
    S →* MulAut (P ⧸ frattini P) :=
  let _ := conjMulDistribMulActionOfLeNormalizer S P hn
  (quotientAut (frattini P)).comp (MulDistribMulAction.toMulAut S P)

end CFSG.Quasithin.Chapter1

namespace CFSG.Quasithin.Chapter1.XiAction

open scoped commutatorElement

/-- The ambient form of the Frattini displacement argument. -/
theorem eq_commutator_frattini_of_irreducible
    {G : Type*} [Group G] [Finite G] (P S : Subgroup G)
    (hn : S ≤ normalizer (P : Set G)) (hS : IsPGroup 2 S)
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) (hnc : ¬ IsCyclic P)
    (hirr : ∀ A : Subgroup (P ⧸ frattini P),
      (∀ s : S, ∀ a ∈ A, frattiniConjugationAction S P hn s a ∈ A) →
        A = ⊥ ∨ A = ⊤) :
    P = ⁅P, (frattini S).map S.subtype⁆ := by
  let F := (frattini S).map S.subtype
  let D := ⁅P, F⁆
  have hFS : F ≤ S := map_subtype_le _
  have hSF : S ≤ normalizer (F : Set G) := by
    have hh := (frattini S).le_normalizer_map S.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hDP : D ≤ P := le_normalizer_iff_commutator_le_left.mp (hFS.trans hn)
  have hSD : S ≤ normalizer (D : Set G) := by
    apply subgroup_le_normalizer_of_conj_mem
    intro s d hd
    have hm : D.map (MulAut.conj (s : G)).toMonoidHom ≤ D := by
      rw [map_commutator]
      apply commutator_mono
      · rintro _ ⟨x, hx, rfl⟩
        exact (mem_normalizer_iff.mp (hn s.property) x).mp hx
      · rintro _ ⟨x, hx, rfl⟩
        exact (mem_normalizer_iff.mp (hSF s.property) x).mp hx
    exact hm (mem_map_of_mem _ hd)
  let _ := conjMulDistribMulActionOfLeNormalizer S P hn
  have htop : D.subgroupOf P = ⊤ := by
    apply eq_top_of_frattini_displacements hS hP hnc
      (MulDistribMulAction.toMulAut S P) hirr (D.subgroupOf P)
    · intro s d hd
      exact (mem_normalizer_iff.mp (hSD s.property) (d : G)).mp hd
    · intro s hs k
      change (k : G)⁻¹ * ((s : G) * (k : G) * (s : G)⁻¹) ∈ D
      have hh := commutator_mem_commutator (P.inv_mem k.property)
        (mem_map_of_mem S.subtype hs)
      simpa only [D, F, Subgroup.coe_subtype, commutatorElement_def, inv_inv, mul_assoc] using hh
  have hh := congrArg (Subgroup.map P.subtype) htop
  simpa only [map_subgroupOf_eq_of_le hDP, ← MonoidHom.range_eq_map, range_subtype] using hh.symm

end CFSG.Quasithin.Chapter1.XiAction
