module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.SylowTransport

/-!
# Irreducibility obstructions for invariant Ξ embeddings

The odd complement injects into a component's two-core quotient. In particular,
the cyclic cases of A.3.15 cannot occur after a valid application of that theorem.
An invariant cyclic subgroup lies in the Frattini subgroup; power automorphisms,
even together with a single graph involution, cannot act irreducibly on the
noncyclic Frattini quotient.

The power-action assertions concern the actual conjugation action, so their
application to concrete Lie-type groups still requires the corresponding torus
and automorphism computations. This module does not assert the classification
of invariant embeddings. `SylowTransport` supplies the separately strengthened
input and its genuine Sylow and product transports. Passing the complement
further to the simple central quotient uses explicit coprimality with the
center; the source's multiplier results must discharge this premise.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of Proposition 1.3.4, printed pp. 510–511;
Lemma A.3.15, printed pp. 50–51.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge

variable {G : Type*} [Group G]

/-- The actual inclusion followed by the component's two-core quotient. -/
def componentMap {P L : Subgroup G} (hPL : P ≤ L) : P →* XiQuotient L :=
  (QuotientGroup.mk' (pCore 2 L)).comp (inclusion hPL)

theorem componentMap_injective {p : ℕ} {P L : Subgroup G}
    (hP : IsPGroup p P) (ho : Odd p) (hPL : P ≤ L) :
    Function.Injective (componentMap hPL) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hc : inclusion hPL a ∈ pCore 2 L := (QuotientGroup.eq_one_iff _).mp ha
  have hd := (isPGroup_pCoreIn 2 L).disjoint_of_coprime hP
    (Nat.coprime_two_left.mpr ho)
  exact Subtype.ext (hd.le_bot ⟨mem_map_of_mem L.subtype hc, a.property⟩)

theorem component_image_not_cyclic [Finite G] {p : ℕ} {T X P H L : Subgroup G}
    (h : LocalInput p T X P H) (hPL : P ≤ L) :
    ¬ IsCyclic (componentMap hPL).range := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  intro hc
  let _ := hc
  apply h.complement_not_cyclic
  exact isCyclic_of_injective (componentMap hPL).rangeRestrict
    (fun _ _ he => componentMap_injective h.odd_complement.isPGroup h.odd hPL
      (congrArg Subtype.val he))

/-- An invariant cyclic subgroup cannot survive in an irreducible noncyclic section. -/
theorem cyclic_invariant_le_frattini [Finite G] {p : ℕ} {T X P H : Subgroup G}
    (h : LocalInput p T X P H) (A : Subgroup P) [IsCyclic A]
    (hA : ∀ s : (T ⊓ normalizer P : Subgroup G),
      ∀ a ∈ A.map (QuotientGroup.mk' (frattini P)),
        frattiniConjugationAction (T ⊓ normalizer P) P inf_le_right s a ∈
          A.map (QuotientGroup.mk' (frattini P))) : A ≤ frattini P := by
  rcases h.irreducible _ hA with hb | ht
  · simpa only [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hb
  · have he : A = ⊤ := frattini_nongenerating (by
      have hh := congrArg (Subgroup.comap (QuotientGroup.mk' (frattini P))) ht
      simpa only [comap_map_eq, QuotientGroup.ker_mk', comap_top] using hh)
    have hi : IsCyclic (⊤ : Subgroup P) := he ▸ inferInstance
    let _ := hi
    exact False.elim (h.complement_not_cyclic
      (isCyclic_of_surjective topEquiv.toMonoidHom topEquiv.surjective))

/-- The two cyclic factors in A.3.15(3) cannot generate P when the first
factor is invariant. The other factor would generate modulo Φ(P), hence all of P. -/
theorem not_cyclic_factorization [Finite G] {p : ℕ} {T X P H : Subgroup G}
    (h : LocalInput p T X P H) (A B : Subgroup P) [IsCyclic A] [IsCyclic B]
    (hgen : A ⊔ B = ⊤)
    (hA : ∀ s : (T ⊓ normalizer P : Subgroup G),
      ∀ a ∈ A.map (QuotientGroup.mk' (frattini P)),
        frattiniConjugationAction (T ⊓ normalizer P) P inf_le_right s a ∈
          A.map (QuotientGroup.mk' (frattini P))) : False := by
  have hAF := cyclic_invariant_le_frattini h A hA
  have hB : B = ⊤ := frattini_nongenerating (by
    apply top_unique
    rw [← hgen]
    exact sup_le (hAF.trans le_sup_right) le_sup_left)
  have hc : IsCyclic (⊤ : Subgroup P) := hB ▸ inferInstance
  let _ := hc
  exact h.complement_not_cyclic
    (isCyclic_of_surjective topEquiv.toMonoidHom topEquiv.surjective)

/-- Actual normalization implies invariance in the Frattini quotient. -/
theorem cyclic_normalized_le_frattini [Finite G] {p : ℕ} {T X P H : Subgroup G}
    (h : LocalInput p T X P H) (A : Subgroup P) [IsCyclic A]
    (hn : T ⊓ normalizer P ≤ normalizer (A.map P.subtype)) :
    A ≤ frattini P := by
  apply cyclic_invariant_le_frattini h A
  intro s a ha
  obtain ⟨b, hb, rfl⟩ := ha
  let _ := conjMulDistribMulActionOfLeNormalizer (T ⊓ normalizer P) P inf_le_right
  refine ⟨MulDistribMulAction.toMulAut (T ⊓ normalizer P : Subgroup G) P s b, ?_, ?_⟩
  · have hm := (mem_normalizer_iff.mp (hn s.property) (b : G)).mp
      (mem_map_of_mem P.subtype hb)
    have hv : (MulDistribMulAction.toMulAut (T ⊓ normalizer P : Subgroup G) P s b : G) =
        (s : G) * b * (s : G)⁻¹ := rfl
    obtain ⟨c, hc, he⟩ := hm
    have he' : c = MulDistribMulAction.toMulAut (T ⊓ normalizer P : Subgroup G) P s b :=
      Subtype.ext (he.trans hv.symm)
    exact he' ▸ hc
  · exact (quotientAut_apply_mk _ _ _).symm

private theorem cyclic_of_irreducible_power_action
    {S V : Type*} [Group S] [Group V] (f : S →* MulAut V)
    (hirr : ∀ A : Subgroup V,
      (∀ s : S, ∀ a ∈ A, f s a ∈ A) → A = ⊥ ∨ A = ⊤)
    (hpower : ∀ s v, f s v ∈ zpowers v) : IsCyclic V := by
  by_cases hV : Subsingleton V
  · let _ := hV
    infer_instance
  · let _ : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
    obtain ⟨v, hv⟩ := exists_ne (1 : V)
    have hstable : ∀ s : S, ∀ a ∈ zpowers v, f s a ∈ zpowers v :=
      fun s a ha => (zpowers_le.mpr ha) (hpower s a)
    rcases hirr (zpowers v) hstable with hb | ht
    · exact False.elim (hv (Subgroup.mem_bot.mp (hb ▸ mem_zpowers v)))
    · exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨v, ht⟩

/-- Field actions on a torus preserve cyclic subgroups, so they cannot supply
the action required by the intrinsic input. The premise is about the actual action. -/
theorem not_power_action [Finite G] {p : ℕ} {T X P H : Subgroup G}
    (h : LocalInput p T X P H) :
    ¬ ∀ s v, frattiniConjugationAction (T ⊓ normalizer P) P inf_le_right s v ∈
      zpowers v := by
  intro hp
  exact OddInvolutionFrattini.noncyclic_frattini_quotient h.complement_not_cyclic
    (cyclic_of_irreducible_power_action _ h.irreducible hp)

private theorem cyclic_of_irreducible_power_involution_action
    {S V : Type*} [Group S] [Group V] [IsMulCommutative V]
    (f : S →* MulAut V) (g : MulAut V) (hg : g ^ 2 = 1)
    (hirr : ∀ A : Subgroup V,
      (∀ s : S, ∀ a ∈ A, f s a ∈ A) → A = ⊥ ∨ A = ⊤)
    (hpower : ∀ s v, f s v ∈ zpowers v ∨ f s v ∈ zpowers (g v)) :
    IsCyclic V := by
  let C := g.toMonoidHom.eqLocus (MonoidHom.id V)
  have hC : ∀ s : S, ∀ a ∈ C, f s a ∈ C := by
    intro s a ha
    rcases hpower s a with hp | hp
    · exact (zpowers_le.mpr ha) hp
    · have hga : g a = a := ha
      rw [hga] at hp
      exact (zpowers_le.mpr ha) hp
  have hsign : (∀ v, g v = v) ∨ (∀ v, g v = v⁻¹) := by
    rcases hirr C hC with hb | ht
    · right
      intro v
      have hv : g v * v ∈ C := by
        change g (g v * v) = g v * v
        have hh := DFunLike.congr_fun hg v
        change g (g v) = v at hh
        rw [map_mul, hh, mul_comm]
      exact mul_eq_one_iff_eq_inv.mp (Subgroup.mem_bot.mp (hb ▸ hv))
    · exact Or.inl (fun v => show v ∈ C from ht.symm ▸ mem_top v)
  apply cyclic_of_irreducible_power_action f hirr
  intro s v
  rcases hpower s v with hp | hp
  · exact hp
  · rcases hsign with he | he
    · simpa only [he] using hp
    · rw [he] at hp
      exact (zpowers_le.mpr ((zpowers v).inv_mem (mem_zpowers v))) hp

/-- Adding a single graph involution to power actions still cannot act
irreducibly on this noncyclic Frattini quotient. -/
theorem not_power_involution_action [Finite G] {p : ℕ} {T X P H : Subgroup G}
    (h : LocalInput p T X P H) (g : MulAut (P ⧸ frattini P)) (hg : g ^ 2 = 1) :
    ¬ ∀ s v, frattiniConjugationAction (T ⊓ normalizer P) P inf_le_right s v ∈
        zpowers v ∨
      frattiniConjugationAction (T ⊓ normalizer P) P inf_le_right s v ∈
        zpowers (g v) := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  let _ : Fact (IsPGroup p P) := ⟨h.odd_complement.isPGroup⟩
  let _ : IsElementaryAbelian p (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  intro hp
  exact OddInvolutionFrattini.noncyclic_frattini_quotient h.complement_not_cyclic
    (cyclic_of_irreducible_power_involution_action _ g hg h.irreducible hp)

/-- The actual map to the simple central quotient of the component quotient. -/
def componentSimpleMap {P L : Subgroup G} (hPL : P ≤ L) :
    P →* XiQuotient L ⧸ center (XiQuotient L) :=
  (QuotientGroup.mk' (center (XiQuotient L))).comp (componentMap hPL)

/-- The multiplier input needed to retain the odd complement is precisely
coprimality of its prime with the center of the component quotient. -/
theorem componentSimpleMap_injective [Finite G] {p : ℕ} [Fact p.Prime]
    {P L : Subgroup G} (hP : IsPGroup p P) (ho : Odd p) (hPL : P ≤ L)
    (hc : Nat.Coprime p (Nat.card (center (XiQuotient L)))) :
    Function.Injective (componentSimpleMap hPL) := by
  have hi := componentMap_injective hP ho hPL
  have hr : IsPGroup p (componentMap hPL).range :=
    hP.of_surjective (componentMap hPL).rangeRestrict (componentMap hPL).rangeRestrict_surjective
  have hd : Disjoint (componentMap hPL).range (center (XiQuotient L)) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := hr.exists_card_eq
    rw [hn]
    exact hc.pow_left n
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hz : componentMap hPL a ∈ center (XiQuotient L) :=
    (QuotientGroup.eq_one_iff _).mp ha
  exact hi ((hd.le_bot ⟨⟨a, rfl⟩, hz⟩).trans (map_one _).symm)

/-- The original elementary/extraspecial group survives as an actual subgroup
of the simple central quotient, once the stated central coprimality is proved. -/
theorem component_simple_image_odd_complement [Finite G] {p : ℕ}
    {T X P H L : Subgroup G} (h : LocalInput p T X P H) (hPL : P ≤ L)
    (hc : Nat.Coprime p (Nat.card (center (XiQuotient L)))) :
    XiOddQuotient p (componentSimpleMap hPL).range := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  let e : P ≃* (componentSimpleMap hPL).range :=
    MulEquiv.ofBijective (componentSimpleMap hPL).rangeRestrict
      ⟨fun _ _ he => componentSimpleMap_injective h.odd_complement.isPGroup h.odd hPL hc
        (congrArg Subtype.val he), (componentSimpleMap hPL).rangeRestrict_surjective⟩
  exact h.odd_complement.of_mulEquiv e

theorem component_simple_image_not_cyclic [Finite G] {p : ℕ}
    {T X P H L : Subgroup G} (h : LocalInput p T X P H) (hPL : P ≤ L)
    (hc : Nat.Coprime p (Nat.card (center (XiQuotient L)))) :
    ¬ IsCyclic (componentSimpleMap hPL).range := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  exact (component_simple_image_odd_complement h hPL hc).not_isCyclic


/-- A cyclic quotient action controls the actual automizer once its kernel
centralizes P. The Borel argument must establish this kernel condition. -/
theorem automizer_cyclic_of_cyclic_representation {T P : Subgroup G} {C : Type*} [Group C] [IsCyclic C]
    (f : (T ⊓ normalizer P : Subgroup G) →* C)
    (hker : ∀ s, f s = 1 → (s : G) ∈ centralizer (P : Set G)) :
    IsCyclic (automizer T P) := by
  let S := T ⊓ normalizer P
  let a : S →* MulAut P := P.normalizerMonoidHom.comp (inclusion inf_le_right)
  have hk : f.ker ≤ a.rangeRestrict.ker := by
    intro s hs
    apply Subtype.ext
    change a s = 1
    have hn : (inclusion (show S ≤ normalizer P from inf_le_right)) s ∈
        P.normalizerMonoidHom.ker := by
      rw [normalizerMonoidHom_ker]
      exact hker s hs
    exact hn
  let g := QuotientGroup.lift f.ker a.rangeRestrict hk
  let _ : IsCyclic (S ⧸ f.ker) := isCyclic_of_injective
    (QuotientGroup.kerLift f) (QuotientGroup.kerLift_injective f)
  exact isCyclic_of_surjective g
    (QuotientGroup.lift_surjective_of_surjective f.ker a.rangeRestrict
      a.rangeRestrict_surjective hk)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge
