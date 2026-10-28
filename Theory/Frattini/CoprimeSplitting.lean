module

public import Theory.Representation.CoprimeElementaryComplement
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Lifting an invariant Frattini decomposition

A nonzero proper invariant subspace of the Frattini quotient of a finite
normal p-subgroup admits a complement for any actor of order prime to p.
Its two full preimages are proper subgroups, normalized by that same actor,
and generate the original p-subgroup. Both preimages and the action are
formed using the actual subgroup embedding and quotient map.

This is the Maschke reduction used in Aschbacher–Smith, E.5.2,
printed p.243 (combined manuscript of 1 March 2004).
-/

namespace Subgroup
open scoped IsMulCommutative

/-- A reducible Frattini section yields two proper invariant subgroups
which together generate the normal p-subgroup. -/
public theorem exists_proper_invariant_frattini_cover {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (R S U : Subgroup G) [R.Normal] [U.Normal]
    (hR : IsPGroup p R) (hcop : Nat.Coprime p (Nat.card S))
    (hUR : U ≤ R) (hUzero : ¬ U ≤ (frattini R).map R.subtype)
    (hUfull : U ⊔ (frattini R).map R.subtype ≠ R) :
    ∃ B C : Subgroup G, B ≤ R ∧ C ≤ R ∧ B ≠ R ∧ C ≠ R ∧
      S ≤ normalizer B ∧ S ≤ normalizer C ∧ B ⊔ C = R := by
  let : Fact (IsPGroup p R) := ⟨hR⟩
  let V := R ⧸ frattini R
  let : IsElementaryAbelian p V := isElementaryAbelian_quotient_frattini
  let q := QuotientGroup.mk' (frattini R)
  let ρ : S →* MulAut V :=
    (quotientAut (frattini R)).comp (MulAut.conjNormal.comp S.subtype)
  let U₀ := (U.subgroupOf R).map q
  have hinv : ∀ s : S, ∀ x ∈ U₀, ρ s x ∈ U₀ := by
    rintro s x ⟨u, hu, rfl⟩
    refine ⟨MulAut.conjNormal (s : G) u, ?_, ?_⟩
    · exact (inferInstance : U.Normal).conj_mem u hu s
    · exact (quotientAut_apply_mk (frattini R) _ u).symm
  have hzero : U₀ ≠ ⊥ := by
    intro hz
    have hu : U.subgroupOf R ≤ frattini R := by
      simpa only [U₀, Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using hz
    exact hUzero (by
      rw [← map_subgroupOf_eq_of_le hUR]
      exact map_mono hu)
  have hfull : U₀ ≠ ⊤ := by
    intro ht
    have hc := congrArg (fun L : Subgroup V => (L.comap q).map R.subtype) ht
    apply hUfull
    simpa only [U₀, comap_map_eq, q, QuotientGroup.ker_mk', Subgroup.map_sup,
      map_subgroupOf_eq_of_le hUR, comap_top, ← MonoidHom.range_eq_map,
      range_subtype] using hc
  obtain ⟨W, hcompl, hW⟩ :=
    IsElementaryAbelian.exists_invariant_complement ρ hcop U₀ hinv
  have hWfull : W ≠ ⊤ := by
    intro ht
    apply hzero
    simpa only [ht, inf_top_eq] using hcompl.inf_eq_bot
  let lift (L : Subgroup V) := (L.comap q).map R.subtype
  have hlift_le (L : Subgroup V) : lift L ≤ R := map_subtype_le _
  have hlift_proper (L : Subgroup V) (hne : L ≠ ⊤) : lift L ≠ R := by
    intro heq
    apply hne
    have he : L.comap q = ⊤ := by
      apply map_injective R.subtype_injective
      simpa only [← MonoidHom.range_eq_map, range_subtype] using heq
    have hm := congrArg (Subgroup.map q) he
    rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) L,
      map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at hm
    exact hm
  have hlift_norm (L : Subgroup V) (hL : ∀ s : S, ∀ x ∈ L, ρ s x ∈ L) :
      S ≤ normalizer (lift L) := by
    rw [le_normalizer_iff]
    rintro s hs x ⟨r, hr, rfl⟩
    refine ⟨MulAut.conjNormal s r, ?_, rfl⟩
    change q (MulAut.conjNormal s r) ∈ L
    have he : ρ ⟨s,hs⟩ (q r) = q (MulAut.conjNormal s r) :=
      quotientAut_apply_mk (frattini R) _ r
    rw [← he]
    exact hL ⟨s,hs⟩ (q r) hr
  refine ⟨lift U₀, lift W, hlift_le _, hlift_le _, hlift_proper _ hfull,
    hlift_proper _ hWfull, hlift_norm _ hinv, hlift_norm _ hW, ?_⟩
  change (U₀.comap q).map R.subtype ⊔ (W.comap q).map R.subtype = R
  rw [← Subgroup.map_sup, comap_sup_eq q U₀ W (QuotientGroup.mk'_surjective _),
    hcompl.sup_eq_top, comap_top, ← MonoidHom.range_eq_map, range_subtype]

end Subgroup
