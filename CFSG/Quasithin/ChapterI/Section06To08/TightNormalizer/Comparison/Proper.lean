module

public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Basic

/-!
# The proper-normalizer branch of the Sylow comparison

For `S₁ < S₀`, the normalizer condition inside the finite two-group `S`
produces a distinct conjugate `T` of `R` inside `N_S(R)`. I.7.4 makes
`R` and `T` disjoint and commuting. Projection along the multiplication
isomorphism `S₁ × R ≃* N_S(R)` embeds `T` in `S₁`, proving the order
inequality. Equal orders upgrade this embedding to an actual isomorphism.

The opposite projection embeds `T` in `R`: conjugation by `S` preserves
`Kᵍ`, so `T` remains disjoint from `S₁`. Since `|T| = |R|`, this projection
is onto. Both `T` and `S₁` centralize `R`, so `R` is abelian. This proves
I.7.7(4) without requiring the later symmetric order comparison.
The isomorphism result here remains explicitly conditional on that comparison.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, I.7.7(2--4), printed p.427 (PDF p.438).
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem projection_injective {A B T N : Subgroup G}
    (hTN : T ≤ N) (e : A × B ≃* N)
    (he : ∀ a b, (e (a, b) : G) = (a : G) * (b : G))
    (hd : Disjoint T B) :
    Function.Injective ((MonoidHom.fst A B).comp
      (e.symm.toMonoidHom.comp (inclusion hTN))) := by
  apply (injective_iff_map_eq_one _).mpr
  intro t ht
  let z := e.symm (inclusion hTN t)
  have hz : z.1 = 1 := ht
  have htz : (t : G) = (z.2 : G) := by
    have hh := he z.1 z.2
    rw [show e (z.1, z.2) = inclusion hTN t from e.apply_symm_apply _] at hh
    simpa [hz] using hh
  apply Subtype.ext
  exact hd.le_bot ⟨t.property, htz ▸ z.2.property⟩

namespace TightNormalizerSetup
variable {K : Subgroup G} {g : G} {R S : Subgroup G} (h : TightNormalizerSetup K g R S)
include h

/-- The first normalizer factor lies in the opposite tightly embedded normalizer. -/
theorem factor_le_opposite :
    (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) ≤
      conjSubgroup K g ⊓ normalizer (K : Set G) :=
  le_inf (inf_le_left.trans inf_le_right)
    (inf_le_right.trans (h.hK.normalizer_le h.hRp h.hRne
      (h.hRle.trans inf_le_left)))

/-- Normalizer growth supplies a distinct conjugate inside `N_S(R)`. -/
theorem proper_exists_conjugate
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g) :
    ∃ x ∈ S, conjSubgroup R x ≠ R ∧
      conjSubgroup R x ≤ S ⊓ normalizer (R : Set G) := by
  let A := R.subgroupOf S
  let N := normalizer (A : Set S)
  have hn : N ≠ ⊤ := by
    intro hn
    apply hp.ne
    apply inf_eq_left.mpr
    intro x hx
    have hxN : (⟨x, hx.1⟩ : S) ∈ N := hn ▸ mem_top _
    dsimp [N, A] at hxN
    rw [← subgroupOf_normalizer_eq h.hRS] at hxN
    exact hxN
  let : Group.IsNilpotent S := h.hSp.isNilpotent
  obtain ⟨x, hxN, hx⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent N (lt_top_iff_ne_top.mpr hn))
  refine ⟨x, x.property, ?_, ?_⟩
  · intro he
    apply hx
    dsimp [N, A]
    rw [← subgroupOf_normalizer_eq h.hRS]
    exact mem_normalizer_iff_map_conj_eq.mpr he
  · rintro _ ⟨r, hr, rfl⟩
    have hrS := h.hRS hr
    have hrN : (⟨r, hrS⟩ : S) ∈ N := A.le_normalizer hr
    have htN := (mem_normalizer_iff.mp hxN ⟨r, hrS⟩).mp hrN
    refine ⟨S.mul_mem (S.mul_mem x.property hrS) (S.inv_mem x.property), ?_⟩
    dsimp [N, A] at htN
    rw [← subgroupOf_normalizer_eq h.hRS] at htN
    exact htN
/-- The conjugate supplied by normalizer growth is disjoint from the other factor. -/
theorem conjugate_disjoint_intersection {x : G} (hx : x ∈ S) :
    Disjoint (conjSubgroup R x) (S ⊓ conjSubgroup K g) := by
  apply disjoint_iff.mpr
  apply eq_bot_iff.mpr
  intro t ht
  have htR : x⁻¹ * t * x ∈ R := mem_conjSubgroup_iff.mp ht.1
  have hxn := h.overgroup_normalizes (h.hSle hx)
  have htK : x⁻¹ * t * x ∈ conjSubgroup K g := by
    simpa only [inv_inv] using (mem_normalizer_iff.mp ((normalizer (conjSubgroup K g : Set G)).inv_mem hxn) t).mp ht.2.2
  have hz : x⁻¹ * t * x = 1 := h.disjoint_conjugate.le_bot ⟨htR, htK⟩
  have he := congrArg (fun y : G => x * y * x⁻¹) hz
  simpa [mul_assoc] using he

/-- The order inequality in the proper-normalizer branch of I.7.7. -/
theorem card_le_of_proper
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g) :
    Nat.card R ≤ Nat.card ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) := by
  obtain ⟨x, hx, hne, hT⟩ := h.proper_exists_conjugate hp
  obtain ⟨hd, _⟩ := lemma_I_7_4_commuting h.pgroupSetup (h.hSle hx) hne hT
  obtain ⟨_, _, e, he⟩ := h.directProduct
  have hi := projection_injective hT e he hd.symm
  have hc := Nat.card_le_card_of_injective _ hi
  rwa [card_conjSubgroup] at hc

/-- Equal orders turn the first-factor projection into the required isomorphism. -/
theorem equiv_of_proper_of_card_eq
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g)
    (hc : Nat.card ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) = Nat.card R) :
    Nonempty (↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R) := by
  obtain ⟨x, hx, hne, hT⟩ := h.proper_exists_conjugate hp
  obtain ⟨hd, _⟩ := lemma_I_7_4_commuting h.pgroupSetup (h.hSle hx) hne hT
  obtain ⟨_, _, e, he⟩ := h.directProduct
  have hi := projection_injective hT e he hd.symm
  have hb := hi.bijective_of_nat_card_le (by simpa only [card_conjSubgroup] using hc.le)
  exact ⟨(MulEquiv.ofBijective _ hb).symm.trans
    (R.equivMapOfInjective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective).symm⟩

/-- I.7.7(4), using projection onto the second direct factor. -/
theorem commutative_of_proper
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g) :
    IsMulCommutative R := by
  let S1 := (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)
  obtain ⟨x, hx, hne, hT⟩ := h.proper_exists_conjugate hp
  obtain ⟨_, hRT⟩ := lemma_I_7_4_commuting h.pgroupSetup (h.hSle hx) hne hT
  obtain ⟨_, _, e, he⟩ := h.directProduct
  have hS1R : S1 ≤ centralizer (R : Set G) := by
    change (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) ≤ _
    rw [h.normalizer_eq_centralizer]
    exact inf_le_right
  let e' : R × S1 ≃* ↥(S ⊓ normalizer (R : Set G)) := MulEquiv.prodComm.trans e
  have he' : ∀ r s, (e' (r, s) : G) = (r : G) * (s : G) := by
    intro r s
    exact (he s r).trans (hS1R s.property r r.property).symm
  have hd := (h.conjugate_disjoint_intersection hx).mono_right
    (inf_le_left : S1 ≤ S ⊓ conjSubgroup K g)
  have hi := projection_injective hT e' he' hd
  have hb := hi.bijective_of_nat_card_le (by rw [card_conjSubgroup])
  apply IsMulCommutative.of_comm
  intro a b
  obtain ⟨t, ht⟩ := hb.surjective a
  let z := e'.symm (inclusion hT t)
  have hz : z.1 = a := ht
  have htz : (t : G) = (a : G) * (z.2 : G) := by
    have hh := he' z.1 z.2
    rw [show e' (z.1, z.2) = inclusion hT t from e'.apply_symm_apply _] at hh
    simpa [hz] using hh
  have htb := hRT b.property t t.property
  have hsb := hS1R z.2.property b b.property
  apply Subtype.ext
  change (a : G) * (b : G) = (b : G) * (a : G)
  apply mul_right_cancel (b := (z.2 : G))
  calc
    (a : G) * b * (z.2 : G) = (a : G) * ((z.2 : G) * b) := by rw [mul_assoc, hsb]
    _ = (t : G) * b := by rw [← mul_assoc, ← htz]
    _ = (b : G) * t := htb
    _ = (b : G) * a * (z.2 : G) := by rw [htz, mul_assoc]

end TightNormalizerSetup
end CFSG.Quasithin.ChapterI.Section06To08
