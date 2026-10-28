module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.CyclicIntersection.Coordinates
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.SourceTheorems

/-!
# The cyclic-three component intersection in B.1.13

For H = ⟨K,T⟩ and |K| = 3, B.1.12 supplies the independent cyclic-three
coordinates and the literal quotient M/O₂(M). The normal global offender
subgroup contains M and normalizes L. If K does not lie in L, then K ∩ L
is trivial. An element of H ∩ L either fixes K, so its commutators with K
lie in that trivial intersection, or moves K to a distinct coordinate.
In the latter case, a quotient involution lifts to m ∈ M which inverts K
and fixes its moved conjugate. For k ∈ K and x ∈ H ∩ L, the double
commutator [m,[k,x]] equals k and belongs to L, again giving triviality.

This replaces the source's implicit representative choice by an explicit
commutator in L. All quotient kernels are the intrinsic two-core of M.
The result has exactly the local-intersection conclusion of the quasisimple
branch in `ComponentRecognition`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), B.1.13, printed p. 74 (PDF p. 85).
-/

public section

namespace CFSG.Quasithin.ChapterB.ComponentRecognition
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open ThreeConjugates
open scoped commutatorElement
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The entire local group M supplied by B.1.12 lies in the normal global
offender subgroup. Thus the source normalizer hypothesis applies to M. -/
theorem mixedSubgroup_le_offenderSubgroup (K T : Subgroup G)
    (hcomm : K = ⁅K, generatedBy {A | IsBestOffender ρ A} T⁆) :
    mixedSubgroup ρ K T ≤ offenderSubgroup ρ := by
  let := offenderSubgroup_normal ρ
  apply sup_le
  · exact iSup_le fun A => iSup_le fun hA =>
      le_iSup_of_le A (le_iSup_of_le ⟨hA.1, le_top⟩ le_rfl)
  · exact iSup_conjugates_le_of_le_normalizer K T _
      (le_offenderSubgroup_of_local_commutator ρ K T hcomm) le_normalizer_of_normal

/-- If m inverts k and fixes its x-conjugate, then the double commutator
[m,[k,x]] equals k, since k has exponent three. Both commutators belong
to L by the two normalizer hypotheses. No arbitrary quotient lift is
asserted to lie in L. -/
private theorem mem_of_separating_conjugation (K L : Subgroup G)
    (hKL : K ≤ normalizer (L : Set G)) {k x m : G}
    (hk : k ∈ K) (hx : x ∈ L) (hm : m ∈ normalizer (L : Set G))
    (hk3 : k ^ 3 = 1) (hinv : m * k * m⁻¹ = k⁻¹)
    (hfix : m * (x * k * x⁻¹) * m⁻¹ = x * k * x⁻¹) : k ∈ L := by
  let u := k * (x * k * x⁻¹)⁻¹
  have hu : u ∈ L := by
    have h' : ⁅k, x⁆ ∈ L :=
      le_normalizer_iff_commutator_le_right.mp hKL
        (commutator_mem_commutator hk hx)
    simpa [u, commutatorElement_def, mul_assoc] using h'
  have hv : m * u * m⁻¹ * u⁻¹ ∈ L :=
    L.mul_mem ((mem_normalizer_iff.mp hm u).mp hu) (L.inv_mem hu)
  have he : m * u * m⁻¹ * u⁻¹ = k⁻¹ * k⁻¹ := by
    calc
      m * u * m⁻¹ * u⁻¹ =
          (m * k * m⁻¹) * (m * (x * k * x⁻¹) * m⁻¹)⁻¹ *
            ((x * k * x⁻¹) * k⁻¹) := by dsimp [u]; group
      _ = k⁻¹ * k⁻¹ := by rw [hinv, hfix]; group
  have hkpow : k⁻¹ * k⁻¹ = k := by
    have := congrArg (fun z : G => k⁻¹ * z * k⁻¹) hk3
    simpa [pow_succ, mul_assoc] using this.symm
  rwa [he, hkpow] at hv

variable [Finite G] [FiniteDimensional (ZMod 2) V]

/-- The cyclic-three alternative in B.1.13, relative to the original local
overgroup. For a moved conjugate, a single-coordinate quotient involution
and its double commutator force containment. For a fixed conjugate, the
commutator already lies in K ∩ L, which is trivial unless K lies in L.

The algebra in fact applies to any L normalized by the offender subgroup;
the component hypotheses are retained for the B.1.13 interface. -/
theorem cyclic_local_dichotomy (K L : Subgroup G) (T : Sylow 2 G)
    (hρ : Function.Injective ρ) (hcard : Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal)
    (hcomm : K = ⁅K, generatedBy {A | IsBestOffender ρ A} (T : Subgroup G)⁆)
    (_hL : IsComponent G L) (_hLK : ⁅L, K⁆ = L)
    (hN : offenderSubgroup ρ ≤ normalizer (L : Set G)) :
    K ≤ L ∨ ⁅K, L ⊓ (K ⊔ (T : Subgroup G))⁆ = ⊥ := by
  classical
  by_cases hKL : K ≤ L
  · exact Or.inl hKL
  right
  obtain ⟨d⟩ := source_lemma_B_1_12 ρ hρ K T hcard hK hcomm
  have hMN := (mixedSubgroup_le_offenderSubgroup ρ K (T : Subgroup G) hcomm).trans hN
  have hKN := (le_offenderSubgroup_of_local_commutator ρ K (T : Subgroup G) hcomm).trans hN
  have htriv : ∀ z ∈ K, z ∈ L → z = 1 := by
    let : Fact (Nat.card K).Prime := ⟨hcard ▸ Nat.prime_three⟩
    rcases (L.subgroupOf K).eq_bot_or_eq_top_of_prime_card with hb | ht
    · intro z hzK hzL
      have h : (⟨z, hzK⟩ : K) ∈ L.subgroupOf K := hzL
      rw [hb] at h
      exact congrArg Subtype.val (mem_bot.mp h)
    · exact (hKL (subgroupOf_eq_top.mp ht)).elim
  let i : conjugateFamily K (T : Subgroup G) := ⟨K, ⟨1, by
      have he : (MulAut.conj ((1 : (T : Subgroup G)) : G)).toMonoidHom =
          MonoidHom.id G := by ext g; simp
      change K.map (MulAut.conj ((1 : (T : Subgroup G)) : G)).toMonoidHom = K
      rw [he, map_id]⟩⟩
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro k hk
  rw [mem_centralizer_iff]
  intro x hx
  let j : conjugateFamily K (T : Subgroup G) :=
    ⟨K.map (MulAut.conj x).toMonoidHom, d.conjugate_mem_family_of_mem_sup hcard hx.2⟩
  have hxk : x * k * x⁻¹ ∈ (j : Subgroup G) := mem_map_of_mem _ hk
  by_cases hji : j = i
  · have hxkK : x * k * x⁻¹ ∈ K := by simpa only [hji] using hxk
    have hzK : ⁅x, k⁆ ∈ K := K.mul_mem hxkK (K.inv_mem hk)
    have hzL : ⁅x, k⁆ ∈ L :=
      le_normalizer_iff_commutator_le_left.mp hKN (commutator_mem_commutator hx.1 hk)
    exact commutatorElement_eq_one_iff_mul_comm.mp (htriv _ hzK hzL)
  · obtain ⟨m, _, _, _, hmi, hmj⟩ := d.separating_involution_lift hK hcard i j (Ne.symm hji)
    have hk3 : k ^ 3 = 1 := congrArg Subtype.val
      (show (⟨k, hk⟩ : K) ^ 3 = 1 by rw [← hcard]; exact pow_card_eq_one')
    have hkL := mem_of_separating_conjugation K L hKN hk hx.1 (hMN m.property)
      hk3 (hmi k hk) (hmj _ hxk)
    rw [htriv k hk hkL, mul_one, one_mul]
end CFSG.Quasithin.ChapterB.ComponentRecognition
