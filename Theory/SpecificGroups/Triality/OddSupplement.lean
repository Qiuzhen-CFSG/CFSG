module
public import Theory.SpecificGroups.Triality.SolvableSylowControl
public import Theory.SpecificGroups.Triality.StandardTwoRank.Derived
public import Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics.Placement.Bruhat
public import Theory.GroupTheory.SylowPairSolvableGeneration

/-!
# Odd solvable supplements to a normal genuine triality component

The graph-field D₄ carrier has a full positive Sylow subgroup, its actual
root Borel, and two maximal root parabolics with solvable intersection.
Bruhat factorization and normal generation enlarge any proper Sylow
overgroup to a proper Borel overgroup, proving exhaustive parabolic placement.
Sylow conjugacy transports this geometry to arbitrary markings. Combined
with the proved solvable Sylow control, it excludes generation by a proper
invariant nonsolvable subgroup and a solvable odd supplement when q > 2.

Source: Aschbacher--Smith 5.1.13 and 5.2.2, pp.636 and 648; GLS3
2.3.4--8 and 2.6.5--7 for the genuine graph-field Bruhat construction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Triality.Standard.OddSupplement
open Parabolics ConcreteBruhat
variable {G : Type*} [Group G] [Finite G]

private def sylowBruhat (n : ℕ) (hn : 0 < n) :
    SylowBruhatData (borel (binaryParameters n hn)) := by
  let P := binaryParameters n hn
  have hTU : torus P ≤ normalizer (unipotent P : Set (Carrier P)) :=
    (torus_le_borel P).trans (borel_le_normalizer_unipotent P rfl)
  refine {
    sylow := unipotentSylow P rfl
    cartan := torus P
    monomial := normalizerCandidate P rfl
    borel_eq := ?_
    cartan_normalizes := hTU
    monomial_normalizes := sup_le (torus P).le_normalizer
      (RelativeNormalizer.weylSubgroup_normalizes_torus P rfl)
    factorization := ?_
    normal_generates := ?_ }
  · apply le_antisymm
    · intro x hx
      rw [← SetLike.mem_coe, borel_eq_mul P rfl] at hx
      obtain ⟨u,hu,t,ht,rfl⟩ := hx
      exact (unipotent P ⊔ torus P).mul_mem (mem_sup_left hu) (mem_sup_right ht)
    · exact sup_le (unipotent_le_borel P) (torus_le_borel P)
  · intro g
    obtain ⟨w,hw⟩ := FixedDescent.exists_mem_cell n hn g
    obtain ⟨b₁,hb₁,b₂,hb₂,rfl⟩ := (mem_cell_iff P rfl w g).mp hw
    rw [← SetLike.mem_coe, borel_eq_mul P rfl] at hb₁ hb₂
    obtain ⟨u,hu,t,ht,rfl⟩ := hb₁
    obtain ⟨v,hv,s,hs,rfl⟩ := hb₂
    refine ⟨u,hu,t * weylRepresentative P rfl w * s,
      (normalizerCandidate P rfl).mul_mem
        ((normalizerCandidate P rfl).mul_mem (mem_sup_left ht)
          (RelativeNormalizer.weylRepresentative_mem_normalizer P rfl w))
        (mem_sup_left hs),s⁻¹ * v * s,?_,?_⟩
    · change s⁻¹ * v * s ∈ unipotent P
      simpa only [inv_inv] using
        (mem_normalizer_iff.mp (hTU ((torus P).inv_mem hs)) v).mp hv
    · group
  · have hu : 1 < Nat.card (unipotent P) := by
      rw [card_unipotent_binary P rfl]
      exact one_lt_pow₀ (by have := P.q_ge_two; omega) (by decide)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (normalClosure (unipotent P : Set (Carrier P))) inferInstance with hb | ht
    · have hbot : unipotent P = ⊥ := bot_unique (by
        intro x hx
        exact hb ▸ subset_normalClosure hx)
      simp [hbot] at hu
    · exact ht

/-- Every proper overgroup of the full positive Sylow lies in a root parabolic. -/
theorem le_parabolic (n : ℕ) (hn : 0 < n)
    (J : Subgroup (BinaryCarrier n hn))
    (hU : unipotent (binaryParameters n hn) ≤ J) (hJ : J ≠ ⊤) :
    ∃ a : Node, J ≤ parabolic (binaryParameters n hn) a := by
  obtain ⟨Q,hBQ,hJQ,hQ⟩ := (sylowBruhat n hn).exists_proper_borel_overgroup J hU hJ
  obtain ⟨a,ha⟩ := TwoRank.Derived.le_parabolic_of_borel_le n hn Q hBQ hQ
  exact ⟨a,hJQ.trans ha⟩

/-- Each of the two original full root parabolics is maximal. -/
theorem parabolic_isCoatom (n : ℕ) (hn : 0 < n) (a : Node) :
    IsCoatom (parabolic (binaryParameters n hn) a) := by
  let P := binaryParameters n hn
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨parabolic_ne_top_binary P rfl a,?_⟩
  intro J hJ hPJ
  obtain ⟨b,hb⟩ := TwoRank.Derived.le_parabolic_of_borel_le n hn J
    ((borel_le_parabolic P a).trans hPJ) hJ
  by_cases he : a = b
  · subst b
    exact hb
  · have ht : parabolic P a ⊔ parabolic P b = ⊤ := by
      cases a <;> cases b
      · exact (he rfl).elim
      · exact parabolic_sup_binary P rfl
      · rw [sup_comm]; exact parabolic_sup_binary P rfl
      · exact (he rfl).elim
    exact (parabolic_ne_top_binary P rfl b (top_le_iff.mp
      (ht ▸ sup_le (hPJ.trans hb) le_rfl))).elim

/-- Sylow conjugacy transports both maximal parabolics and their solvable overlap. -/
theorem two_sylow_overgroups_of_equiv (n : ℕ) (hn : 0 < n)
    (e : G ≃* BinaryCarrier n hn) (S : Sylow 2 G) :
    ∃ P Q : Subgroup G, IsCoatom P ∧ IsCoatom Q ∧
      (S : Subgroup G) ≤ P ∧ (S : Subgroup G) ≤ Q ∧
      Group.IsSolvable (P ⊓ Q : Subgroup G) ∧
      ∀ J : Subgroup G, (S : Subgroup G) ≤ J → J ≠ ⊤ → J ≤ P ∨ J ≤ Q := by
  let M := binaryParameters n hn
  obtain ⟨_,a,_,hS⟩ := Theory.GroupTheory.SolvableSylowControl.exists_aligned_equiv
    e S (unipotentSylow M rfl)
  change (S : Subgroup G).map a.toMonoidHom = unipotent M at hS
  let P := (parabolic M .arms).comap a.toMonoidHom
  let Q := (parabolic M .central).comap a.toMonoidHom
  have hUP : (S : Subgroup G) ≤ P := map_le_iff_le_comap.mp (by
    rw [hS]
    exact (unipotent_le_borel M).trans (borel_le_parabolic M .arms))
  have hUQ : (S : Subgroup G) ≤ Q := map_le_iff_le_comap.mp (by
    rw [hS]
    exact (unipotent_le_borel M).trans (borel_le_parabolic M .central))
  refine ⟨P,Q,isCoatom_comap_of_surjective a.surjective (parabolic_isCoatom n hn .arms),
    isCoatom_comap_of_surjective a.surjective (parabolic_isCoatom n hn .central),
    hUP,hUQ,?_,?_⟩
  · let : Group.IsSolvable (borel M) := TwoRank.Derived.borel_isSolvable n hn
    let f : (P ⊓ Q : Subgroup G) →* borel M :=
      (a.toMonoidHom.comp (P ⊓ Q).subtype).codRestrict (borel M)
        (fun x => (parabolic_inf_binary M rfl) ▸ x.property)
    exact Group.isSolvable_of_isSolvable_injective (f := f) (by
      intro x y hxy
      exact Subtype.ext (a.injective (congrArg Subtype.val hxy)))
  · intro J hSJ hJ
    have hj : J.map a.toMonoidHom ≠ ⊤ := by
      intro he
      apply hJ
      apply map_injective (f := a.toMonoidHom) a.injective
      rw [he,map_top_of_surjective _ a.surjective]
    obtain ⟨b,hb⟩ := le_parabolic n hn (J.map a.toMonoidHom)
      (hS ▸ map_mono hSJ) hj
    cases b with
    | arms => exact Or.inl (map_le_iff_le_comap.mp hb)
    | central => exact Or.inr (map_le_iff_le_comap.mp hb)

/-- A proper Sylow-invariant nonsolvable subgroup cannot generate an extension
of nonbinary genuine triality with a solvable odd supplement. -/
theorem no_odd_solvable_supplement (n : ℕ) (hn : 1 < n)
    (S : Sylow 2 G) (K R D : Subgroup G) [K.Normal]
    (e : K ≃* BinaryCarrier n (by omega)) (hRK : R < K) (hRns : ¬ Group.IsSolvable R)
    (hSR : (S : Subgroup G) ≤ normalizer (R : Set G))
    (ho : Odd (Nat.card D)) (hsol : Group.IsSolvable ((S : Subgroup G) ⊔ D : Subgroup G))
    (hgen : R ⊔ (S : Subgroup G) ⊔ D = ⊤) : False := by
  let : IsSimpleGroup K := e.isSimpleGroup
  apply no_solvable_odd_supplement_of_two_sylow_overgroups S K R D hRK hRns hSR ho hsol hgen
  · exact Theory.GroupTheory.SolvableSylowControl.of_equiv e
      (SolvableSylowControl.binary_control n hn)
  · exact two_sylow_overgroups_of_equiv n (by omega) e
end Triality.Standard.OddSupplement
