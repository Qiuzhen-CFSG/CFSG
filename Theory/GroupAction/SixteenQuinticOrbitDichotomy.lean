module
public import Theory.GroupAction.LargeOrbits
public import Theory.GroupAction.FiveActionMinimalOrder
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Quintic orbit dichotomy on a group of order sixteen

If every nonidentity orbit has size divisible by five, the action is
transitive on the fifteen nonidentity elements or has an orbit of size five.
Indeed, without a five-orbit every orbit has at least ten elements, and two
such orbits cannot be disjoint. For an actual automorphism homomorphism,
five dividing the image order supplies the divisibility: an order-five
subgroup of the image acts without nonidentity fixed points.

No elementary structure, chosen module or simple-group classification is
needed. This finite-action step applies to the actual quotient of order
sixteen in the original alternating-five two-core analysis.
-/

public section
namespace Theory.GroupAction
open MulAction Subgroup

/-- Fifteen nonidentity points with quintic orbit sizes form one orbit,
unless an actual orbit has five elements. -/
theorem transitive_nonidentity_or_orbit_five_of_sixteen
    {M V : Type*} [Group M] [Group V] [Finite V] [MulDistribMulAction M V]
    (hV : Nat.card V = 16)
    (hdiv : ∀ v : V, v ≠ 1 → 5 ∣ (orbit M v).ncard) :
    (∀ x y : V, x ≠ 1 → y ≠ 1 → ∃ g : M, g • x = y) ∨
      ∃ x : V, x ≠ 1 ∧ (orbit M x).ncard = 5 := by
  classical
  by_cases hfive : ∃ x : V, x ≠ 1 ∧ (orbit M x).ncard = 5
  · exact Or.inr hfive
  left
  have hc : (({1} : Set V)ᶜ).ncard = 15 := by
    rw [Set.ncard_compl,hV,Set.ncard_singleton]
  apply transitive_of_large_orbits (({1} : Set V)ᶜ)
  · intro g x hx he
    apply hx
    have hh := congrArg (fun z : V => g⁻¹ • z) he
    simpa only [inv_smul_smul,smul_one,Set.mem_singleton_iff] using hh
  · intro x hx
    have hpos : 0 < (orbit M x).ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨x,mem_orbit_self x⟩
    have hd := hdiv x hx
    have hn : (orbit M x).ncard ≠ 5 := fun hh => hfive ⟨x,hx,hh⟩
    rw [hc]
    omega

private theorem orbit_five_dvd_of_faithful_image
    {M V : Type*} [Group M] [Finite M] [Group V] [Finite V]
    [MulDistribMulAction M V] [FaithfulSMul M V]
    (hM : 5 ∣ Nat.card M) (hV : Nat.card V = 16)
    (x : V) (hx : x ≠ 1) : 5 ∣ (orbit M x).ncard := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := M) 5 hM
  let B := zpowers a
  have hB : Nat.card B = 5 := (Nat.card_zpowers a).trans ha
  have hnot : FixedPoints.subgroup B V ≠ ⊤ := by
    intro htop
    have he : a = 1 := by
      apply eq_of_smul_eq_smul (α := V)
      intro v
      have hv : v ∈ FixedPoints.subgroup B V := htop ▸ mem_top v
      simpa only [Subgroup.smul_def,one_smul] using hv ⟨a,mem_zpowers a⟩
    simp [he] at ha
  have hfixed := fixed_eq_bot_of_five_action_card_sixteen hB hV hnot
  let : MulAction B (orbit M x) := MulAction.compHom (orbit M x) B.subtype
  have hempty : fixedPoints B (orbit M x) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hyV : (y:V) ∈ FixedPoints.subgroup B V := fun b => congrArg Subtype.val (hy b)
    have hyone : (y:V) = 1 := hfixed.le hyV
    obtain ⟨g,hg⟩ := y.property
    apply hx
    have hh := congrArg (fun z : V => g⁻¹ • z) (hg.trans hyone)
    simpa only [inv_smul_smul,smul_one] using hh
  have hp : IsPGroup 5 B := IsPGroup.of_card (n := 1) (by simpa using hB)
  have hm := hp.card_modEq_card_fixedPoints (orbit M x)
  have hz : Nat.card (fixedPoints B (orbit M x)) = 0 := by
    rw [hempty]
    exact Nat.card_of_isEmpty
  rw [hz] at hm
  exact Nat.modEq_zero_iff_dvd.mp hm

/-- Five in the image of the supplied automorphism homomorphism gives the
orbit dichotomy for that same action, with no faithfulness assumption on M. -/
theorem transitive_nonidentity_or_orbit_five_of_image_five
    {M V : Type*} [Group M] [Group V] [Finite V]
    (ρ : M →* MulAut V) (hM : 5 ∣ Nat.card ρ.range) (hV : Nat.card V = 16) :
    (∀ x y : V, x ≠ 1 → y ≠ 1 → ∃ g : M, ρ g x = y) ∨
      ∃ x : V, x ≠ 1 ∧ (Set.range (fun g : M => ρ g x)).ncard = 5 := by
  have hdiv := orbit_five_dvd_of_faithful_image hM hV
  rcases transitive_nonidentity_or_orbit_five_of_sixteen hV hdiv with ht | hf
  · left
    intro x y hx hy
    obtain ⟨g,hg⟩ := ht x y hx hy
    obtain ⟨m,hm⟩ := g.property
    exact ⟨m,by rw [hm]; exact hg⟩
  · right
    obtain ⟨x,hx,hcard⟩ := hf
    refine ⟨x,hx,?_⟩
    have he : Set.range (fun g : M => ρ g x) = orbit ρ.range x := by
      ext y
      constructor
      · rintro ⟨g,rfl⟩
        exact ⟨ρ.rangeRestrict g,rfl⟩
      · rintro ⟨g,rfl⟩
        obtain ⟨m,hm⟩ := g.property
        exact ⟨m,congrArg (fun a : MulAut V => a x) hm⟩
    rwa [he]

end Theory.GroupAction
