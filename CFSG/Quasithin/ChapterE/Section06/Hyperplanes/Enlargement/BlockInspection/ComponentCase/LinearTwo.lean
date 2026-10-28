module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.Reduction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Models
public import Theory.SpecificGroups.Alternating.SmallInvolutionCentralizers

/-!
# The PSL₂(4) exclusion in the proper block enlargement

The actual component action fixes a Sylow four-group pointwise. Transport
to A₅ makes every such automorphism inner, by an element of that four-group.
Since C_V(X) has corank two, U contains an element acting nontrivially on X.
Its inner representative is an involution, whose A₅ centralizer is a two-group.
The embedded small block centralizes this involution, contradicting its
quotient of order divisible by three.

The only finite computation says that an A₅ element whose fourth power is
one has square one; Lean's kernel checks that certificate. All automorphism,
Sylow and centralizer transports use actual multiplicative equivalences.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed p.254 (PDF p.265), inspecting the PSL₂(4) case of E.6.8.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase
open ComponentBalance Components
variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

private theorem four_power_five (z : alternatingGroup (Fin 5)) (hz : z ^ 4 = 1) :
    z ^ 2 = 1 := by
  revert z
  decide +kernel

/-- A nontrivial Sylow-fixing action on PSL₂(4) has a two-group fixed centralizer,
which cannot contain an actual alternating small block. -/
theorem component_not_linearTwo [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    {U A L X : Subgroup G} (hUh : IsHyperplane V U)
    (hL : SmallBlock U L) (hA : A ∈ obstructionFamily M V)
    (hc : subgroupCorank V A = 2) (hX : CentralizerComponent A X)
    (hLX : L ≤ X) (hfixed : V ⊓ centralizer (X : Set G) = A)
    (hm : ClassicalGroup.IsPSL X 2 4) : False := by
  have hnUA : ¬ U ≤ A := by
    intro hh
    have := subgroupCorank_antitone (V := V) hh
    rw [hc, hUh.2] at this
    omega
  obtain ⟨u, hu, huA⟩ := Set.not_subset.mp hnUA
  have huV := hUh.1 hu
  have huC : u ∉ centralizer (X : Set G) := by
    intro hh
    exact huA (hfixed ▸ (show u ∈ V ⊓ centralizer (X : Set G) from ⟨huV, hh⟩))
  obtain ⟨hVN, S, _, hfix⟩ := component_sylow_action h hA hX rfl
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨e4⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let eA := e.trans e4
  let β := X.normalizerMonoidHom ⟨u, hVN huV⟩
  obtain ⟨z, hz, hβz⟩ := Theory.PSL2.SylowFixedQuotients.sylow_fixed_inner_of_equiv_five
    eA S β (by
      intro s hs
      apply Subtype.ext
      exact hfix u huV ⟨s, hs⟩)
  have hz1 : z ≠ 1 := by
    intro hz1
    apply huC
    apply mem_centralizer_iff.mpr
    intro x hx
    have hh := congrArg (fun a : MulAut X => (a ⟨x, hx⟩ : G)) hβz
    change u * x * u⁻¹ = (z : G) * x * (z : G)⁻¹ at hh
    rw [hz1] at hh
    simp only [coe_one, one_mul, inv_one, mul_one] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hza4 : (eA z) ^ 4 = 1 := by
    have hh : (⟨z, hz⟩ : ↥(S : Subgroup X)) ^ Nat.card ↥(S : Subgroup X) = 1 := pow_card_eq_one'
    have hcard : Nat.card S = 4 :=
      Theory.PSL2.SylowFixedQuotients.sylow_card_of_equiv_five eA S
    rw [hcard] at hh
    have hz4 : z ^ 4 = 1 := congrArg (fun x : S => x.val) hh
    simpa only [map_pow, map_one] using congrArg eA hz4
  have hza : orderOf (eA z) = 2 := orderOf_eq_prime (four_power_five _ hza4) (by
    intro he
    exact hz1 (eA.injective (he.trans (map_one eA).symm)))
  have hcent := alternatingGroup.isPGroup_centralizer_involution_of_degree_le_six
    (by decide : 5 ≤ 6) (eA z) hza
  have hcomm (l : L) : Commute (eA z) (eA ⟨l, hLX l.property⟩) := by
    have hh := congrArg (fun a : MulAut X => (a ⟨l, hLX l.property⟩ : G)) hβz
    have huc : u * (l : G) = (l : G) * u :=
      mem_centralizer_iff.mp (hL.1 l.property) u hu
    change u * (l : G) * u⁻¹ = (z : G) * (l : G) * (z : G)⁻¹ at hh
    rw [huc, mul_inv_cancel_right] at hh
    have hh' : Commute z (⟨l, hLX l.property⟩ : X) := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mp hh.symm
    exact hh'.map eA.toMonoidHom
  let f : L →* centralizer ({eA z} : Set (alternatingGroup (Fin 5))) :=
    { toFun := fun l => ⟨eA ⟨l, hLX l.property⟩, mem_centralizer_singleton_iff.mpr (hcomm l).eq.symm⟩
      map_one' := Subtype.ext (map_one eA)
      map_mul' := fun x y => Subtype.ext (map_mul eA
        (⟨x, hLX x.property⟩ : X) (⟨y, hLX y.property⟩ : X)) }
  have hf : Function.Injective f := by
    intro x y hh
    apply Subtype.ext
    exact congrArg (fun a : X => (a : G)) (eA.injective (congrArg Subtype.val hh))
  have hp : IsPGroup 2 L := hcent.of_injective f hf
  have h3 : 3 ∣ Nat.card L := hL.2.2.elim
    (fun hh => three_dvd_card_alternating_block L hh (Or.inl rfl))
    (fun hh => three_dvd_card_alternating_block L hh (Or.inr rfl))
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn] at h3
  exact (by decide : ¬ 3 ∣ 2) (Nat.Prime.dvd_of_dvd_pow (by decide) h3)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase
