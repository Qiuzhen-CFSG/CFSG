module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.RadicalStabilizers.SylowImage
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.SymmetricFive
public import Theory.GroupAction.CoprimePrimePlane

/-!
# Coprime component stabilizers on the original radical plane

The component Frattini action maps onto the moved action over each original
element of L. Hence noncommutativity of C_L(u) on the moved module is also
detected on the radical plane. When this latter image has order prime to p,
the elementary-plane theorem proves irreducibility. Restriction of the
literal C_M(u) action then gives exactly RadicalCentralizerIrreducible.

The S₅ marking supplies its actual S₃ stabilizer and the local orbit bound.
Its prime-to-p Frattini-image order remains explicit here: establishing it
from the SL₂ cover is required before the source theorem is assembled by
the module-orbit owner. Nonabelianness alone is not used as an
irreducibility criterion.

Source: Aschbacher--Smith, 13.1.12(1--2), printed pp.872--873.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
open Chapter1 Chapter1.Section02 Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]

/-- Noncommutativity transfers on C_L(u) itself, before enlarging to C_M(u). -/
theorem component_centralizer_frattini_not_commutative
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : G)
    (hnc : ¬ IsMulCommutative
      (((centralizer ({u} : Set G)).subgroupOf L).map (componentAction L))) :
    ¬ IsMulCommutative (((centralizer ({u} : Set G)).subgroupOf L).map
      (xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer))) := by
  obtain ⟨f,_,hf⟩ := moved_action_factors_frattini h hmany hL hn ho hd
  let σ := xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer)
  intro hc
  apply hnc
  apply IsMulCommutative.of_comm
  intro a b
  obtain ⟨l,hl,hel⟩ := a.property
  obtain ⟨k,hk,hek⟩ := b.property
  let H := ((centralizer ({u} : Set G)).subgroupOf L).map σ
  have hh := congrArg Subtype.val ((isMulCommutative_iff.mp hc)
    (⟨σ l,⟨l,hl,rfl⟩⟩ : H) (⟨σ k,⟨k,hk,rfl⟩⟩ : H))
  have hr : σ.rangeRestrict l * σ.rangeRestrict k =
      σ.rangeRestrict k * σ.rangeRestrict l := Subtype.ext hh
  have he := congrArg (fun x => (f x : MulAut (normalizerMoved L))) hr
  simp only [map_mul,Subgroup.coe_mul] at he
  rw [hf l,hf k] at he
  apply Subtype.ext
  simpa only [MonoidHom.coe_rangeRestrict,Subgroup.coe_mul,hel,hek] using he

/-- The prime-to-p restriction is an explicit mathematical premise, to be
discharged by the actual SL₂ stabilizer model. -/
theorem radicalCentralizerIrreducible_of_coprime_component_image
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : G)
    (hnc : ¬ IsMulCommutative
      (((centralizer ({u} : Set G)).subgroupOf L).map (componentAction L)))
    (hcop : Nat.Coprime p (Nat.card
      (((centralizer ({u} : Set G)).subgroupOf L).map
        (xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer))))) :
    RadicalCentralizerIrreducible L p u := by
  obtain ⟨_,he,hc⟩ := radical_frattini_plane h.simpleQTKE hL.1.1 hn ho hd
  let := he
  intro A hA
  apply PrimePlaneAction.irreducible_of_coprime_noncommutative hc _ hcop
    (component_centralizer_frattini_not_commutative h hmany hL hn ho hd u hnc) A
  intro g a ha
  obtain ⟨l,hl,hel⟩ := g.property
  rw [← hel]
  exact hA ⟨l,L.le_normalizer l.property,hl⟩ a ha

namespace SymmetricFiveMarking

/-- The actual S₅ orbit calculation supplies the nonabelian image and the
index bound. Only its prime-to-p Frattini-image order remains to supply. -/
theorem centralizer_index_and_radical_irreducible_of_coprime
    {T : Sylow 2 G} {L : Subgroup G} (d : SymmetricFiveMarking T L)
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : normalizerMoved L) (hu : u ≠ 1)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)))
    (hcop : Nat.Coprime p (Nat.card
      (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
        (xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer))))) :
    (centralizer ({(u : G)} : Set G)).relIndex (T : Subgroup G) ≤ 2 ∧
      RadicalCentralizerIrreducible L p u := by
  obtain ⟨hi,hs⟩ := d.centralizer_orbit h hL hn u hu hlocal
  refine ⟨hi,?_⟩
  by_cases ht : (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G)
  · exact radicalCentralizerIrreducible_of_sylow_centralizes h.simpleQTKE hL.1.1 hn ho hd ht
  · exact radicalCentralizerIrreducible_of_coprime_component_image h hmany hL hn ho hd u
      (hs ht).2 hcop

end SymmetricFiveMarking
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
