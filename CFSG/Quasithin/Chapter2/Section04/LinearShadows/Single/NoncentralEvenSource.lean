module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.NoncentralFaithfulSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.NoncentralSylowModelSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.InvolutionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.InvolutionFusionSource
public import Theory.SpecificGroups.SymplecticFour.Sylow.QuotientActorsTransport

/-!
# The original noncentral even-field exclusion

The absorbed Thompson subgroup is a symplectic Sylow group over the original
field. The literal torus complement acts faithfully on its central quotient.
The intrinsic square-map calculation makes that two-group cyclic for fields
larger than four, contradicting the original involution-fusion consequence of
2.4.22. The final setup wrappers construct the 2.4.21 fusion input and retain
no component recognition, fixed-block or marked-action premise.

Source: Aschbacher–Smith 2.4.24(2), printed pp.538–539. This route proves the
needed contradiction directly instead of recognizing the larger component
in the intermediate source argument 2.4.23(5).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_noncentral_large_false
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0=d.block) {n:ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hu : ∀ N, IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M)
    (c : CyclicTorusSetup d T n)
    (hclosed : ∀ r t : T, orderOf r=2 →
      (r:G)∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype) →
      IsConj (r:G) (t:G) →
      (t:G)∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype))
    (hZ : center (d.block.map d.H.subtype)≠⊥) (hn : 2<n) : False := by
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)
  let A := (normalizer (c.hall:Set G)).subgroupOf (T:Subgroup G)
  obtain ⟨F,_,_,_,hF,⟨e⟩⟩ :=
    source_noncenterless_thompson_model d hG T hST hsingle hL hM hTM hu hZ
  obtain ⟨α,_,hfaithful⟩ :=
    source_torus_faithful_thompson_quotient d hG T hST hsingle hL hM hTM hu c hZ
  let : IsCyclic A := QuotientActors.isCyclic_of_faithful_centerQuotient
    hF hn e (T.isPGroup'.to_subgroup A) α hfaithful
  let := c.normal_in_sylow
  exact c.quotient_not_cyclic_of_fusion hG hclosed
    ((c.split_ambient.symm.QuotientMulEquiv).isCyclic.mpr inferInstance)

/-- The original even-half-field branch of 2.4.24(2), with its literal
marked field involution and earlier strong-closure source input. -/
theorem source_noncentral_even_false
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0=d.block) {n:ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hu : ∀ N, IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M)
    (c : CyclicTorusSetup d T n) (s:T)
    (_hs : (s:G)∈(d.S:Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (_hs2 : orderOf s=2)
    (_hsR : (s:G)∉Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype))
    (hclosed : ∀ r t : T, orderOf r=2 →
      (r:G)∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype) →
      IsConj (r:G) (t:G) →
      (t:G)∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype))
    (hZ : center (d.block.map d.H.subtype)≠⊥) (hn : 4∣n) : False := by
  apply source_noncentral_large_false d hG T hST hsingle hL hM hTM hu c hclosed hZ
  have hnpos := hL.1
  omega
/-- Original noncentral 2.4.24(2) for fields larger than four, with the
2.4.21 involution fusion input constructed from the source setup. -/
theorem source_noncentral_large_false_of_setup
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0=d.block) {n:ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hu : ∀ N, IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M)
    (c : CyclicTorusSetup d T n)
    (hZ : center (d.block.map d.H.subtype)≠⊥) (hn : 2<n) : False :=
  source_noncentral_large_false d hG T hST hsingle hL hM hTM hu c
    (CyclicTorusSetup.involution_fusion_closed d hG T hST hsingle hL hM hTM hu c) hZ hn

/-- The original even-half-field case, without a marked-involution or
strong-closure premise. These data are supplied by the original setup. -/
theorem source_noncentral_even_false_of_setup
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0=d.block) {n:ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hu : ∀ N, IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M)
    (c : CyclicTorusSetup d T n)
    (hZ : center (d.block.map d.H.subtype)≠⊥) (hn : 4∣n) : False := by
  apply source_noncentral_large_false_of_setup d hG T hST hsingle hL hM hTM hu c hZ
  have hnpos := hL.1
  omega
end CFSG.Quasithin.Chapter2.LinearShadows.Single
