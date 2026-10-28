module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterlessCountingSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.SmallFieldSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.TerminalKernelSource
/-!
# The original centerless transfer consumer

Sylow conjugacy transports the actual outside fixed group into C_T(s).
The full-center row is excluded directly; the other row forces degree two
by the fixed-center alignment and elementary count, then the original
quaternion obstruction excludes it. Transfer closes the centerless branch.

The only two retained premises are the literal fixed-Sylow action kernels;
the independently proved field kernels supply them in FixedSylowKernelSource.
Source: Aschbacher–Smith, the end of the single linear block proof, p.539.
-/
public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open Stellmacher
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_centerless_field_not_conj_of_kernels
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (s : T) (hs : (s:G)∈(d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (hs2 : orderOf s=2) (hsR : (s:G)∉elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (hkernel :
      let R := elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
      let Zs := (R⊓centralizer (R:Set G))⊓centralizer ({(s:G)}:Set G)
      let Rs := R⊓centralizer ({(s:G)}:Set G)
      ∀E∈elementaryAbelianMaxSubgroups Rs,∀a∈(T:Subgroup G)⊓centralizer ({(s:G)}:Set G),
        a∈normalizer (E:Set G)→(∀u∈E,a*u*a⁻¹*u⁻¹∈Zs)→a∈Rs⊔zpowers (s:G))
    (hindex :
      let R := elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
      let Zs := (R⊓centralizer (R:Set G))⊓centralizer ({(s:G)}:Set G)
      let Rs := R⊓centralizer ({(s:G)}:Set G)
      (Rs⊔zpowers (s:G)).relIndex
        (((T:Subgroup G)⊓centralizer ({(s:G)}:Set G))⊓centralizer (Zs:Set G))≤2)
    (i : G) (hiT : i∈T) (hiS : i∉(d.S:Subgroup d.H).map d.H.subtype)
    (hi2 : orderOf i=2) : ¬IsConj i (s:G) := by
  let S := (d.S:Subgroup d.H).map d.H.subtype
  let R := elementaryAbelianMaxJ S
  let I := R⊓centralizer ({i}:Set G)
  let Ts := (T:Subgroup G)⊓centralizer ({(s:G)}:Set G)
  intro his
  by_cases hiZ : i∈centralizer (distinguishedZ d:Set G)
  · exact source_centerless_field_not_conj_to_full_center d hG T hST hsingle hL hM hTM hu c hZ s hs hs2 hsR i
      (fun z hz=>mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hiZ) z hz)) his
  have hRT : R≤(T:Subgroup G) := (sSup_le fun _ h=>h.1).trans hST.le
  obtain ⟨hTsTwo,hTsC,hmax⟩ := Chapter1.isSylowIn_iff.mp
    (source_centerless_field_centralizer_sylow d hG T hST hsingle hL hM hTM hu c hZ s hs hs2 hsR)
  obtain ⟨g,hgi,hgI⟩ := exists_conj_into_saturated_centralizer (s:G) i Ts I hTsTwo
    (T.isPGroup'.to_le (inf_le_left.trans hRT)) hTsC inf_le_right hmax his
  have hn := source_centerless_conjugacy_forces_small_field_of_kernels d hG T hST hsingle hL hM hTM hu c hZ s hs hs2 hsR
    i hiT hiS (by simpa only [hi2] using pow_orderOf_eq_one i) hiZ g hgi hgI hkernel hindex
  subst n
  exact source_centerless_small_field_not_conj d hG T hST hsingle hL hM hTM hu c hZ s hs hs2 hsR i hiT hiS hi2
    (by
      intro h
      apply hiZ
      rw [distinguishedZ_of_centerless d hZ]
      exact h) his

theorem source_centerless_false_of_kernels
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (s : T) (hs : (s:G)∈(d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (hs2 : orderOf s=2) (hsR : (s:G)∉elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (hkernel :
      let R := elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
      let Zs := (R⊓centralizer (R:Set G))⊓centralizer ({(s:G)}:Set G)
      let Rs := R⊓centralizer ({(s:G)}:Set G)
      ∀E∈elementaryAbelianMaxSubgroups Rs,∀a∈(T:Subgroup G)⊓centralizer ({(s:G)}:Set G),
        a∈normalizer (E:Set G)→(∀u∈E,a*u*a⁻¹*u⁻¹∈Zs)→a∈Rs⊔zpowers (s:G))
    (hindex :
      let R := elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
      let Zs := (R⊓centralizer (R:Set G))⊓centralizer ({(s:G)}:Set G)
      let Rs := R⊓centralizer ({(s:G)}:Set G)
      (Rs⊔zpowers (s:G)).relIndex
        (((T:Subgroup G)⊓centralizer ({(s:G)}:Set G))⊓centralizer (Zs:Set G))≤2) : False := by
  have hclosed := c.centerless_involution_fusion_closed d hG T hST hsingle hL hM hTM hu hZ
  apply source_false_of_centerless_fusion d hG T hST hsingle hL hM hTM hu c s hs2 hsR hclosed hZ
  intro t ht
  by_contra htS
  have ht2 : orderOf (t:G)=2 := by
    obtain ⟨a,ha⟩ := isConj_iff.mp ht
    exact ha ▸ ((MulAut.conj a).orderOf_eq (s:G)).trans ((orderOf_coe s).trans hs2)
  exact source_centerless_field_not_conj_of_kernels d hG T hST hsingle hL hM hTM hu c hZ s hs hs2 hsR
    hkernel hindex t t.property htS ht2 ht.symm
end CFSG.Quasithin.Chapter2.LinearShadows.Single
