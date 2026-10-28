module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.NoncenterlessFieldDerivedSource
public import Theory.GroupTheory.ElementaryClassClosure
/-!
# Nonabelian inside fixed groups in the full-cover branch

The distinguished center is a nontrivial elementary two-group normalized by
S, so an inside involution fixes a nonidentity element of that center. The
actual fixed-derived row places this element in the fixed group's commutator
subgroup, except at q=4 where its marked Δ commutator supplies the same
nontriviality directly. Thus the original C_R(s) is nonabelian in both cases.

Source: Aschbacher–Smith, Lemma 2.4.12(2), and its use in the odd branch of
Lemma 2.4.24(2), printed pp.532 and 540.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_noncenterless_inside_fixed_nonabelian
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (s : G) (hsS : s∈(d.S:Subgroup d.H).map d.H.subtype) (hs2 : orderOf s=2)
    (hsR : s∉Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype))
    (hz : center (d.block.map d.H.subtype)≠⊥) :
    ¬IsMulCommutative ((Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)⊓centralizer ({s}:Set G)):Subgroup G) := by
  let I := Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)⊓centralizer ({s}:Set G)
  obtain ⟨hZE,hZcard,hZR,hZN⟩ := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  let : IsElementaryAbelian 2 (distinguishedZ d) := hZE
  have hZne : distinguishedZ d≠⊥ := by
    intro he
    rw [he,card_bot] at hZcard
    have hn := hL.1
    have hh : 1<2^n := Nat.one_lt_pow (by omega) (by decide)
    omega
  have hs' : s^2=1 := by simpa only [hs2] using pow_orderOf_eq_one s
  obtain ⟨z,hzZ,hz1,hzs⟩ := exists_nonidentity_fixed_of_elementary_normalizer
    (distinguishedZ d) hZne s hs' (hZN hsS)
  intro hab
  let : IsMulCommutative I := hab
  have hder : ⁅I,I⁆=⊥ := commutator_self_eq_bot_iff.mpr inferInstance
  obtain ⟨x,hxT,hxS,_⟩ := c.outside
  rcases source_noncenterless_inside_fixed_derived d hG T hST hsingle hL hM hTM hunique c hz s hsS hs2 hsR x hxT hxS with hf | ⟨_,u,hu,hd⟩
  · have hzder := hf ⟨hzZ,mem_centralizer_singleton_iff.mpr hzs.eq.symm⟩
    rw [hder] at hzder
    exact hz1 hzder
  · rw [hder] at hd
    exact hu.2.1 (hd ▸ (distinguishedZ d).one_mem)
end CFSG.Quasithin.Chapter2.LinearShadows.Single
