module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ModuleGeometry
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeFusion
public import Theory.GroupTheory.SymmetricCommutatorPlane

/-!
# The literal symmetric B.4.8 plane in the L₃ source configuration

For a mutually normalizing noncommuting conjugate, every moving involution
has the same fixed and displacement plane. This forces the whole
commutator to be that plane and to contain the original fixed line.
Transitivity outside that line adjusts the conjugator inside L so that
the commutator is invariant under the literal MulAut.conj map. Both the
conjugate and the commutator remain unchanged by this adjustment.

Only the nonfixed-orbit theorem is used from SmallFusion.SLThreeFusion;
no fusion, Sylow-centralizer, or weak-closure theorem is used here.
Source: Aschbacher–Smith, B.4.8(2) and 12.4.9, printed pp.91 and 816.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource
open Section02 SmallFusion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The B.4.8 source geometry, with only its actual full-normalizer action
and the noncommuting conjugate still supplied as earlier inputs. -/
theorem symmetric_plane_of_noncommuting_conjugate
    (E : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥)
    (hN : ∀ n ∈ normalizer (V : Set G), ∃ l ∈ L,
      ∀ v ∈ V, MulAut.conj n v = MulAut.conj l v)
    (g : G) (hcomm : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hbound : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    ∃ k : G,
      V.map (MulAut.conj k).toMonoidHom = V.map (MulAut.conj g).toMonoidHom ∧
      V.map (MulAut.conj k).toMonoidHom ≤ normalizer (V : Set G) ∧
      fixedSubgroup L V ≤ ⁅V, V.map (MulAut.conj k).toMonoidHom⁆ ∧
      (⁅V, V.map (MulAut.conj k).toMonoidHom⁆).map (MulAut.conj k).toMonoidHom =
        ⁅V, V.map (MulAut.conj k).toMonoidHom⁆ ∧
      ⁅V, V.map (MulAut.conj k).toMonoidHom⁆ ≠ ⊥ ∧
      Nat.card (⁅V, V.map (MulAut.conj k).toMonoidHom⁆ : Subgroup G) = 4 := by
  let _ := D.elementary
  have hplanes : ∀ a ∈ normalizer (V : Set G), a ^ 2 = 1 →
      a ∉ centralizer (V : Set G) →
      fixedSubgroup L V ≤ ⁅V, zpowers a⁆ ∧
        ⁅V, zpowers a⁆ = V ⊓ centralizer ({a} : Set G) ∧
        Nat.card (⁅V, zpowers a⁆ : Subgroup G) = 4 := by
    intro a han ha hna
    obtain ⟨l, hl, he⟩ := hN a han
    apply ambient_involution_plane E hne a ha hna
      (E.quotientEquiv (QuotientGroup.mk' (pCore 2 L) ⟨l, hl⟩))
    intro v
    rw [E.conjugation]
    exact (he v.toMul v.toMul.property).symm
  obtain ⟨k, hk, hfix, hsym, hcard⟩ := exists_symmetric_commutator_plane
    V (fixedSubgroup L V) L (E.fixed_card_eq_two hne) D.normalizes
    (le_centralizer_iff.mpr inf_le_right)
    (fun x hx hxZ y hy hyZ => E.transitive_nonfixed hne x y hx hy hxZ hyZ)
    hplanes g hcomm hbound
  refine ⟨k, hk, ?_, hfix, hsym, ?_, hcard⟩
  · rw [hk]
    exact le_normalizer_iff_commutator_le_left.mpr (hbound.trans inf_le_left)
  · rwa [hk]

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource
