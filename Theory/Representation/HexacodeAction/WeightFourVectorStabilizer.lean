module

public import Theory.Representation.HexacodeAction.FullWeightVectorStabilizer
public import Theory.Representation.HexacodeAction.PairGeometry
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Models

/-!
# The actual weight-four vector stabilizer is S4

The coordinate action of the stabilizer of a weight-four codeword preserves
its two zero positions. Fixing the vector removes the central scalar kernel.
The weight-four orbit has size forty-five, so this faithful action on the
remaining four coordinates is the whole symmetric group.

Source: Aschbacher--Smith12.7.2(2--5), printed p.839. This is the pointwise
stabilizer of the scalar point, distinct from its full setwise stabilizer.
The literal hexacode and monomial action retain their ATLAS attribution.
-/

public noncomputable section
open Atlas.Codes Subgroup
namespace Representation.Hexacode
open BinaryOffender BinaryPermutation.SixPairsQuadratic
open Theory.SpecificGroups.SymmetricSix

private def firstPair : Pair := ⟨{0,1},by decide⟩
private def seed : hexacode := ⟨systematicEncoder ![0,0,a],systematic_mem _⟩

private theorem seed_weight : hammingNorm seed.val = 4 := by decide

private theorem seed_ne_zero : seed ≠ 0 := by
  intro h
  have hh := seed_weight
  simp [h] at hh

private theorem seed_plane :
    (Submodule.span F {seed}).restrictScalars Bit = zeroPairPlane firstPair := by
  have hle : (Submodule.span F {seed}).restrictScalars Bit ≤ zeroPairPlane firstPair := by
    intro w hw
    obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [field_smul_formula]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (by intro i hi; revert i hi; decide)
    · apply Submodule.smul_mem
      intro i hi
      revert i hi
      decide
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [fieldPoint_binary_finrank _ (finrank_span_singleton seed_ne_zero),zeroPairPlane_finrank]

private theorem stabilizer_fixes_plane (v : hexacode) (g : fullWeightVectorStabilizer v) :
    g.val.val ∈ subspaceStabilizer action ((Submodule.span F {v}).restrictScalars Bit) := by
  intro w
  constructor
  · intro hw
    obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hw
    apply Submodule.mem_span_singleton.mpr
    refine ⟨r,?_⟩
    apply (evenFieldAction g.val).injective
    rw [map_smul]
    exact (congrArg (fun z => r • z) g.property).trans hr
  · intro hw
    obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hw
    apply Submodule.mem_span_singleton.mpr
    refine ⟨r,?_⟩
    change r • v = evenFieldAction g.val (r • v)
    rw [map_smul]
    exact congrArg (fun z => r • z) g.property.symm

private def seedCoordinate : fullWeightVectorStabilizer seed →* a6DuadStabilizer :=
  (hexEvenCoordinate.comp (fullWeightVectorStabilizer seed).subtype).codRestrict _ (by
    intro g
    have hp := stabilizer_fixes_plane seed g
    rw [seed_plane] at hp
    have he := (zeroPairPlane_stabilizer_iff _ firstPair).mp hp
    change ({0,1} : Finset (Fin 6)).image (hexEvenCoordinate g.val).val = {0,1}
    have hh := congrArg Subtype.val he
    change ({0,1} : Finset (Fin 6)).map (hexCoordinateSixHom g.val.val).toEmbedding = {0,1} at hh
    rw [Finset.map_eq_image] at hh
    exact hh)

private theorem scalar_fixed_trivial (v : hexacode) (hv : v ≠ 0)
    (g : HexEvenAutomorphisms) (hg : g ∈ hexEvenCoordinate.ker)
    (hfix : evenAction g v = v) : g = 1 := by
  classical
  rw [hexEvenCoordinate_kernel,mem_zpowers_iff_mem_range_orderOf,hexEvenZ_order] at hg
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hg
  have hn3 : n < 3 := Finset.mem_range.mp hn
  have hs : evenAction hexEvenZ v = omega • v := scalar_eq_omega_smul v
  interval_cases n
  · exact pow_zero _
  · have he : (omega-1) • v = 0 := by
      rw [sub_smul,one_smul]
      simpa only [pow_one,hs,sub_eq_zero] using hfix
    rcases smul_eq_zero.mp he with h | h
    · exact False.elim ((by decide : omega ≠ 1) (sub_eq_zero.mp h))
    · exact False.elim (hv h)
  · have he : (omega^2-1) • v = 0 := by
      change evenAction (hexEvenZ*hexEvenZ) v = v at hfix
      rw [map_mul,Module.End.mul_apply,hs] at hfix
      change evenFieldAction hexEvenZ (omega • v) = v at hfix
      rw [map_smul] at hfix
      change omega • evenAction hexEvenZ v = v at hfix
      rw [hs] at hfix
      rw [sub_smul,one_smul,pow_two,mul_smul,hfix,sub_self]
    rcases smul_eq_zero.mp he with h | h
    · exact False.elim ((by decide : omega^2 ≠ 1) (sub_eq_zero.mp h))
    · exact False.elim (hv h)

private theorem seedCoordinate_injective : Function.Injective seedCoordinate := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  have he : hexEvenCoordinate g.val = 1 := congrArg Subtype.val hg
  exact Subtype.ext (scalar_fixed_trivial seed seed_ne_zero g.val he g.property)

/-- A weight-four vector has an actual stabilizer of order twenty-four. -/
theorem weightFourVectorStabilizer_card (v : hexacode)
    (hv : hammingNorm v.val = 4) : Nat.card (fullWeightVectorStabilizer v) = 24 := by
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  let : MulAction HexEvenAutomorphisms hexacode := {
    smul := fun g w => evenAction g w
    one_smul := fun w => by change evenAction 1 w = w; rw [map_one]; rfl
    mul_smul := fun g h w => by
      change evenAction (g*h) w = evenAction g (evenAction h w)
      rw [map_mul,Module.End.mul_apply] }
  have ho : (MulAction.orbit HexEvenAutomorphisms v).ncard = 45 := by
    exact (evenAction_orbit_card v hv0).trans (by simp [hv])
  have hc := (fullWeightVectorStabilizer v).card_mul_index
  have hi : (fullWeightVectorStabilizer v).index = 45 :=
    (MulAction.index_stabilizer HexEvenAutomorphisms v).trans ho
  rw [hi,hexEven_card] at hc
  omega

private def seedEquiv : fullWeightVectorStabilizer seed ≃* Equiv.Perm (Fin 4) :=
  (MulEquiv.ofBijective seedCoordinate
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨seedCoordinate_injective,by
      rw [weightFourVectorStabilizer_card seed seed_weight,a6DuadStabilizer_card]⟩)).trans
    a6DuadModelEquiv.symm

private def stabilizerConj (k : HexEvenAutomorphisms) (v : hexacode) :
    fullWeightVectorStabilizer v ≃* fullWeightVectorStabilizer (evenAction k v) := by
  have he : (fullWeightVectorStabilizer v).map (MulAut.conj k).toMonoidHom =
      fullWeightVectorStabilizer (evenAction k v) := by
    ext g
    rw [mem_map_equiv]
    change evenAction (k⁻¹*g*k) v = v ↔ evenAction g (evenAction k v) = evenAction k v
    constructor
    · intro h
      have hh := congrArg (evenAction k) h
      simpa only [←Module.End.mul_apply,←map_mul,mul_inv_cancel_left,mul_assoc] using hh
    · intro h
      have hh := congrArg (evenAction k⁻¹) h
      simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_left,mul_assoc,
        inv_mul_cancel,map_one,Module.End.one_apply] using hh
  exact ((MulAut.conj k).subgroupMap _).trans (MulEquiv.subgroupCongr he)

private theorem seed_orbit (v : hexacode) (hv : hammingNorm v.val = 4) :
    ∃ k : HexEvenAutomorphisms, evenAction k seed = v := by
  have hh : v ∈ Set.range (fun k : HexEvenAutomorphisms => evenAction k seed) := by
    rw [evenAction_orbit_eq_weight seed seed_ne_zero]
    exact hv.trans seed_weight.symm
  exact hh

/-- The actual vector stabilizer, hence the pointwise scalar-plane stabilizer,
is S4. The full setwise plane stabilizer still has its central cubic kernel. -/
def weightFourVectorStabilizerEquiv (v : hexacode) (hv : hammingNorm v.val = 4) :
    fullWeightVectorStabilizer v ≃* Equiv.Perm (Fin 4) :=
  ((stabilizerConj (seed_orbit v hv).choose seed).trans
    (MulEquiv.subgroupCongr (congrArg fullWeightVectorStabilizer
      (seed_orbit v hv).choose_spec))).symm.trans seedEquiv

end Representation.Hexacode
