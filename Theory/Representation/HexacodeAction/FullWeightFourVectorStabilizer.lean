module

public import Theory.Representation.HexacodeAction.WeightFourVectorStabilizer
public import Theory.Representation.BinaryPermutation.SixPairsQuadratic.Cosets
public import Theory.Representation.HexacodeAction.ThompsonOffenders

/-!
# The full stabilizer of a weight-four vector

The full monomial group has the same weight-four orbit as its even subgroup,
so the vector stabilizer has order 48. Its coordinate action is faithful and
preserves the actual two zero positions. This identifies it with the literal
duad stabilizer S2 × S4, with an explicit even coordinate relabeling. The
even subgroup is the sign graph; it is also precisely the subgroup fixing
the whole scalar point pointwise.

Source: Aschbacher--Smith, 12.7.15(2--3), printed p.843. The coordinate-six
action used here is kept distinct from the action on full-weight planes.
-/

public noncomputable section
open Atlas.Codes Subgroup
namespace Representation.Hexacode
open BinaryOffender BinaryPermutation.SixPairsQuadratic
open Theory.SpecificGroups.SymmetricSix

/-- The stabilizer of the vector in the full monomial group. -/
@[expose] def fullVectorStabilizer (v : hexacode) : Subgroup HexAutomorphisms where
  carrier := {g | action g v = v}
  one_mem' := by change action 1 v = v; rw [map_one]; rfl
  mul_mem' := by
    intro g h hg hh
    change action (g * h) v = v
    rw [map_mul, Module.End.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    change action g v = v at hg
    change action g⁻¹ v = v
    have hh := congrArg (action g⁻¹) hg
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using hh.symm

/-- Fixing a nonzero scalar point pointwise is exactly fixing its vector
and belonging to the even subgroup. -/
theorem scalar_point_kernel_eq_even_vector (v : hexacode) (hv : v ≠ 0) :
    subspaceKernel action ((Submodule.span F {v}).restrictScalars Bit) ⊤ =
      fullVectorStabilizer v ⊓ hexSign.ker := by
  ext g
  constructor
  · rintro ⟨_, hg⟩
    have hgv : action g v = v := hg v (Submodule.mem_span_singleton_self v)
    refine ⟨hgv, ?_⟩
    rcases Int.units_eq_one_or (hexSign g) with he | ho
    · exact he
    · have hω := hg (omega • v)
        ((Submodule.span F {v}).smul_mem omega (Submodule.mem_span_singleton_self v))
      exact (hv (ThompsonOffenders.eq_zero_of_odd_fixes_scalar g ho v hgv hω)).elim
  · rintro ⟨hg, he⟩
    refine ⟨mem_top _, ?_⟩
    intro w hw
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [action_even_smul g he]
    exact congrArg (fun x => r • x) hg

private theorem full_vector_fixes_scalar_point (v : hexacode) (g : fullVectorStabilizer v) :
    g.val ∈ subspaceStabilizer action ((Submodule.span F {v}).restrictScalars Bit) := by
  have hforward (g : HexAutomorphisms) (hg : action g v = v)
      (w : hexacode) (hw : w ∈ Submodule.span F {v}) :
      action g w ∈ Submodule.span F {v} := by
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rcases Int.units_eq_one_or (hexSign g) with he | ho
    · rw [action_even_smul g he, hg]
      exact (Submodule.span F {v}).smul_mem _ (Submodule.mem_span_singleton_self v)
    · rw [action_odd_smul g ho, hg]
      exact (Submodule.span F {v}).smul_mem _ (Submodule.mem_span_singleton_self v)
  intro w
  constructor
  · intro hw
    change w ∈ Submodule.span F {v}
    have hi : action g.val⁻¹ v = v := (fullVectorStabilizer v).inv_mem g.property
    have hh := hforward g.val⁻¹ hi (action g.val w) hw
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using hh
  · exact hforward g.val g.property w

/-- The actual full weight-four vector stabilizer has order 48. -/
theorem fullWeightFourVectorStabilizer_card (v : hexacode)
    (hv : hammingNorm v.val = 4) : Nat.card (fullVectorStabilizer v) = 48 := by
  have hv0 : v ≠ 0 := by intro he; simp [he] at hv
  let : MulAction HexAutomorphisms hexacode := {
    smul := fun g w => action g w
    one_smul := fun w => by change action 1 w = w; rw [map_one]; rfl
    mul_smul := fun g h w => by
      change action (g * h) w = action g (action h w)
      rw [map_mul, Module.End.mul_apply] }
  have ho : MulAction.orbit HexAutomorphisms v =
      Set.range (fun g : HexEvenAutomorphisms => evenAction g v) := by
    ext w
    constructor
    · rintro ⟨g, rfl⟩
      rw [evenAction_orbit_eq_weight v hv0]
      exact Monomial.act_weight g.val v.val
    · rintro ⟨g, rfl⟩
      exact ⟨g.val, rfl⟩
  have hi : (fullVectorStabilizer v).index = 45 := by
    change (MulAction.stabilizer HexAutomorphisms v).index = 45
    rw [MulAction.index_stabilizer HexAutomorphisms v, ho, evenAction_orbit_card v hv0]
    simp [hv]
  have hc := (fullVectorStabilizer v).card_mul_index
  rw [hi, hexAutomorphisms_card] at hc
  omega

private theorem coordinate_injective (v : hexacode) (hv : v ≠ 0) :
    Function.Injective (hexCoordinateSixHom.comp (fullVectorStabilizer v).subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  have he : hexCoordinateSixHom g.val = 1 := hg
  rcases hex_kernel_trichotomy g.val ((hexSix_eq_one _).mp he) with h | h | h
  · exact Subtype.ext h
  · have hh := g.property
    rw [h] at hh
    exact (hv ((scalar_fixed_iff v).mp hh)).elim
  · have hh := g.property
    rw [h] at hh
    have hh' := congrArg (action hexZ) hh
    have hz : hexZ * hexZ ^ 2 = 1 := by simpa only [← pow_succ'] using hexZ_cube
    rw [← Module.End.mul_apply, ← map_mul, hz, map_one, Module.End.one_apply] at hh'
    exact (hv ((scalar_fixed_iff v).mp hh'.symm)).elim

private theorem exists_zero_pair (v : hexacode) (hv : hammingNorm v.val = 4) :
    ∃ s : Pair, (Submodule.span F {v}).restrictScalars Bit = zeroPairPlane s := by
  have hv0 : v ≠ 0 := by intro he; simp [he] at hv
  rcases fieldPoint_full_or_pair (Submodule.span F {v}) (finrank_span_singleton hv0)
    with hfull | hpair
  · have hh := hfull.2.2 ⟨v, Submodule.mem_span_singleton_self v⟩
      (fun he => hv0 (congrArg Subtype.val he))
    change hammingNorm v.val = 6 at hh
    omega
  · exact hpair

private theorem pair_fixed_iff (s : Pair) (g : Equiv.Perm (Fin 6)) :
    pairPerm g s = s ↔ g • s.val = s.val := by
  rw [Subtype.ext_iff]
  change s.val.map g.toEmbedding = s.val ↔ s.val.image g = s.val
  simp only [Finset.map_eq_image, Equiv.coe_toEmbedding]

private theorem product_even_iff (x : DuadProduct) :
    Equiv.Perm.sign (duadProductHom x) = 1 ↔ x.1 = signPermTwo x.2 := by
  revert x
  decide +kernel

/-- The full stabilizer is the literal duad product after an explicit even
coordinate relabeling, and its even subgroup is exactly the sign graph. -/
theorem fullWeightFourVectorStabilizer_model (v : hexacode)
    (hv : hammingNorm v.val = 4) :
    ∃ e : fullVectorStabilizer v ≃* DuadProduct,
      ∃ r : alternatingGroup (Fin 6),
        (∀ g : fullVectorStabilizer v,
          duadProductHom (e g) = r.val * hexCoordinateSixHom g.val * r.val⁻¹) ∧
        (∀ g : fullVectorStabilizer v,
          hexSign g.val = 1 ↔ (e g).1 = signPermTwo (e g).2) := by
  have hv0 : v ≠ 0 := by intro he; simp [he] at hv
  obtain ⟨s, hs⟩ := exists_zero_pair v hv
  obtain ⟨r, hr⟩ := exists_even_pair_transport s (⟨{0, 1}, by decide⟩ : Pair)
  have hr' : (pair 0 1) = r.val • s.val := by
    have hh := congrArg Subtype.val hr
    change s.val.map r.val.toEmbedding = {0, 1} at hh
    change {0, 1} = s.val.image r.val
    simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using hh.symm
  let P := MulAction.stabilizer (Equiv.Perm (Fin 6)) s.val
  let q : fullVectorStabilizer v →* P :=
    (hexCoordinateSixHom.comp (fullVectorStabilizer v).subtype).codRestrict _ (by
      intro g
      have hh := full_vector_fixes_scalar_point v g
      rw [hs] at hh
      exact (pair_fixed_iff s _).mp ((zeroPairPlane_stabilizer_iff g.val s).mp hh))
  let d : P ≃* duadStabilizer := MulAction.stabilizerEquivStabilizer hr'
  have hq : Function.Bijective q := by
    apply (Nat.bijective_iff_injective_and_card _).mpr
    refine ⟨?_, ?_⟩
    · intro x y hh
      exact coordinate_injective v hv0 (congrArg Subtype.val hh)
    · rw [fullWeightFourVectorStabilizer_card v hv,
        Nat.card_congr d.toEquiv, duadStabilizer_card]
  let e : fullVectorStabilizer v ≃* DuadProduct :=
    ((MulEquiv.ofBijective q hq).trans d).trans duadProductEquiv.symm
  have he (g : fullVectorStabilizer v) :
      duadProductHom (e g) = r.val * hexCoordinateSixHom g.val * r.val⁻¹ := by
    have hh := congrArg Subtype.val (duadProductEquiv.apply_symm_apply (d (q g)))
    change duadProductHom (e g) = (d (q g)).val at hh
    exact hh.trans (MulAction.stabilizerEquivStabilizer_apply hr' (q g))
  refine ⟨e, r, he, ?_⟩
  intro g
  rw [← product_even_iff, he]
  have hrs : Equiv.Perm.sign r.val = 1 := r.property
  simp only [map_mul, map_inv, hrs, inv_one, one_mul, mul_one]
  rfl

end Representation.Hexacode
