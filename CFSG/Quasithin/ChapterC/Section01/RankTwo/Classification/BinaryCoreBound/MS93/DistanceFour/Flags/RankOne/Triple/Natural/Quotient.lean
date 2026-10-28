module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Geometry
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.Representation.ElementaryAbelianAction
public import Theory.ElementaryAbelian.Quotient

/-!
# The actual quotient underlying the natural flag section

The denominator is the inverse image of the fixed space of the tilded
residual on V_beta/Z_alpha. It is normalized by the full parabolic, so
the quotient carries the literal conjugation action of that full actor.
The contrary triple-commutator hypothesis forces this quotient to be
nonzero. Residual commutator idempotence strengthens this to nontrivial
residual action on the quotient itself.

The module construction below supplies a finite binary representation,
an onto coordinate-free quotient map and its exact kernel. Recognizing
this representation as a single natural plane additionally requires the
geometric order bound on p.905; that bound is not asserted here.

Source: Meierfrankenfeld--Stellmacher (1993), numbered claim (1) in the
proof of (4.6.8), printed p.905.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
universe u
variable {M : Type u} [Group M] {L R : Subgroup M}

/-- The literal denominator of the natural section, before recognition. -/
noncomputable def flagFixedPreimage (source : LocalSource L R) (i : Bool) :
    Subgroup (FreeAmalgam R) :=
  commutatorPreimage (V R (beta R)) (flagResidual source i) (Z R (alpha R))

/-- The layer used for bars is contained in the actual edge layer. -/
theorem Z_le_edgeRadius : Z R (alpha R) ≤ V R (beta R) := by
  rw [V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)]
  exact le_iSup_of_le (alpha R)
    (le_iSup_of_le (adjacent_symm R (base_adjacent R)) le_rfl)

/-- The edge layer lies in the finite original vertex stabilizer. -/
theorem edgeRadius_le_stabilizer (geometry : Geometry R) (hlarge : 2 < geometry.b R) :
    V R (beta R) ≤ stabilizer R (alpha R) :=
  (edgeRadius_le_radius (alpha R) (beta R) rfl (base_adjacent R)).trans
    (geometry.V_local _ rfl hlarge)

/-- The full actor normalizes the layer used for bars. -/
theorem flagParabolic_normalizes_Z (source : LocalSource L R) (i : Bool) :
    flagParabolic source i ≤ normalizer (Z R (alpha R)) :=
  (flagParabolic_le source i).trans (Z_normalized R _)

/-- The fixed preimage contains Z_alpha and is contained in V_beta. -/
theorem flagFixedPreimage_bounds (source : LocalSource L R) (i : Bool) :
    Z R (alpha R) ≤ flagFixedPreimage source i ∧
      flagFixedPreimage source i ≤ V R (beta R) := by
  refine ⟨le_commutatorPreimage Z_le_edgeRadius ?_, commutatorPreimage_le _ _ _⟩
  exact le_normalizer_iff_commutator_le_left.mp
    ((flagResidual_le source i).trans (flagParabolic_normalizes_Z source i))

/-- Relative normality of the fixed preimage under the full, untilded actor. -/
theorem flagFixedPreimage_normalized [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) :
    flagParabolic source i ≤ normalizer (flagFixedPreimage source i) :=
  commutatorPreimage_normalized _ _ _ _
    ((edgeRadius_le_stabilizer geometry hlarge).trans (Z_normalized R _))
    (flagParabolic_normalizes_edgeRadius source geometry hlarge i hkernel)
    (flagResidual_normalized source i) (flagParabolic_normalizes_Z source i)

/-- The source denominator is intrinsically normal in its elementary numerator. -/
theorem flagFixedPreimage_normal (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) :
    ((flagFixedPreimage source i).subgroupOf (V R (beta R))).Normal := by
  let := edgeRadius_abelian geometry hlarge (alpha R) (beta R) rfl (base_adjacent R)
  infer_instance

/-- The full embedded parabolic has no nontrivial odd-order quotient. -/
theorem flagParabolic_primeToResidual [Finite M] (source : LocalSource L R) (i : Bool) :
    primeToResidual 2 (flagParabolic source i) = ⊤ := by
  let e := (parabolic source.projection source.flag i).equivMapOfInjective
    (embedM R) (embedM_injective R)
  change primeToResidual 2 ((parabolic source.projection source.flag i).map (embedM R)) = ⊤
  rw [← map_primeToResidual (p := 2) e,
    primeToResidual_parabolic_eq_top source.projection source.projection_surjective
      (by rw [source.projection_kernel]; exact pCore_isPGroup),
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr e.surjective]

/-- The selected parabolic contains the whole edge layer, not just its image
modulo Z_alpha. -/
theorem edgeRadius_le_flagParabolic [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) :
    V R (beta R) ≤ flagParabolic source i := by
  have h := (edgeRadius_le_radius (alpha R) (beta R) rfl (base_adjacent R)).trans
    ((V_le_Q geometry hlarge _ rfl).trans (Q_le_adjacent_h R rfl (base_adjacent R)))
  exact h.trans (hkernel ▸ flagKernel_le source i)

/-- Residual idempotence on the actual elementary edge group. The calculation
is made in the finite parabolic and mapped through its literal inclusion. -/
theorem flag_commutator_idempotent [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) :
    ⁅⁅V R (beta R), flagResidual source i⁆, flagResidual source i⁆ =
      ⁅V R (beta R), flagResidual source i⁆ := by
  let P := flagParabolic source i
  let H := V R (beta R)
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite P := Finite.of_injective (inclusion (flagParabolic_le source i))
    (inclusion_injective _)
  let : IsElementaryAbelian 2 H :=
    edgeRadius_elementary geometry hlarge (alpha R) (beta R) rfl (base_adjacent R)
  let : (H.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer
    (flagParabolic_normalizes_edgeRadius source geometry hlarge i hkernel)
  have hh := commutator_isPPerfect_idempotent (pResidual 2 P) (H.subgroupOf P)
    (isPPerfect_pResidual 2) ((IsElementaryAbelian.isPGroup 2 H).comap_subtype)
    le_normalizer_of_normal
  have hm := congrArg (Subgroup.map P.subtype) hh
  simp only [map_commutator] at hm
  dsimp only [P, H] at hm
  simpa only [
    map_subgroupOf_eq_of_le (edgeRadius_le_flagParabolic source geometry hlarge i hkernel),
    ← flagResidual_eq source i] using hm

/-- If the residual commutator vanished modulo Z_alpha, the contrary triple
would vanish entirely. -/
theorem flag_commutator_not_le_Z (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hbad : ¬ ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    ¬ ⁅V R (beta R), flagResidual source i⁆ ≤ Z R (alpha R) := by
  intro h
  apply hbad
  have hzero : ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤ ⊥ := by
    exact (commutator_mono h (V_le_Q geometry hlarge _ rfl)).trans_eq
      (geometry.centralizes _ rfl)
  exact hzero.trans bot_le

/-- The exact fixed-space denominator is proper under the contrary hypothesis. -/
theorem flagFixedPreimage_ne_edgeRadius (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hbad : ¬ ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    flagFixedPreimage source i ≠ V R (beta R) := by
  intro he
  apply flag_commutator_not_le_Z source geometry hlarge i hbad
  rw [← he]
  exact commutator_commutatorPreimage_le _ _ _
    ((edgeRadius_le_stabilizer geometry hlarge).trans (Z_normalized R _))

/-- The tilded residual really moves the final fixed-space quotient. This is
stronger than merely asserting that the quotient is nonzero. -/
theorem flag_residual_moves_quotient [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (hbad : ¬ ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    ¬ ⁅V R (beta R), flagResidual source i⁆ ≤ flagFixedPreimage source i := by
  intro h
  apply flag_commutator_not_le_Z source geometry hlarge i hbad
  rw [← flag_commutator_idempotent source geometry hlarge i hkernel]
  exact (commutator_mono h le_rfl).trans (commutator_commutatorPreimage_le _ _ _
    ((edgeRadius_le_stabilizer geometry hlarge).trans (Z_normalized R _)))

/-- Coordinate-free finite binary sections of the actual edge layer, with
the full parabolic action and a specified exact ambient denominator. -/
structure FlagLayerModule (source : LocalSource L R) (i : Bool)
    (N : Subgroup (FreeAmalgam R)) where
  Space : Type u
  [addCommGroup : AddCommGroup Space]
  [module : Module (ZMod 2) Space]
  [finite : Finite Space]
  representation : Representation (ZMod 2) (flagParabolic source i) Space
  projection : V R (beta R) →* Multiplicative Space
  onto : Function.Surjective projection
  kernel : projection.ker = N.subgroupOf (V R (beta R))
  action : ∀ (p : flagParabolic source i) (x y : V R (beta R)),
    (y : FreeAmalgam R) = (p : FreeAmalgam R) * (x : FreeAmalgam R) *
      (p : FreeAmalgam R)⁻¹ →
    (projection y).toAdd = representation p (projection x).toAdd

attribute [instance] FlagLayerModule.addCommGroup FlagLayerModule.module FlagLayerModule.finite

/-- Construct the actual elementary quotient by any full-actor invariant
denominator. This applies both to bars modulo Z_alpha and to the fixed quotient. -/
noncomputable def flagLayerModule [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (N : Subgroup (FreeAmalgam R)) (hn : flagParabolic source i ≤ normalizer N) :
    FlagLayerModule source i N := by
  let H := V R (beta R)
  let K := N.subgroupOf H
  let : IsElementaryAbelian 2 H :=
    edgeRadius_elementary geometry hlarge (alpha R) (beta R) rfl (base_adjacent R)
  let : K.Normal := inferInstance
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite H := Finite.of_injective (inclusion (edgeRadius_le_stabilizer geometry hlarge))
    (inclusion_injective _)
  let D := H ⧸ K
  have hex := exists_quotient_conjugation_action (flagParabolic source i) H N
    (flagParabolic_normalizes_edgeRadius source geometry hlarge i hkernel) hn inferInstance
  let a := Classical.choose hex
  have ha := Classical.choose_spec hex
  let : MulDistribMulAction (flagParabolic source i) D := MulDistribMulAction.compHom D a
  let ρ : Representation (ZMod 2) (flagParabolic source i) (Additive D) :=
    Representation.ofElementaryAbelianAction
  let p : H →* Multiplicative (Additive D) :=
    (MulEquiv.multiplicativeAdditive (H := D)).symm.toMonoidHom.comp (QuotientGroup.mk' K)
  exact {
    Space := Additive D
    representation := ρ
    projection := p
    onto := (MulEquiv.multiplicativeAdditive (H := D)).symm.surjective.comp
      (QuotientGroup.mk'_surjective K)
    kernel := (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' K)
      (MulEquiv.multiplicativeAdditive (H := D)).symm.toMonoidHom
      (MulEquiv.multiplicativeAdditive (H := D)).symm.injective).trans (QuotientGroup.ker_mk' K)
    action := by
      intro g x y hy
      change QuotientGroup.mk' K y = a g (QuotientGroup.mk' K x)
      rw [ha]
      congr 1
      exact Subtype.ext hy }

/-- The source barred edge layer with its actual full parabolic action. -/
noncomputable def flagBarModule [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) :
    FlagLayerModule source i (Z R (alpha R)) :=
  flagLayerModule source geometry hlarge i hkernel _ (flagParabolic_normalizes_Z source i)

/-- The precise fixed-space quotient in claim (1), before natural recognition. -/
noncomputable def flagQuotientModule [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) :
    FlagLayerModule source i (flagFixedPreimage source i) :=
  flagLayerModule source geometry hlarge i hkernel _
    (flagFixedPreimage_normalized source geometry hlarge i hkernel)

namespace FlagLayerModule
variable {source : LocalSource L R} {i : Bool} {N : Subgroup (FreeAmalgam R)}

/-- Trivial residual action in any exact layer coordinates forces the literal
ambient residual commutator into the specified denominator. -/
theorem commutator_le_of_residual_le_kernel [Finite M] (d : FlagLayerModule source i N)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (hkernel : flagKernel source i = Q R (beta R))
    (htriv : pResidual 2 (flagParabolic source i) ≤ d.representation.ker) :
    ⁅V R (beta R), flagResidual source i⁆ ≤ N := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl x hx
  rw [flagResidual_eq source i] at hl
  obtain ⟨g, hg, rfl⟩ := hl
  let v : V R (beta R) := ⟨x, hx⟩
  let w := edgeRadiusAction source geometry hlarge i hkernel g v
  have he : d.projection w = d.projection v := by
    apply Multiplicative.toAdd.injective
    rw [d.action g v w (edgeRadiusAction_apply source geometry hlarge i hkernel g v)]
    rw [MonoidHom.mem_ker.mp (htriv hg)]
    rfl
  have hk : w * v⁻¹ ∈ d.projection.ker := by
    change d.projection (w * v⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  rw [d.kernel] at hk
  exact hk

/-- The representation of the source fixed quotient has nontrivial
two-residual action; a two-group image is therefore impossible. -/
theorem residual_not_le_kernel [Finite M]
    (d : FlagLayerModule source i (flagFixedPreimage source i))
    (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (hkernel : flagKernel source i = Q R (beta R))
    (hbad : ¬ ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    ¬ pResidual 2 (flagParabolic source i) ≤ d.representation.ker := by
  intro h
  exact flag_residual_moves_quotient source geometry hlarge i hkernel hbad
    (d.commutator_le_of_residual_le_kernel geometry hlarge hkernel h)

/-- Actual equivariant linear coordinates turn an exact layer module into
the original rank-one factor, preserving its full actor and ambient kernel. -/
noncomputable def toRankOneFactor (d : FlagLayerModule source i N)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (hkernel : flagKernel source i = Q R (beta R)) [Finite M]
    (π : flagParabolic source i →* SL2)
    (hπ : Function.Surjective π) (e : d.Space ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (he : ∀ g v, e (d.representation g v) = (π g).val.mulVec (e v)) :
    RankOnePairing.RankOneFactor (flagParabolic source i) (V R (beta R)) N := by
  let f : Multiplicative d.Space ≃* Multiplicative (Fin 2 → ZMod 2) :=
    e.toAddEquiv.toMultiplicative
  exact {
    projection := π
    surjective := hπ
    coordinates := f.toMonoidHom.comp d.projection
    coordinates_surjective := f.surjective.comp d.onto
    kernel := (MonoidHom.ker_comp_of_injective d.projection f.toMonoidHom f.injective).trans d.kernel
    normalized := flagParabolic_normalizes_edgeRadius source geometry hlarge i hkernel
    action := by
      intro g x y hy
      change e (d.projection y).toAdd = (π g).val.mulVec (e (d.projection x).toAdd)
      rw [d.action g x y hy, he] }

/-- The size is the relative index of the exact source denominator. -/
theorem card (d : FlagLayerModule source i N) :
    Nat.card d.Space = N.relIndex (V R (beta R)) := by
  change Nat.card (Multiplicative d.Space) = (N.subgroupOf (V R (beta R))).index
  rw [← d.kernel, index_ker, MonoidHom.range_eq_top.mpr d.onto,
    Nat.card_congr (topEquiv).toEquiv]

/-- The quotient of claim (1) is nonzero under the contrary hypothesis. -/
theorem nontrivial (d : FlagLayerModule source i (flagFixedPreimage source i))
    (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (hbad : ¬ ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    Nontrivial d.Space := by
  rcases subsingleton_or_nontrivial d.Space with hs | h
  · let := hs
    have he : V R (beta R) ≤ flagFixedPreimage source i := by
      intro x hx
      have hk : (⟨x, hx⟩ : V R (beta R)) ∈ d.projection.ker :=
        show d.projection ⟨x, hx⟩ = 1 from Subsingleton.elim _ _
      rwa [d.kernel] at hk
    exact (flagFixedPreimage_ne_edgeRadius source geometry hlarge i hbad
      (le_antisymm (flagFixedPreimage_bounds source i).2 he)).elim
  · exact h

end FlagLayerModule
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
