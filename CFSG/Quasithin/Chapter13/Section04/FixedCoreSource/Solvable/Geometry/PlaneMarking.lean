module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Marking
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The original second flag in the five-dimensional core

The preimage in V of a subspace of the natural quotient uses the literal
core projection and the chosen coordinate map. Equivariance identifies
its normalizer in L with the corresponding permutation stabilizer.
Restricting the original Sylow subgroup to L and passing through the same
quotient shows that every T-invariant plane is an even conjugate of the
canonical syntheme plane. Relabeling both the quotient and module by that
same conjugator supplies the exact marking used by the chief-factor proof.

SecondFlag applies this to N_LT(V₂) and its embedded two-residual.
No arbitrary parabolic-image equality is assumed. Source:
Aschbacher–Smith Notation 13.2.1, printed p.877, and 13.4.9, p.906.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
open Chapter12.Section02
open Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
namespace CoreMarking
variable {D : ChosenModule T L V}

def relabel (m : CoreMarking D) (g : alternatingGroup (Fin 6)) : CoreMarking D where
  quotient := m.quotient.trans (MulAut.conj g⁻¹)
  coordinate := m.coordinate.trans
    (LinearEquiv.ofBijective (coreRepresentation (Fin 6) g.val⁻¹)
      ((coreRepresentation (Fin 6)).apply_bijective g.val⁻¹)).toAddEquiv.toMultiplicative
  equivariant l v := by
    change coreRepresentation (Fin 6) g.val⁻¹
      (m.coordinate (V.normalizerMonoidHom ⟨l.val,D.normalizes l.property⟩ v)).toAdd =
      coreRepresentation (Fin 6) (g.val⁻¹ * (m.quotient (QuotientGroup.mk' (centralCore L) l)).val * g.val)
        (coreRepresentation (Fin 6) g.val⁻¹ (m.coordinate v).toAdd)
    rw [m.equivariant]
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]

/-- The original preimage of a natural-module subspace inside V. -/
def naturalPreimage (m : CoreMarking D)
    (W : Submodule (ZMod 2) (natural (Fin 6))) : Subgroup G :=
  ((W.toAddSubgroup.toSubgroup).comap
    ((coreToNatural (Fin 6)).toAddMonoidHom.toMultiplicative.comp m.coordinate.toMonoidHom)).map V.subtype

theorem mem_naturalPreimage (m : CoreMarking D)
    (W : Submodule (ZMod 2) (natural (Fin 6))) (v : V) :
    v.val ∈ m.naturalPreimage W ↔ coreToNatural (Fin 6) (m.coordinate v).toAdd ∈ W := by
  exact mem_map_iff_mem V.subtype_injective

theorem naturalPreimage_le (m : CoreMarking D)
    (W : Submodule (ZMod 2) (natural (Fin 6))) : m.naturalPreimage W ≤ V := map_subtype_le _


theorem normalizes_naturalPreimage_iff (m : CoreMarking D)
    (W : Submodule (ZMod 2) (natural (Fin 6))) (l : L) :
    l.val ∈ normalizer (m.naturalPreimage W : Set G) ↔
      (m.quotient (QuotientGroup.mk' (centralCore L) l)).val ∈ flagStabilizer W := by
  have he (v : V) :
      coreToNatural (Fin 6) (m.coordinate (V.normalizerMonoidHom ⟨l.val,D.normalizes l.property⟩ v)).toAdd =
        naturalRepresentation (Fin 6) (m.quotient (QuotientGroup.mk' (centralCore L) l)).val
          (coreToNatural (Fin 6) (m.coordinate v).toAdd) := by
    rw [m.equivariant,coreToNatural_equivariant]
  constructor
  · intro hl w
    obtain ⟨c,rfl⟩ := coreToNatural_surjective w
    obtain ⟨v,hv⟩ := m.coordinate.surjective (Multiplicative.ofAdd c)
    have hc : (m.coordinate v).toAdd = c := congrArg Multiplicative.toAdd hv
    rw [←hc,←he,←mem_naturalPreimage,←mem_naturalPreimage]
    exact ((mem_normalizer_iff.mp hl) v.val).symm
  · intro hl
    apply mem_normalizer_iff.mpr
    intro x
    by_cases hx : x ∈ V
    · let v : V := ⟨x,hx⟩
      have hh := hl (coreToNatural (Fin 6) (m.coordinate v).toAdd)
      rw [←he,←mem_naturalPreimage,←mem_naturalPreimage] at hh
      exact hh.symm
    · have hx' : l.val * x * l.val⁻¹ ∉ V :=
        fun hh => hx (((mem_normalizer_iff.mp (D.normalizes l.property)) x).mpr hh)
      exact iff_of_false (fun hh => hx (m.naturalPreimage_le W hh))
        (fun hh => hx' (m.naturalPreimage_le W hh))

theorem naturalPreimage_normalizer_image (m : CoreMarking D)
    (W : Submodule (ZMod 2) (natural (Fin 6))) :
    ((L ⊓ normalizer (m.naturalPreimage W : Set G)).subgroupOf L).map
      ((alternatingGroup (Fin 6)).subtype.comp
        (m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L)))) =
      flagStabilizer W ⊓ alternatingGroup (Fin 6) := by
  ext a
  constructor
  · rintro ⟨l,hl,rfl⟩
    exact ⟨(m.normalizes_naturalPreimage_iff W l).mp hl.2,
      (m.quotient (QuotientGroup.mk' (centralCore L) l)).property⟩
  · rintro ⟨ha,hae⟩
    obtain ⟨q,hq⟩ := m.quotient.surjective ⟨a,hae⟩
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) q
    refine ⟨l,⟨l.property,(m.normalizes_naturalPreimage_iff W l).mpr ?_⟩,?_⟩
    · rw [hq]
      exact ha
    · exact congrArg Subtype.val hq

theorem sylow_normalizes_inner_plane (m : CoreMarking D)
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G)) :
    (T : Subgroup G) ≤ normalizer
      ((L ⊓ normalizer (m.naturalPreimage W : Set G) : Subgroup G) : Set G) :=
  (le_inf D.sylow_normalizes_component (hT.trans (normalizer _).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

variable [Finite G]
theorem natural_plane_alignment (m : CoreMarking D)
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G)) :
    ∃ g : alternatingGroup (Fin 6), W = move g.val canonicalPlane := by
  let X := L ⊔ (T : Subgroup G)
  let N := L.subgroupOf X
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  obtain ⟨S,hS⟩ := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).exists_subgroupOf_eq_of_normal N
  let e := subgroupOfEquivOfLe (show L ≤ X from le_sup_left)
  let q : N →* alternatingGroup (Fin 6) :=
    m.quotient.toMonoidHom.comp ((QuotientGroup.mk' (centralCore L)).comp e.toMonoidHom)
  have hq : Function.Surjective q := m.quotient.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp e.surjective)
  let P := S.mapSurjective hq
  have hi : ∀ a ∈ (P : Subgroup (alternatingGroup (Fin 6))).map
      (alternatingGroup (Fin 6)).subtype, move a W = W := by
    rintro a ⟨b,⟨c,hc,rfl⟩,rfl⟩
    have hcT : c.val.val ∈ (T : Subgroup G) := by rw [hS] at hc; exact hc
    exact (BinaryFlags.NaturalPairing.mem_stabilizer_iff_map W _).mp
      ((m.normalizes_naturalPreimage_iff W (e c)).mp (hT hcT))
  obtain ⟨g,hg⟩ := exists_conjugate_T0_le (alternatingGroup (Fin 6)) le_rfl P
  exact ⟨g,(invariant_unique_conjugate T0 le_rfl g.val W
    (fun a ha => hi a (hg ha))).2 hW⟩

omit [Finite G] in
theorem aligned_inner_plane_image (m : CoreMarking D)
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (g : alternatingGroup (Fin 6)) (hg : W = move g.val canonicalPlane) :
    ((L ⊓ normalizer (m.naturalPreimage W : Set G)).subgroupOf L).map
      ((alternatingGroup (Fin 6)).subtype.comp
        ((m.relabel g).quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L)))) =
      synthemeStabilizer ⊓ alternatingGroup (Fin 6) := by
  let α := (alternatingGroup (Fin 6)).subtype.comp
    (m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L)))
  change ((L ⊓ normalizer (m.naturalPreimage W : Set G)).subgroupOf L).map
    ((MulAut.conj g.val⁻¹).toMonoidHom.comp α) = _
  rw [←map_map,m.naturalPreimage_normalizer_image W,hg,flagStabilizer_move,flagStabilizer_plane]
  have hc : BinaryFlags.H2.map (MulAut.conj g.val).toMonoidHom ⊓ alternatingGroup (Fin 6) =
      (BinaryFlags.H2 ⊓ alternatingGroup (Fin 6)).map (MulAut.conj g.val).toMonoidHom := by
    rw [map_inf _ _ _ (MulAut.conj g.val).injective,BinaryFlags.conjugate_alternating]
  rw [hc,map_map]
  have he : (MulAut.conj g.val⁻¹).toMonoidHom.comp (MulAut.conj g.val).toMonoidHom = MonoidHom.id _ := by
    ext a
    simp
  rw [he,map_id]
  rfl

end CoreMarking
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
