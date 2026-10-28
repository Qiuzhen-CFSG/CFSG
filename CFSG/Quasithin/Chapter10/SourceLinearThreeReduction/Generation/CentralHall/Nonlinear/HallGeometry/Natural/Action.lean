module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.FixedVectors
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.ComponentAction
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.Representation.CentralCoverOriginalAction.Quadratic
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.Representation.SL2NaturalOffenders.FieldAction.Basic

/-!
# The original Hall action on a natural component section

The Hall group preserves both the moved subgroup and its component-central
kernel. The literal quotient conjugation therefore extends to its specified
natural coordinates. Equivariance identifies its normalizer action on SL₂
with the original component automorphism, and the diagonal argument fixes
the coordinates of the Sylow-stabilizer-fixed vectors.

The natural matrix commutant consists of field scalars. Conjugating that
commutant gives semilinearity and an actual coefficient homomorphism from
the original Hall carrier, whose image has odd order. Its triviality and the
remaining Borel placement are still needed for the natural-row exclusion.
Source: Aschbacher--Smith, 10.1.2(5) and 10.2.3, printed pp.742 and745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 Representation
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
local instance naturalHallBinaryAlgebra (r : ℕ) : Algebra (ZMod 2) (GaloisField 2 r) :=
  ZMod.algebra _ 2

include D c

/-- The actual Hall actor preserves the denominator of the natural section. -/
theorem hall_normalizes_natural_kernel :
    B.map H.subtype ≤ normalizer
      ((⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
  (le_inf (hall_normalizes_moved D c)
    ((hall_normalizes_component D c).trans
      (normalizer_le_normalizer_centralizer L))).trans
    inf_normalizer_le_normalizer_inf

/-- The original Hall action extends to the actual natural quotient coordinates.
It intertwines the literal component automorphism and fixes the coordinates
of vectors fixed by the original Sylow component stabilizer. -/
theorem exists_natural_hall_action
    (geometry : ModuleGeometry D) (r : ℕ)
    (e : (L ⧸ pCore 2 L) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 r))
    (d : NaturalSection D r e) :
    ∃ η : Representation (ZMod 2) B (Fin 2 → GaloisField 2 r),
      (∀ (b : B) (w : (⁅D.fullModule,L⁆ : Subgroup G)),
        η b (d.coordinates w).toAdd =
          (d.coordinates ⟨(b : G)*w*(b : G)⁻¹,
            (mem_normalizer_iff.mp (hall_normalizes_moved D c
              (mem_map_of_mem H.subtype b.property)) w).mp w.property⟩).toAdd) ∧
      (∀ (b : B) (l : L) (v : Fin 2 → GaloisField 2 r),
        η b (SL2.BinarySmall.natural (e (QuotientGroup.mk' (pCore 2 L) l)) v) =
          SL2.BinarySmall.natural
            (e (componentAction D c b (QuotientGroup.mk' (pCore 2 L) l))) (η b v)) ∧
      (∀ (b : B) (w : (⁅D.fullModule,L⁆ : Subgroup G)),
        (w : G) ∈ centralizer
          ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) →
        η b (d.coordinates w).toAdd = (d.coordinates w).toAdd) := by
  let W : Subgroup G := ⁅D.fullModule,L⁆
  have hWV : W ≤ D.moduleSubgroup := by
    have hh := le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
    exact hh.trans (le_of_eq geometry.full_eq_local)
  let := D.module_elementary
  let : IsElementaryAbelian 2 W :=
    IsElementaryAbelian.of_injective (inclusion hWV) (inclusion_injective hWV)
  let P := B.map H.subtype
  have hPW := hall_normalizes_moved D c
  obtain ⟨η₀,hη₀⟩ := d.exists_original_quotient_action hPW
    (hall_normalizes_natural_kernel D c)
  let f : B →* P := (H.subtype.comp B.subtype).codRestrict P
    (fun b => mem_map_of_mem H.subtype b.property)
  let η := η₀.comp f
  have hη (b : B) (w : W) : η b (d.coordinates w).toAdd =
      (d.coordinates (W.normalizerMonoidHom
        ⟨(b : G),hPW (mem_map_of_mem H.subtype b.property)⟩ w)).toAdd :=
    hη₀ (f b) w
  refine ⟨η,hη,?_,?_⟩
  · intro b l v
    obtain ⟨w,hw⟩ := d.onto (Multiplicative.ofAdd v)
    have hv : (d.coordinates w).toAdd = v := congrArg Multiplicative.toAdd hw
    rw [←hv]
    let l' : L := L.normalizerMonoidHom
      ⟨(b : G),hall_normalizes_component D c
        (mem_map_of_mem H.subtype b.property)⟩ l
    have hl' : componentAction D c b (QuotientGroup.mk' (pCore 2 L) l) =
        QuotientGroup.mk' (pCore 2 L) l' := quotientAut_apply_mk _ _ _
    rw [hl']
    change η b ((SL2.BinarySmall.natural.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) l (d.coordinates w).toAdd) = _
    rw [←d.equivariant,hη,hη]
    refine Eq.trans ?_ (d.equivariant l' (W.normalizerMonoidHom
      ⟨(b : G),hPW (mem_map_of_mem H.subtype b.property)⟩ w))
    congr 2
    apply Subtype.ext
    change (b : G)*((l : G)*(w : G)*(l : G)⁻¹)*(b : G)⁻¹ =
      ((b : G)*(l : G)*(b : G)⁻¹)*((b : G)*(w : G)*(b : G)⁻¹)*
        ((b : G)*(l : G)*(b : G)⁻¹)⁻¹
    group
  · intro b w hw
    rw [hη]
    exact congrArg Multiplicative.toAdd
      (natural_hall_fixed_coordinates D c geometry r e d w hw b)

/-- Each literal Hall actor on the natural section is semilinear over its
specified coefficient field; the central section kernel is retained. -/
theorem exists_natural_hall_semilinear
    (geometry : ModuleGeometry D) (r : ℕ)
    (e : (L ⧸ pCore 2 L) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 r))
    (d : NaturalSection D r e) :
    ∃ η : Representation (ZMod 2) B (Fin 2 → GaloisField 2 r),
      (∀ (b : B) (w : (⁅D.fullModule,L⁆ : Subgroup G)),
        η b (d.coordinates w).toAdd =
          (d.coordinates ⟨(b : G)*w*(b : G)⁻¹,
            (mem_normalizer_iff.mp (hall_normalizes_moved D c
              (mem_map_of_mem H.subtype b.property)) w).mp w.property⟩).toAdd) ∧
      ∀ b : B, ∃ σ : GaloisField 2 r ≃+* GaloisField 2 r,
        ∀ a v, η b (a • v) = σ a • η b v := by
  obtain ⟨η,hη,hcomp,_⟩ := exists_natural_hall_action D c geometry r e d
  refine ⟨η,hη,fun b => ?_⟩
  let a : MulAut (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 r)) :=
    MulAut.congr e (componentAction D c b)
  apply OneCohomology.CentralCoverOriginalAction.normalizer_semilinear
    (specialLinearNatural 2 (k := GaloisField 2 r))
    (fun f hf => SL2NaturalOffenders.centralizer_scalar f hf) a (LinearMap.GeneralLinearGroup.toLinearEquiv (η.asGroupHom b))
  intro g v
  obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
  subst g
  change η b (SL2.BinarySmall.natural (e (QuotientGroup.mk' (pCore 2 L) l)) v) =
    SL2.BinarySmall.natural
      (e (componentAction D c b (e.symm (e (QuotientGroup.mk' (pCore 2 L) l))))) (η b v)
  rw [e.symm_apply_apply]
  exact hcomp b l v

/-- Semilinearity supplies the actual odd coefficient-action image of the
original Hall group, before its remaining field-factor exclusion. -/
theorem exists_natural_hall_field_action
    (geometry : ModuleGeometry D) (r : ℕ)
    (e : (L ⧸ pCore 2 L) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 r))
    (d : NaturalSection D r e) :
    ∃ (η : Representation (ZMod 2) B (Fin 2 → GaloisField 2 r))
      (φ : B →* (GaloisField 2 r ≃+* GaloisField 2 r)),
      (∀ (b : B) (w : (⁅D.fullModule,L⁆ : Subgroup G)),
        η b (d.coordinates w).toAdd =
          (d.coordinates ⟨(b : G)*w*(b : G)⁻¹,
            (mem_normalizer_iff.mp (hall_normalizes_moved D c
              (mem_map_of_mem H.subtype b.property)) w).mp w.property⟩).toAdd) ∧
      (∀ (b : B) a v, η b (a • v) = φ b a • η b v) ∧
      Odd (Nat.card φ.range) := by
  obtain ⟨η,hη,hsemi⟩ := exists_natural_hall_semilinear D c geometry r e d
  let φ := SL2NaturalOffenders.fieldAction η hsemi
  exact ⟨η,φ,hη,SL2NaturalOffenders.fieldAction_smul η hsemi,
    (hall_odd D c).of_dvd_nat (Subgroup.card_range_dvd φ)⟩

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
