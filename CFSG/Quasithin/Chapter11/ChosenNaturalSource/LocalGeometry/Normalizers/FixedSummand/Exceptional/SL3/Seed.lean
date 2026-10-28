module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.SL3Core.Point

/-!
# The literal SL₃ point-residual action on the chosen seed

Point-local transvections generate all three coordinates by displacement.
Transport through the original natural marking gives [V,L₁]=V. The same
marked residual fixes the first line pointwise; the already proved core
fixed-space calculation then gives C_V(L₁)=V₁. These identities also put
V in O₂(L₁). The rank-one quotient is the existing literal flag isomorphism.

These are the local action inputs used by the exceptional order-21 argument,
with the caller's flag and original quotient map retained throughout.
Source: Aschbacher–Smith, combined manuscript, 1 March 2004, 11.1.5,
printed p.766, using the flag geometry of pp.760–761.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix
open scoped MatrixGroups IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
namespace SL3
open Matrix.PSL3.LinearThree Matrix.PSL3.PointRadicalGeneration

private theorem point_displacements_generate {F : Type*} [Field F] [Finite F]
    (W : Subgroup (Multiplicative (Fin 3 → F)))
    (hm : ∀ t ∈ pointLocalSL F, ∀ v : Fin 3 → F,
      Multiplicative.ofAdd (t.val *ᵥ v - v) ∈ W) : W = ⊤ := by
  have hs (i : Fin 3) (b : F) : Multiplicative.ofAdd (Pi.single i b) ∈ W := by
    obtain ⟨j, hij, hj⟩ : ∃ j : Fin 3, i ≠ j ∧ j ≠ 0 := by
      fin_cases i
      · exact ⟨1, by decide, by decide⟩
      · exact ⟨2, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
    let t : SL(3,F) := SpecialLinearGroup.transvection hij b
    have ht : t ∈ pointLocalSL F := by
      apply (mem_pointLocalSL_iff F t).mpr
      simp [t, SpecialLinearGroup.transvection_coe, Matrix.single, hj]
    have hh := hm t ht (Pi.single j 1)
    have he : t.val *ᵥ Pi.single j 1 - Pi.single j 1 = Pi.single i b := by
      change t • (Pi.single j 1 : Fin 3 → F) - (Pi.single j 1 : Fin 3 → F) = _
      rw [SpecialLinearGroup.transvection_smul_single_snd]
      ext k
      simp [Pi.single_apply, smul_eq_mul]
    rwa [he] at hh
  apply top_unique
  intro v _
  have he : v = Multiplicative.ofAdd (Pi.single 0 (v.toAdd 0)) *
      Multiplicative.ofAdd (Pi.single 1 (v.toAdd 1)) *
      Multiplicative.ofAdd (Pi.single 2 (v.toAdd 2)) := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp
  rw [he]
  exact W.mul_mem (W.mul_mem (hs 0 _) (hs 1 _)) (hs 2 _)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- The literal point residual fully moves the original SL₃ seed. -/
theorem seed_commutator (f : InvariantFlag (Coordinates.sl3 m)) : ⁅V, f.Li 0⁆ = V := by
  obtain ⟨a, ha⟩ := exists_standardPoint_conjugator (f.space 0) (f.dimension 0)
  let q := PointCohomology.PointGeometry.SL3Core.componentMap D S m
  let ρ := specialLinearNatural (k := S.field.Carrier) 3
  let b : (Fin 3 → S.field.Carrier) ≃+ (Fin 3 → S.field.Carrier) :=
    { toFun := ρ a
      invFun := ρ a⁻¹
      left_inv := ρ.inv_self_apply a
      right_inv := ρ.self_inv_apply a
      map_add' := map_add (ρ a) }
  let e : V ≃* Multiplicative (Fin 3 → S.field.Carrier) :=
    (LocalGeometry.SL3.naturalEquiv D S m).trans b.toMultiplicative
  have hAV : f.Li 0 ≤ normalizer (V : Set G) :=
    ((localResidual_le _).trans inf_le_left).trans D.normalizes
  have hUV : ⁅f.Li 0,V⁆ ≤ V := le_normalizer_iff_commutator_le_right.mp hAV
  let U := ⁅f.Li 0,V⁆.subgroupOf V
  have hi := PointCohomology.PointGeometry.SL3Core.componentImage_residual_conjugate D S m f a ha
  have ht (t : SL(3,S.field.Carrier)) (ht : t ∈ pointLocalSL S.field.Carrier) :
      ∃ l : L, (l : G) ∈ f.Li 0 ∧ a * q l * a⁻¹ = t := by
    have hx : a⁻¹*t*a ∈ PointCohomology.PointGeometry.SL3Core.componentImage D S m (f.Li 0) := by
      rw [hi]
      exact ⟨t,ht,by simp⟩
    obtain ⟨l,hl,he⟩ := hx
    refine ⟨l,hl,?_⟩
    change q l = a⁻¹*t*a at he
    rw [he]
    group
  have hconj (l : L) (v : V) :
      (e (V.normalizerMonoidHom (inclusion D.normalizes l) v)).toAdd =
        ρ (a * q l * a⁻¹) (e v).toAdd := by
    change ρ a ((LocalGeometry.SL3.naturalEquiv D S m
      (V.normalizerMonoidHom (inclusion D.normalizes l) v)).toAdd) =
        ρ (a * q l * a⁻¹)
          (ρ a (LocalGeometry.SL3.naturalEquiv D S m v).toAdd)
    rw [LocalGeometry.SL3.naturalEquiv_conjugation]
    simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]
    change ρ a (ρ (q l) ((LocalGeometry.SL3.naturalEquiv D S m v).toAdd)) = _
    rfl
  have htop : U.map e.toMonoidHom = ⊤ := by
    apply point_displacements_generate
    intro t ht' w
    obtain ⟨l,hl,hlt⟩ := ht t ht'
    obtain ⟨v,hv⟩ := e.surjective (Multiplicative.ofAdd w)
    let d : V := V.normalizerMonoidHom (inclusion D.normalizes l) v * v⁻¹
    have hd : d ∈ U := commutator_mem_commutator hl v.property
    refine ⟨d,hd,?_⟩
    apply Multiplicative.toAdd.injective
    change (e d).toAdd = t.val *ᵥ w - w
    dsimp only [d]
    rw [map_mul,map_inv]
    change (e (V.normalizerMonoidHom (inclusion D.normalizes l) v)).toAdd +
      -(e v).toAdd = _
    rw [←sub_eq_add_neg]
    rw [hconj,hlt,hv]
    rfl
  have hU : U = ⊤ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [htop, map_top_of_surjective _ e.surjective]
  rw [commutator_comm V]
  have h := congrArg (Subgroup.map V.subtype) hU
  simpa only [U,map_subgroupOf_eq_of_le hUV, ← MonoidHom.range_eq_map, range_subtype] using h


/-- The point residual fixes the actual first field line, pointwise. -/
theorem first_centralizes_line (f : InvariantFlag (Coordinates.sl3 m)) :
    f.Li 0 ≤ centralizer (f.Vi 0 : Set G) := by
  obtain ⟨a, ha⟩ := exists_standardPoint_conjugator (f.space 0) (f.dimension 0)
  let q := PointCohomology.PointGeometry.SL3Core.componentMap D S m
  let ρ := specialLinearNatural (k := S.field.Carrier) 3
  have hi := PointCohomology.PointGeometry.SL3Core.componentImage_residual_conjugate D S m f a ha
  apply le_centralizer_iff.mpr
  intro v hv l hl
  let v' : V := ⟨v,D.centralQuotientPreimage_le _ hv⟩
  let l' : L := ⟨l,((localResidual_le _).trans inf_le_left) hl⟩
  let x := ((Coordinates.sl3 m).projection v').toAdd
  have hx : ρ a x ∈ standardPoint := by
    have hh := ((Coordinates.sl3 m).mem_preimage (f.space 0) v').mp hv
    rw [←ha,mem_conjugatePoint] at hh
    exact hh
  have hq : q l' ∈ PointCohomology.PointGeometry.SL3Core.componentImage D S m (f.Li 0) :=
    mem_map_of_mem q hl
  rw [hi] at hq
  obtain ⟨t,ht,he⟩ := hq
  have htx : ρ t (ρ a x) = ρ a x := by
    obtain ⟨h1,h2⟩ := (mem_standardPoint _).mp hx
    obtain ⟨h00,h10,h20⟩ := (mem_pointLocalSL_iff _ t).mp ht
    change t.val *ᵥ (ρ a x) = ρ a x
    ext i
    fin_cases i <;> simp [mulVec,dotProduct,Fin.sum_univ_three,h1,h2,h00,h10,h20]
  have heq : ρ (q l') x = x := by
    change a⁻¹ * t * a⁻¹⁻¹ = q l' at he
    rw [←he,inv_inv,map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,
      htx,Representation.inv_self_apply]
  have hh := (PointCohomology.PointGeometry.SL3Core.projection_fixed_iff D S m l' v').mp heq
  have hh' := congrArg Subtype.val hh
  change l * v * l⁻¹ = v at hh'
  exact mul_inv_eq_iff_eq_mul.mp hh'

/-- The same literal residual has exactly the first line as its fixed seed. -/
theorem seed_fixed_first (f : InvariantFlag (Coordinates.sl3 m)) :
    V ⊓ centralizer (f.Li 0 : Set G) = f.Vi 0 := by
  apply le_antisymm
  · exact (inf_le_inf_left V (centralizer_le (pCoreIn_le 2 (f.Li 0)))).trans
      (PointCohomology.PointGeometry.SL3Core.local_core_fixed D S m f).le
  · exact le_inf (D.centralQuotientPreimage_le _) (le_centralizer_iff.mp
      (first_centralizes_line D S m f))

/-- The original seed lies in the two-core of the original point residual. -/
theorem seed_le_first_core (f : InvariantFlag (Coordinates.sl3 m)) :
    V ≤ (f.Li 0).pCoreIn 2 := by
  let := D.elementary
  apply le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
  · exact (seed_commutator D S m f).ge.trans (le_normalizer_iff_commutator_le_right.mp
      (D.le_sylow.trans (f.sylow_normalizes_Li 0)))
  · exact ((localResidual_le _).trans inf_le_left).trans D.normalizes

/-- The source quotient name is witnessed by the original flag quotient isomorphism. -/
theorem first_isPSL (f : InvariantFlag (Coordinates.sl3 m)) :
    ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree) :=
  ⟨S.field.Carrier, inferInstance, inferInstance, S.field.card_eq,
    ⟨LocalGeometry.SL3.flagLocalCoreEquiv S m f 0⟩⟩

end SL3
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
