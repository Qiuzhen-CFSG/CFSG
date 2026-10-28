module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.Sp4Core.Comparison
import all CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.Sp4Core.Comparison
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoTerminal.Displacement

/-!
# Both original symplectic flag radicals

The plane-local automorphism kernel gives the same core identity as the
point-local calculation. Transport through the original quotient action
proves Rᵢ = O₂(Lᵢ)O₂(LT) at both indices. In the actual J₁ configuration,
the inner local action then gives T = T ∩ LO₂(LT).

The `import all` is an intentional companion-proof boundary: the plane
calculation uses the existing image definition, whose body is private.
Its public image and core statements remain unchanged.
Sp4Displacement and Sp4Cartan consume these literal identities.
Source: Aschbacher--Smith 3.3.16, p.591; 11.1.5, pp.765--766.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix
open scoped commutatorElement IsMulCommutative Pointwise
open Theory.SpecificGroups.SymplecticFour DiagramAutomorphisms
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.Sp4Terminal
open PointCohomology.PointGeometry.Sp4Core
section Model
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
/-- The plane local itself detects the diagram type of a normalizing actor. -/
private theorem preservesDiagram_of_planeLocal {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (a : MulAut (Sp F)) (ha : planeLocal.map a.toMonoidHom = planeLocal) :
    PreservesDiagram a := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  apply preservesDiagram_of_one_parabolic_class hq a
  apply Or.inr
  refine ⟨1,?_⟩
  rw [←planeLocal_normalizer hF hn,map_equiv_normalizer_eq,ha,map_one]
  exact (Subgroup.map_id _).symm

/-- Inside the full automorphism group, the plane-local core survives adjoining
any subgroup preserving that local. Diagram preservation is derived locally. -/
private theorem local_join_core_in_aut {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (U : Subgroup (MulAut (Sp F)))
    (hU : ∀ a ∈ U, planeLocal.map a.toMonoidHom = planeLocal) :
    ((planeLocal (F := F)).map MulAut.conj ⊔ U).pCoreIn 2 =
      ((planeLocal (F := F)).map MulAut.conj).pCoreIn 2 := by
  let K := (planeLocal (F := F)).map MulAut.conj
  have hnorm : U ≤ normalizer (K : Set (MulAut (Sp F))) := by
    intro a ha
    rw [mem_normalizer_iff_map_conj_eq]
    have he : (MulAut.conj a).toMonoidHom.comp MulAut.conj =
        MulAut.conj.comp a.toMonoidHom := by ext x y; simp
    change K.map (MulAut.conj a).toMonoidHom = K
    dsimp only [K]
    rw [Subgroup.map_map,he,←Subgroup.map_map,hU a ha]
  apply join_pCore_eq_of_quotient_action_detection 2 K U hnorm
  intro a ha htwo hc
  have hL := preserves_of_normalizes_inner planeLocal a
    ((sup_le K.le_normalizer hnorm) ha)
  obtain ⟨l,hl⟩ := planeSL2Action_kernel_of_preservesDiagram hF hn a
    (preservesDiagram_of_planeLocal hF hn a hL) hL htwo (by
      apply MulEquiv.ext
      intro A
      obtain ⟨l,rfl⟩ := Plane.quotientMap_surjective A
      rw [planeSL2Action_quotient]
      change Plane.quotientMap (restrict a planeLocal hL l) = Plane.quotientMap l
      rw [←planeLocalCoreQuotientEquiv_mk hF hn,←planeLocalCoreQuotientEquiv_mk hF hn]
      apply congrArg (planeLocalCoreQuotientEquiv hF hn)
      apply QuotientGroup.eq_iff_div_mem.mpr
      have hh := hc ⟨MulAut.conj l.val,mem_map_of_mem _ l.property⟩
      change ⁅a,MulAut.conj l.val⁆ ∈ K.pCoreIn 2 at hh
      have he : MulAut.conj (a l.val / l.val) = ⁅a,MulAut.conj l.val⁆ := by
        ext x
        simp [commutatorElement_def,div_eq_mul_inv,mul_assoc]
      rw [←map_pCoreIn_of_injective 2 planeLocal MulAut.conj inner_injective,←he] at hh
      have hm := (Subgroup.mem_map_iff_mem inner_injective).mp hh
      exact (Subgroup.mem_map_iff_mem planeLocal.subtype_injective).mp hm)
  exact hl ▸ mem_map_of_mem MulAut.conj l.property

end Model
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
  (a : Sp S.field.Carrier)
/-- The caller's original plane residual is the conjugate standard plane-local. -/
theorem modelImage_plane (f : InvariantFlag (Coordinates.sp4 m)) :
    modelImage D S m (f.Li 1) =
      planeLocal.map (MulAut.conj (Sp4.alignment m)).toMonoidHom := by
  have hf : f.space 1 = Sp4.space m 2 :=
    Sp4.space_inner_unique m 1 (f.space 1) (f.dimension 1)
      (inf_le_left.trans (f.invariant 1))
  change modelImage D S m (localResidual L ((Coordinates.sp4 m).preimage (f.space 1))) = _
  rw [modelImage_residual,hf]
  let R (A : Subgroup (Sp S.field.Carrier)) := (solvableResidual A).map A.subtype
  have hp := congrArg (fun A : Subgroup (Coordinates.sp4 m).ModelGroup =>
    (solvableResidual A).map A.subtype) (Sp4.modelStabilizer_space m 1)
  apply hp.trans
  change R ((planeParabolic (F := S.field.Carrier)).map
    (MulAut.conj (Sp4.alignment m)).toMonoidHom) = _
  let A := planeParabolic (F := S.field.Carrier)
  let e := MulAut.conj (Sp4.alignment m)
  let j := e.subgroupMap A
  have hm := congrArg (Subgroup.map (A.map e.toMonoidHom).subtype)
    (map_solvableResidual_eq j.toMonoidHom j.surjective)
  have hc : (A.map e.toMonoidHom).subtype.comp j.toMonoidHom =
      e.toMonoidHom.comp A.subtype := rfl
  have he : (R A).map e.toMonoidHom = R (A.map e.toMonoidHom) := by
    change ((solvableResidual A).map j.toMonoidHom).map (A.map e.toMonoidHom).subtype =
      (solvableResidual (A.map e.toMonoidHom)).map (A.map e.toMonoidHom).subtype at hm
    change ((solvableResidual A).map A.subtype).map e.toMonoidHom = _
    rw [Subgroup.map_map,hc] at hm
    rw [Subgroup.map_map]
    exact hm
  rw [←he]
  change ((solvableResidual (planeParabolic (F := S.field.Carrier))).map
    planeParabolic.subtype).map e.toMonoidHom = _
  rw [planeParabolic_solvableResidual_eq S.field.card_eq S.nonbinary]

/-- Rotate the original invariant plane to the standard plane local. -/
theorem image_plane_residual (f : InvariantFlag (Coordinates.sp4 m)) :
    image D S m (Sp4.alignment m)⁻¹ (f.Li 1) =
      (planeLocal (F := S.field.Carrier)).map MulAut.conj := by
  have hL : f.Li 1 ≤ L := (localResidual_le _).trans inf_le_left
  rw [image_component D S m (Sp4.alignment m)⁻¹ (f.Li 1) hL,modelImage_plane]
  have he : (MulAut.conj (Sp4.alignment m)⁻¹).toMonoidHom.comp
      (MulAut.conj (Sp4.alignment m)).toMonoidHom = MonoidHom.id (Sp S.field.Carrier) := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [Subgroup.map_map _ (MulAut.conj (Sp4.alignment m)⁻¹).toMonoidHom,he,Subgroup.map_id]

private theorem image_sup (A B : Subgroup G)
    (hA : A ≤ L ⊔ (T : Subgroup G)) (hB : B ≤ L ⊔ (T : Subgroup G)) :
    image D S m a (A ⊔ B) = image D S m a A ⊔ image D S m a B := by
  unfold image
  rw [subgroupOf_sup hA hB,Subgroup.map_sup]

/-- The full outer Sylow supplement introduces no new plane-local core image. -/
theorem plane_radical_image_le_local_core (f : InvariantFlag (Coordinates.sp4 m)) :
    image D S m (Sp4.alignment m)⁻¹ (f.Ri 1) ≤
      image D S m (Sp4.alignment m)⁻¹ ((f.Li 1).pCoreIn 2) := by
  let a := (Sp4.alignment m)⁻¹
  have hL : f.Li 1 ≤ L := (localResidual_le _).trans inf_le_left
  have hlocal := image_plane_residual D S m f
  have hn := image_normalizes D S m a (f.Li 1) (T : Subgroup G) (f.sylow_normalizes_Li 1)
  change image D S m a (f.Li 1) = _ at hlocal
  rw [hlocal] at hn
  have hc := local_join_core_in_aut S.field.card_eq S.nonbinary
    (image D S m a (T : Subgroup G))
    (fun b hb => preserves_of_normalizes_inner _ b (hn hb))
  rw [component_image_core D S m a (f.Li 1) hL,hlocal]
  change image D S m a ((f.Li 1 ⊔ (T : Subgroup G)).pCoreIn 2) ≤ _
  have hh := core_image_le D S m a (f.Li 1 ⊔ (T : Subgroup G))
    (sup_le (hL.trans le_sup_left) le_sup_right)
  rw [image_sup D S m a _ _ (hL.trans le_sup_left) le_sup_right,hlocal,hc] at hh
  exact hh

/-- The exact original radical product, with no splitting of its central kernel. -/
theorem plane_core_product (f : InvariantFlag (Coordinates.sp4 m)) :
    f.Ri 1 = (f.Li 1).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let a := (Sp4.alignment m)⁻¹
  have hRT : f.Ri 1 ≤ (T : Subgroup G) := by
    change (f.Li 1 ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (f.Li 1 ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hWR : (f.Li 1).pCoreIn 2 ≤ f.Ri 1 :=
    pCoreIn_mono_of_normalizes le_sup_left
      (sup_le (f.Li 1).le_normalizer (f.sylow_normalizes_Li 1))
  apply le_antisymm
  · intro r hr
    let r' : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨r,mem_sup_right (hRT hr)⟩
    obtain ⟨w,hw,he⟩ := plane_radical_image_le_local_core D S m f ⟨r',hr,rfl⟩
    have hk : r' * w⁻¹ ∈ (quotientAction D S m a).ker := by
      change quotientAction D S m a (r' * w⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hd : r * (w : G)⁻¹ ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
      sylow_inf_quotient_kernel_le_core D S m a
        ⟨(T : Subgroup G).mul_mem (hRT hr) ((T : Subgroup G).inv_mem (hRT (hWR hw))),
          r' * w⁻¹,hk,rfl⟩
    have hh := ((f.Li 1).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2).mul_mem
      (mem_sup_right hd) (mem_sup_left hw)
    change r * (w : G)⁻¹ * (w : G) ∈ _ at hh
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
  · apply sup_le hWR
    have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
        pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    intro q hq
    exact inf_pCoreIn_le_of_le 2
      (sup_le (((localResidual_le _).trans inf_le_left).trans le_sup_left) le_sup_right)
      ⟨mem_sup_right (hQT hq),hq⟩

/-- The automorphism image of either original radical is the local two-core. -/
theorem flag_radical_image_le_local_core (f : InvariantFlag (Coordinates.sp4 m)) (i : Fin 2) :
    image D S m (Sp4.alignment m)⁻¹ (f.Ri i) ≤
      image D S m (Sp4.alignment m)⁻¹ ((f.Li i).pCoreIn 2) := by
  fin_cases i
  · exact radical_image_le_local_core D S m f
  · exact plane_radical_image_le_local_core D S m f

/-- Both original radicals retain the full outer Sylow action. -/
theorem flag_core_product (f : InvariantFlag (Coordinates.sp4 m)) (i : Fin 2) :
    f.Ri i = (f.Li i).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  fin_cases i
  · exact PointCohomology.PointGeometry.Sp4Core.core_product D S m f
  · exact plane_core_product D S m f

/-- The inner local action removes the outer factor of the original Sylow. -/
theorem sourceTL_eq_sylow {f : InvariantFlag (Coordinates.sp4 m)}
    {A : OddSupplement T} (E : JankoConfiguration S f A) :
    sourceTL T L = (T : Subgroup G) := by
  apply le_antisymm inf_le_left
  have hL : f.Li E.index ≤ L := (localResidual_le _).trans inf_le_left
  have hR : f.Ri E.index ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [flag_core_product D S m f E.index]
    exact sup_le (((pCoreIn_le 2 (f.Li E.index)).trans hL).trans le_sup_left) le_sup_right
  exact le_inf le_rfl (E.sylow_eq_intersection_sup_radical.le.trans
    (sup_le ((inf_le_right.trans hL).trans le_sup_left) hR))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.Sp4Terminal
