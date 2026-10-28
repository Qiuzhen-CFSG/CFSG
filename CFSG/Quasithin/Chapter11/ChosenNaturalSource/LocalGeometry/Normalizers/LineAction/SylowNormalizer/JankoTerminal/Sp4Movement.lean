module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoTerminal.Sp4Cartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoTerminal.Sp4Displacement
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.FixedRadical

/-!
# Residual movement of the original symplectic displacement

Suppose the selected residual centralizes Q = [X,T]. On the marked
natural module, every displacement (x-1)V then lies in the residual's
fixed space. Explicit parabolic shears put that fixed space in a totally
isotropic plane. Preservation of the symplectic form in characteristic
two forces x²=1, while the actual Cartan gives x³=1. Thus x=1 on the
natural quotient; its odd order removes the two-core kernel. This would
make X trivial, contradicting the proved section-centralizer calculation.

The final theorem combines this movement with the actual displacement
bound. Shortness remains with qt-c132-nonbinary-symplectic; its discharge
and the line-action assembly stay with qt-d-1222-natural-line-action.
Source: Aschbacher--Smith 3.3.16, printed p.591.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix
open scoped commutatorElement IsMulCommutative Pointwise
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.Sp4Terminal
open PointCohomology.PointGeometry.Sp4Core
section Model
variable {F : Type*} [Field F] [CharP F 2]

private def diagonalShear (i : Fin 2) : Plane.symmetricMatrices F :=
  ⟨Matrix.diagonal (Pi.single i 1), Matrix.isSymm_diagonal _⟩

omit [CharP F 2] in
private theorem shear_pointLocal (i : Fin 2) :
    (Plane.shear (diagonalShear (F := F) i)).val ∈ pointLocal := by
  rw [mem_pointLocal_iff_fixed]
  ext j
  cases j <;> simp [Plane.shear,Plane.shearSp,Theory.SpecificGroups.SymplecticFour.e,
    Fintype.sum_sum_type,Matrix.one_apply]

omit [CharP F 2] in
private theorem local_fixed_le_plane (i : Fin 2) (v : Vector F)
    (hf : ∀ y ∈ (if i = 0 then pointLocal else planeLocal : Subgroup (Sp F)), y • v = v) :
    v ∈ plane F := by
  intro j
  have hh : (Plane.shear (diagonalShear (F := F) j)).val • v = v := by
    apply hf
    split_ifs
    · exact shear_pointLocal j
    · exact (Plane.shear (diagonalShear (F := F) j)).property
  have he := congrFun hh (.inl j)
  fin_cases j <;>
    simpa [Plane.shear,Plane.shearSp,diagonalShear,Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,Matrix.mulVec,
      dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.diagonal,Pi.single_apply] using he

omit [CharP F 2] in
private theorem local_fixed_isotropic (i : Fin 2) (u v : Vector F)
    (hu : ∀ y ∈ (if i = 0 then pointLocal else planeLocal : Subgroup (Sp F)), y • u = u)
    (hv : ∀ y ∈ (if i = 0 then pointLocal else planeLocal : Subgroup (Sp F)), y • v = v) :
    form F u v = 0 := by
  have hpu : ∀ j, u (.inr j) = 0 := local_fixed_le_plane i u hu
  have hpv : ∀ j, v (.inr j) = 0 := local_fixed_le_plane i v hv
  simp [form_apply,hpu,hpv]

private theorem cube_eq_one_of_isotropic_displacement (g : Sp F) (hc : g^3=1)
    (hi : ∀ u v : Vector F, form F (g • u-u) (g • v-v) = 0) : g = 1 := by
  have hcross (u v : Vector F) : form F (g • u) v = form F u (g • v) := by
    have hh := hi u v
    simp only [map_sub,LinearMap.sub_apply,preserves_form] at hh
    have hz : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination -hh + (form F u v - form F u (g • v)) * hz
  have hsq (u : Vector F) : g • (g • u) = u := by
    apply sub_eq_zero.mp
    apply TwoLocalCover.form_nondegenerate.1
    intro v
    have hh := hcross (g • u) v
    rw [preserves_form] at hh
    rw [map_sub,LinearMap.sub_apply]
    exact sub_eq_zero.mpr hh
  have hs : g^2=1 := by
    apply Subtype.ext
    ext i j
    have hh := congrFun (hsq (Pi.single j 1)) i
    simp only [Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec] at hh
    rw [Matrix.mulVec_mulVec] at hh
    simpa [Matrix.mulVec_single,Matrix.one_apply,Pi.single_apply,pow_two] using hh
  rw [pow_succ,hs,one_mul] at hc
  exact hc
end Model

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

private theorem residual_fixed_isotropic (f : InvariantFlag (Coordinates.sp4 m))
    (i : Fin 2) (u v : Vector S.field.Carrier)
    (hu : ∀ y ∈ modelImage D S m (f.Li i), y • u = u)
    (hv : ∀ y ∈ modelImage D S m (f.Li i), y • v = v) :
    form S.field.Carrier u v = 0 := by
  have he : modelImage D S m (f.Li i) =
      (if i=0 then pointLocal else planeLocal).map (MulAut.conj (Sp4.alignment m)).toMonoidHom := by
    fin_cases i
    · exact modelImage_point D S m f
    · exact modelImage_plane D S m f
  have hh (w : Vector S.field.Carrier)
      (hw : ∀ y ∈ modelImage D S m (f.Li i), y • w = w) :
      ∀ y ∈ (if i=0 then pointLocal else planeLocal : Subgroup (Sp S.field.Carrier)),
        y • ((Sp4.alignment m)⁻¹ • w) = (Sp4.alignment m)⁻¹ • w := by
    intro y hy
    have h := hw (MulAut.conj (Sp4.alignment m) y) (he ▸ mem_map_of_mem _ hy)
    have hh := congrArg (fun z => (Sp4.alignment m)⁻¹ • z) h
    simpa only [MulAut.conj_apply,mul_smul,inv_smul_smul] using hh
  have hi := local_fixed_isotropic i _ _ (hh u hu) (hh v hv)
  rwa [preserves_form] at hi

private theorem commutator_projection (x : L) (v : V) :
    ∃ w : V, (w : G) = ⁅(x : G),(v : G)⁆ ∧
      ((Coordinates.sp4 m).projection w).toAdd =
        (show Sp S.field.Carrier from (Coordinates.sp4 m).quotientMap x) •
          (show Vector S.field.Carrier from ((Coordinates.sp4 m).projection v).toAdd) -
          (show Vector S.field.Carrier from ((Coordinates.sp4 m).projection v).toAdd) := by
  let c := Coordinates.sp4 m
  let w := V.normalizerMonoidHom (inclusion D.normalizes x) v * v⁻¹
  refine ⟨w,rfl,?_⟩
  change (c.projection (V.normalizerMonoidHom (inclusion D.normalizes x) v * v⁻¹)).toAdd = _
  rw [map_mul,map_inv,toAdd_mul,toAdd_inv,
    c.projection_component_conjugation]
  simp only [sub_eq_add_neg]
  rfl

private theorem central_projection_fixed (f : InvariantFlag (Coordinates.sp4 m))
    (i : Fin 2) (w : V) (hw : (w : G) ∈ centralizer (f.Li i : Set G)) :
    ∀ y ∈ modelImage D S m (f.Li i),
      y • (show Vector S.field.Carrier from ((Coordinates.sp4 m).projection w).toAdd) = ((Coordinates.sp4 m).projection w).toAdd := by
  rintro y ⟨l,hl,rfl⟩
  have hh : V.normalizerMonoidHom (inclusion D.normalizes l) w = w := by
    apply Subtype.ext
    change (l : G) * (w : G) * (l : G)⁻¹ = w
    rw [mem_centralizer_iff.mp hw l hl,mul_inv_cancel_right]
  have he := (Coordinates.sp4 m).projection_component_conjugation l w
  rw [hh] at he
  exact he.symm

/-- The actual residual acts nontrivially on the actual displacement. -/
theorem residual_moves_displacement {f : InvariantFlag (Coordinates.sp4 m)}
    {A : OddSupplement T} (E : JankoConfiguration S f A) :
    ¬ f.Li E.index ≤ centralizer (E.displacement : Set G) := by
  intro hc
  apply section_ne_bot D S m E
  apply bot_unique
  intro x hx
  let xL : L := ⟨x,hx.1.2⟩
  let c := Coordinates.sp4 m
  have hcub : c.quotientMap xL ^ 3 = 1 := by
    have hh := congrArg (fun y : (A.subgroup ⊓ L : Subgroup G) => (y : G))
      (intersection_cube D S m E ⟨x,hx.1⟩)
    have hh' : xL^3=1 := Subtype.ext hh
    rw [←map_pow,hh',map_one]
  have hi : c.quotientMap xL = 1 := by
    apply cube_eq_one_of_isotropic_displacement _ hcub
    intro u v
    obtain ⟨u',hu⟩ := c.projection_surjective (Multiplicative.ofAdd u)
    obtain ⟨v',hv⟩ := c.projection_surjective (Multiplicative.ofAdd v)
    obtain ⟨du,hdu,hpu⟩ := commutator_projection D S m xL u'
    obtain ⟨dv,hdv,hpv⟩ := commutator_projection D S m xL v'
    have hd (w : V) (d : V) (he : (d : G) = ⁅x,(w : G)⁆) :
        (d : G) ∈ centralizer (f.Li E.index : Set G) := by
      apply le_centralizer_iff.mp hc
      rw [he]
      exact commutator_mem_commutator hx (D.le_sylow w.property)
    have hh := residual_fixed_isotropic D S m f E.index _ _
      (central_projection_fixed D S m f E.index du (hd u' du hdu))
      (central_projection_fixed D S m f E.index dv (hd v' dv hdv))
    rw [hpu,hpv,hu,hv] at hh
    exact hh
  have hxP : xL ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact m.groupEquiv.injective (hi.trans m.groupEquiv.map_one.symm)
  have hxT : x ∈ (T : Subgroup G) := by
    have hp := pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] at hp
    exact hp (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component) (mem_map_of_mem L.subtype hxP))
  exact A.disjoint.eq_bot ▸ (show x ∈ (T : Subgroup G) ⊓ A.subgroup from ⟨hxT,hx.1.1⟩)

/-- The Sp₄ terminal contradiction now retains only genuine shortness. -/
theorem false_of_short {f : InvariantFlag (Coordinates.sp4 m)}
    {A : OddSupplement T} (E : JankoConfiguration S f A) (hb : ChapterC.IsShort L) : False :=
  false_of_short_moved_displacement D S m E hb (residual_moves_displacement D S m E)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.Sp4Terminal
