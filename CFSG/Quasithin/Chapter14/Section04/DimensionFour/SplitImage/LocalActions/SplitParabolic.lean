module

public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.SelectedAssembly
public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.NaturalModel
public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.InvolutionGeometry
public import CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.LocalActions.Inputs

/-!
# The split Sylow calculation in the literal ambient normalizer quotient

An injective map of the unitriangular model carries its actual elementary
Thompson subgroup to the Thompson subgroup of the image. This constructs
its order-sixteen coordinates, central point, normalizer elements and the
two generators in N_G(A)/C_G(A), with the published row and column actions.
The elementary subgroup is not an input.

A genuine complement and an equivariant natural-module identification
construct the flagged Sylow and both marked residual parabolics through the
original quotient map. `Natural.generators` constructs ParabolicGenerators
on the actual J(T_L); `Natural.sourceGenerators` uses the original nontrivial
central point z. The second actor is L₂T_L, not L₂ alone.

`Natural.exists_source_involution` selects an actual involution in W^g − U,
where W is the relative centralizer C_U(V₂), proves its a₂ square-quotient
action on the original quaternion core, and proves A = <a,[U,a]>.
`Natural.core_sup_X` identifies U W^g with the constructed Sylow. The
selection applies for each g in the marked line preimage outside the point
preimage. Membership in W^g − U alone does not give the generation assertion
for every representative; no elementary-exponent assumption on W^g is used.
The full ambient source splitting exclusion remains with the parent assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
14.4.4, printed p.1007.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.SplitParabolic
open Matrix.PSL3Two.SplitParabolic
variable {G : Type*} [Group G] (f : Unitriangular.T →* G) (hf : Function.Injective f)

abbrev A := Unitriangular.A.map f

include hf in
theorem thompson_eq : Stellmacher.elementaryAbelianMaxJ f.range = A f := by
 rw [MonoidHom.range_eq_map, Stellmacher.elementaryAbelianMaxJ_map_injective f hf,
  Unitriangular.thompson_eq]

include hf in
theorem card_A : Nat.card (A f) = 16 := by
 rw [A, card_map_of_injective hf, Unitriangular.card_A]

theorem elementary_A : IsElementaryAbelian 2 (A f) :=
 (inferInstance : IsElementaryAbelian 2 Unitriangular.A).map f

noncomputable def coordinates : A f ≃* BinaryFourSplitPair.E :=
 (Unitriangular.A.equivMapOfInjective f hf).symm.trans Unitriangular.coordinates

def marked : A f := ⟨f Unitriangular.z, mem_map_of_mem f Unitriangular.z_mem_A⟩

theorem coordinates_marked : coordinates f hf (marked f) = BinaryFourSplitPair.point := by
 change Unitriangular.coordinates
  ((Unitriangular.A.equivMapOfInjective f hf).symm
   ((Unitriangular.A.equivMapOfInjective f hf) ⟨Unitriangular.z, Unitriangular.z_mem_A⟩)) = _
 rw [MulEquiv.symm_apply_apply]
 exact Unitriangular.coordinates_z

include hf in
theorem marked_ne_one : marked f ≠ 1 := by
 intro h
 have he : f Unitriangular.z = 1 := congrArg (fun x : A f => (x : G)) h
 exact Unitriangular.z_ne_one (hf (he.trans f.map_one.symm))

theorem marked_central (x : f.range) : (marked f : G) * x = x * (marked f : G) := by
 obtain ⟨y,hy⟩ := x.property
 change f Unitriangular.z * (x : G) = (x : G) * f Unitriangular.z
 rw [← hy, ← map_mul, ← map_mul]
 exact congrArg f ((mem_center_iff.mp Unitriangular.z_central y).symm)

include hf in
theorem selected_involution : f Unitriangular.a ∈ Unitriangular.W.map f ∧
 f Unitriangular.a ∉ Unitriangular.U.map f ∧ (f Unitriangular.a)^2 = 1 := by
 refine ⟨mem_map_of_mem f Unitriangular.a_selected.1, ?_, ?_⟩
 · intro h
   exact Unitriangular.a_selected.2.1 ((mem_map_iff_mem hf).mp h)
 · rw [← map_pow, Unitriangular.a_selected.2.2, map_one]

theorem selected_generation :
 zpowers (f Unitriangular.a) ⊔ ⁅Unitriangular.U.map f, zpowers (f Unitriangular.a)⁆ = A f := by
 rw [← MonoidHom.map_zpowers, ← map_commutator, ← Subgroup.map_sup, Unitriangular.a_generates]

theorem normalizes : f.range ≤ normalizer (A f : Set G) := by
 rintro _ ⟨x,rfl⟩
 exact le_normalizer_map f ⟨x, by rw [Unitriangular.A.normalizer_eq_top]; trivial, rfl⟩

def normalizerMap : Unitriangular.T →* normalizer (A f : Set G) :=
 f.codRestrict _ (fun x => normalizes f ⟨x,rfl⟩)
def quotientMap : Unitriangular.T →* NormalizerAction.Star (A f) :=
 (NormalizerAction.quotient (A f)).comp (normalizerMap f)

theorem middle_mem (v : BinaryFourSplitPair.E) : Unitriangular.middle v ∈ Unitriangular.A := ⟨rfl,rfl⟩

theorem coordinates_middle (v : BinaryFourSplitPair.E) :
 coordinates f hf ⟨f (Unitriangular.middle v), mem_map_of_mem f (middle_mem v)⟩ = v := by
 change Unitriangular.coordinates
  ((Unitriangular.A.equivMapOfInjective f hf).symm
    ((Unitriangular.A.equivMapOfInjective f hf) (Unitriangular.coordinates.symm v))) = v
 rw [MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

private theorem conjugation_formula (x : Unitriangular.T)
 (v : BinaryFourSplitPair.E) :
 coordinateAction (A f) (coordinates f hf) (quotientMap f x) v =
 coordinates f hf ⟨f x * f (Unitriangular.middle v) * (f x)⁻¹,
   (A f).normalizerMonoidHom (normalizerMap f x)
    ⟨f (Unitriangular.middle v), mem_map_of_mem f (middle_mem v)⟩ |>.property⟩ := by
 rfl

theorem row_action : coordinateAction (A f) (coordinates f hf)
 (quotientMap f Unitriangular.r) = BinaryFourSplitPair.row := by
 apply MulEquiv.ext
 intro v
 rw [conjugation_formula]
 have he : f Unitriangular.r * f (Unitriangular.middle v) * (f Unitriangular.r)⁻¹ =
    f (Unitriangular.middle (BinaryFourSplitPair.row v)) := by
  rw [← map_inv, ← map_mul, ← map_mul, Unitriangular.row_action]
 simp only [he]
 exact coordinates_middle f hf _

theorem column_action : coordinateAction (A f) (coordinates f hf)
 (quotientMap f Unitriangular.q) = BinaryFourSplitPair.column := by
 apply MulEquiv.ext
 intro v
 rw [conjugation_formula]
 have he : f Unitriangular.q * f (Unitriangular.middle v) * (f Unitriangular.q)⁻¹ =
    f (Unitriangular.middle (BinaryFourSplitPair.column v)) := by
  rw [← map_inv, ← map_mul, ← map_mul, Unitriangular.column_action]
 simp only [he]
 exact coordinates_middle f hf _

private theorem quotientMap_middle (v : BinaryFourSplitPair.E) :
 quotientMap f (Unitriangular.middle v) = 1 := by
 apply (NormalizerAction.quotient_eq_one_iff (A f) _).mpr
 let _ := elementary_A f
 intro y hy
 exact congrArg Subtype.val
  (mul_comm (⟨y,hy⟩ : A f) ⟨f (Unitriangular.middle v),mem_map_of_mem f (middle_mem v)⟩)

theorem quotientImage_range : quotientImage (A f) f.range = (quotientMap f).range := by
 ext t
 constructor
 · rintro ⟨n,hn,rfl⟩
   obtain ⟨x,hx⟩ := hn
   refine ⟨x,?_⟩
   exact congrArg (NormalizerAction.quotient (A f)) (Subtype.ext hx)
 · rintro ⟨x,rfl⟩
   exact ⟨normalizerMap f x, ⟨x,rfl⟩, rfl⟩

theorem sylow_generators : quotientImage (A f) f.range =
 closure {quotientMap f Unitriangular.r, quotientMap f Unitriangular.q} := by
 rw [quotientImage_range]
 apply le_antisymm
 · rintro _ ⟨x,rfl⟩
   rw [Unitriangular.normal_form x, map_mul, map_mul, map_pow, map_pow, quotientMap_middle, one_mul]
   exact mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _)
 · apply (closure_le _).mpr
   intro t ht
   rcases (show t=quotientMap f Unitriangular.r ∨ t=quotientMap f Unitriangular.q from by simpa using ht) with rfl | rfl
   · exact ⟨Unitriangular.r,rfl⟩
   · exact ⟨Unitriangular.q,rfl⟩
/-- The split Sylow converse applies to every *involution* outside U.
Membership outside U alone is insufficient. The source must supply such
an involution in W^g; the model calculation does not assume W^g elementary. -/
theorem model_converse_for_involution
    (d : QuaternionCentralProductData Unitriangular.U)
    (x : Unitriangular.T) (hxU : x ∉ Unitriangular.U) (hx2 : x^2=1) :
 d.IsA2Action (Unitriangular.U.normalizerMonoidHom
   ⟨x, by rw [Unitriangular.U.normalizer_eq_top]; trivial⟩) ∧
 Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup Unitriangular.T) =
   zpowers x ⊔ ⁅Unitriangular.U,zpowers x⁆ := by
 have hxA := Unitriangular.outside_involution_mem_middle x hxU hx2
 exact ⟨Unitriangular.a2_of_mem_A_outside d x hxA hxU,
   Unitriangular.thompson_eq.trans (Unitriangular.generation_of_mem_A_outside x hxA hxU).symm⟩

end CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.SplitParabolic

end

public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.SplitParabolic
open Matrix.PSL3Two.SplitParabolic
variable {G : Type*} [Group G] (f : Unitriangular.T →* G) (hf : Function.Injective f)

private theorem quotientImage_sup' (B P Q : Subgroup G)
 (hP : P ≤ normalizer (B : Set G)) (hQ : Q ≤ normalizer (B : Set G)) :
 quotientImage B (P ⊔ Q) = quotientImage B P ⊔ quotientImage B Q := by
 rw [quotientImage, subgroupOf_sup hP hQ, Subgroup.map_sup]
 rfl

private theorem quotientImage_zpowers' (B : Subgroup G) (b : normalizer (B : Set G)) :
 quotientImage B (zpowers (b : G)) = zpowers (NormalizerAction.quotient B b) := by
 have he : (zpowers (b : G)).subgroupOf (normalizer (B : Set G)) = zpowers b := by
  apply Subgroup.map_injective (normalizer (B : Set G)).subtype_injective
  rw [map_subgroupOf_eq_of_le (zpowers_le.mpr b.property), MonoidHom.map_zpowers]
  rfl
 rw [quotientImage, he, MonoidHom.map_zpowers]

private theorem three_closure (H : Type*) [Group H] (r q b : H) :
 closure {r,q} ⊔ zpowers b = closure {r,q,b} := by
 rw [zpowers_eq_closure, ← Subgroup.closure_union]
 congr 1
 ext x
 simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
 tauto

private noncomputable def withCubic (b : normalizer (A f : Set G))
 (hb : ∀ v, (b : G) * f (Unitriangular.middle v) * (b : G)⁻¹ =
    f (Unitriangular.middle (BinaryFourSplitPair.columnCubic v))) :
 ParabolicGenerators (A f) (zpowers (b : G)) f.range (marked f) where
 coordinates := coordinates f hf
 point_eq := coordinates_marked f hf
 normalizes := sup_le (zpowers_le.mpr b.property) (normalizes f)
 r := quotientMap f Unitriangular.r
 q := quotientMap f Unitriangular.q
 b := NormalizerAction.quotient (A f) b
 sylow_generators := sylow_generators f
 parabolic_generators := by
  rw [sup_comm, quotientImage_sup' _ _ _ (normalizes f) (zpowers_le.mpr b.property),
   sylow_generators f, quotientImage_zpowers', three_closure]
 row_action := row_action f hf
 column_action := column_action f hf
 cubic_action := by
  apply MulEquiv.ext
  intro v
  change coordinates f hf ((A f).normalizerMonoidHom b ((coordinates f hf).symm v)) = _
  have hv : (coordinates f hf).symm v =
   ⟨f (Unitriangular.middle v),mem_map_of_mem f (middle_mem v)⟩ := by
   apply (coordinates f hf).injective
   rw [MulEquiv.apply_symm_apply, coordinates_middle]
  rw [hv]
  change coordinates f hf ⟨(b : G) * f (Unitriangular.middle v) * (b : G)⁻¹,_⟩ = _
  simp only [hb]
  exact coordinates_middle f hf _

end CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.SplitParabolic

namespace CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.SplitParabolic.Natural
open Subgroup Matrix.PSL3Two Matrix.PSL3Two.SplitParabolic
variable {L G : Type*} [Group L] [Group G] {V : Subgroup L} [V.Normal]
 (d : SplitNaturalData V) (i : L →* G) (hi : Function.Injective i)

@[expose] noncomputable def embedding : Unitriangular.T →* G := i.comp d.unitriangularMap

include hi in
theorem embedding_injective : Function.Injective (embedding d i) :=
 hi.comp d.unitriangularMap_injective

@[expose] def TL : Subgroup G := (d.markedPreimage borelSL).map i

/-- The source T_L really is Sylow in L, before its ambient embedding. -/
noncomputable def sylow : Sylow 2 L :=
 naturalSylow.mapSurjective (f := d.blockEquiv.symm.toMonoidHom) d.blockEquiv.symm.surjective

theorem sylow_coe : (sylow d : Subgroup L) = d.markedPreimage borelSL := by
 change standardSylow.map d.blockEquiv.symm.toMonoidHom = _
 exact (d.markedPreimage_eq_map borelSL).symm

theorem sylow_map : (sylow d : Subgroup L).map i = TL d i := by
 rw [sylow_coe]
 rfl

@[expose] def firstParabolic : Subgroup G :=
 ((pResidual 2 (d.markedPreimage pointParabolicSL)).map
  (d.markedPreimage pointParabolicSL).subtype).map i

@[expose] def secondParabolic : Subgroup G :=
 ((pResidual 2 (d.markedPreimage lineParabolicSL)).map
  (d.markedPreimage lineParabolicSL).subtype).map i

theorem embedding_range : (embedding d i).range = TL d i := by
 rw [embedding,MonoidHom.range_comp,d.unitriangularMap_range]
 rfl

include hi in
theorem core_image : Unitriangular.U.map (embedding d i) = (firstParabolic d i).pCoreIn 2 := by
 rw [embedding,← Subgroup.map_map,d.U_image_residual_core,
  map_pCoreIn_of_injective 2 _ i hi]
 rfl

include hi in
theorem thompson_image : Stellmacher.elementaryAbelianMaxJ (TL d i) = A (embedding d i) := by
 rw [← embedding_range]
 exact thompson_eq _ (embedding_injective d i hi)

include hi in
theorem card_thompson : Nat.card (Stellmacher.elementaryAbelianMaxJ (TL d i)) = 16 := by
 rw [thompson_image d i hi]
 exact card_A _ (embedding_injective d i hi)

include hi in
theorem elementary_thompson : IsElementaryAbelian 2 (Stellmacher.elementaryAbelianMaxJ (TL d i)) := by
 rw [thompson_image d i hi]
 exact elementary_A _

@[expose] noncomputable def point : Stellmacher.elementaryAbelianMaxJ (TL d i) :=
 ⟨embedding d i Unitriangular.z, by
  rw [thompson_image d i hi]
  exact mem_map_of_mem _ Unitriangular.z_mem_A⟩

theorem point_ne_one : point d i hi ≠ 1 := by
 intro h
 apply marked_ne_one (embedding d i) (embedding_injective d i hi)
 exact Subtype.ext (congrArg (fun x : Stellmacher.elementaryAbelianMaxJ (TL d i) => (x : G)) h)

theorem point_central (x : TL d i) : (point d i hi : G) * x = x * (point d i hi : G) := by
 apply marked_central (embedding d i) ⟨x,?_⟩
 rw [embedding_range]
 exact x.property

theorem actor_eq : secondParabolic d i ⊔ TL d i =
 (embedding d i).range ⊔ zpowers (i (d.blockEquiv.symm cubicLift)) := by
 have h := congrArg (fun P : Subgroup L => P.map i) d.residual_actor_generators
 rw [Subgroup.map_sup,Subgroup.map_sup,MonoidHom.map_zpowers] at h
 rw [secondParabolic,← embedding_range,embedding,MonoidHom.range_comp]
 exact h

theorem actor_normalizes : secondParabolic d i ⊔ TL d i ≤
 normalizer (A (embedding d i) : Set G) := by
 have h := (map_mono d.residual_actor_normalizes (f := i)).trans (le_normalizer_map i)
 rw [Subgroup.map_sup] at h
 simpa only [A,embedding,secondParabolic,TL,← Subgroup.map_map,MonoidHom.range_comp,
  d.unitriangularMap_range] using h

noncomputable def cubic : normalizer (A (embedding d i) : Set G) :=
 ⟨i (d.blockEquiv.symm cubicLift),by
  apply actor_normalizes d i
  rw [actor_eq]
  exact (show zpowers (i (d.blockEquiv.symm cubicLift)) ≤ _ from le_sup_right) (mem_zpowers _)⟩

theorem cubic_equation (v : BinaryFourSplitPair.E) :
 (cubic d i : G) * embedding d i (Unitriangular.middle v) * (cubic d i : G)⁻¹ =
 embedding d i (Unitriangular.middle (BinaryFourSplitPair.columnCubic v)) := by
 change i (d.blockEquiv.symm cubicLift) * i (d.unitriangularMap (Unitriangular.middle v)) *
  (i (d.blockEquiv.symm cubicLift))⁻¹ = i _
 rw [← map_inv,← map_mul,← map_mul,d.cubic_action]

/-- All fields are produced from splitting and the natural-module identification. -/
noncomputable def generatorsOnImage :
 ParabolicGenerators (A (embedding d i)) (secondParabolic d i) (TL d i)
  (marked (embedding d i)) := by
 let p := withCubic (embedding d i) (embedding_injective d i hi) (cubic d i) (cubic_equation d i)
 refine { p with
  normalizes := actor_normalizes d i
  sylow_generators := ?_
  parabolic_generators := ?_ }
 · rw [← embedding_range]
   exact p.sylow_generators
 · rw [actor_eq,sup_comm]
   exact p.parabolic_generators

private def transferGenerators {B C P S : Subgroup G} (h : B=C) (z : B) (w : C)
 (hz : (z : G) = (w : G)) (p : ParabolicGenerators C P S w) :
 ParabolicGenerators B P S z := by
 subst C
 have he : z=w := Subtype.ext hz
 subst w
 exact p

/-- The constructed record lives on the actual elementary Thompson subgroup. -/
noncomputable def generators :
 ParabolicGenerators (Stellmacher.elementaryAbelianMaxJ (TL d i))
  (secondParabolic d i) (TL d i) (point d i hi) := by
 exact transferGenerators (thompson_image d i hi) (point d i hi)
  (marked (embedding d i)) rfl (generatorsOnImage d i hi)

end CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.SplitParabolic.Natural

namespace CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.SplitParabolic.Natural
open Subgroup Matrix.PSL3Two Matrix.PSL3Two.SplitParabolic
variable {L G : Type*} [Group L] [Group G] {V : Subgroup L} [V.Normal]
 (d : SplitNaturalData V) (i : L →* G) (hi : Function.Injective i)

@[expose] noncomputable def blockEmbedding : Block →* G := i.comp d.blockEquiv.symm.toMonoidHom

include hi in
theorem blockEmbedding_injective : Function.Injective (blockEmbedding d i) :=
 hi.comp d.blockEquiv.symm.injective

include hi in
theorem block_core : OutsideSelection.U.map (blockEmbedding d i) = (firstParabolic d i).pCoreIn 2 := by
 rw [OutsideSelection.U,← Matrix.PSL3Two.SplitParabolic.U_image,Subgroup.map_map]
 exact core_image d i hi

theorem block_sylow : standardSylow.map (blockEmbedding d i) = TL d i := by
 rw [← sylowMap_range,← MonoidHom.range_comp]
 exact embedding_range d i

/-- The source plane V₂ is transported through the same split block isomorphism. -/
@[expose] noncomputable def plane : Subgroup G := OutsideSelection.V2.map (blockEmbedding d i)

/-- This is the literal relative centralizer C_U(V₂). -/
@[expose] noncomputable def W : Subgroup G := (firstParabolic d i).pCoreIn 2 ⊓ centralizer (plane d i : Set G)

/-- Source convention W^g = g⁻¹ W g. -/
@[expose] noncomputable def X (g : L) : Subgroup G := (W d i).map (MulAut.conj (i g)⁻¹).toMonoidHom

include hi in
theorem block_X (g : L) :
 SelectedAssembly.embeddedX (blockEmbedding d i) (d.blockEquiv g) = X d i g := by
 have he : blockEmbedding d i (d.blockEquiv g) = i g := by
  change i (d.blockEquiv.symm (d.blockEquiv g)) = i g
  rw [MulEquiv.symm_apply_apply]
 simp only [SelectedAssembly.embeddedX,SelectedAssembly.embeddedW,block_core d i hi,he]
 rfl

include hi in
/-- The subgroup U W^g is exactly the marked Sylow preimage. -/
theorem core_sup_X (g : L) (hg : g ∈ d.markedPreimage lineParabolicSL)
 (hp : g ∉ d.markedPreimage pointParabolicSL) :
 (firstParabolic d i).pCoreIn 2 ⊔ X d i g = TL d i := by
 have hg' : d.blockEquiv g ∈ linePreimage := by
  change projection (d.blockEquiv g) ∈ lineParabolicSL
  rw [d.blockEquiv_projection]
  exact hg
 have hp' : d.blockEquiv g ∉ pointPreimage := by
  change projection (d.blockEquiv g) ∉ pointParabolicSL
  rw [d.blockEquiv_projection]
  exact hp
 have he := congrArg (fun P : Subgroup Block => P.map (blockEmbedding d i))
  (SelectedAssembly.core_sup_conjugate (d.blockEquiv g) hg' hp')
 rw [Subgroup.map_sup,block_core d i hi,SelectedAssembly.X_map _ (blockEmbedding_injective d i hi),
  block_X d i hi,block_sylow] at he
 exact he

include hi in
/-- The selected involution belongs to the source conjugate centralizer and
acts as a₂ on the actual embedded quaternion core. -/
theorem exists_source_involution [Finite G] (g : L)
 (hg : g ∈ d.markedPreimage lineParabolicSL)
 (hp : g ∉ d.markedPreimage pointParabolicSL)
 (dq : QuaternionCentralProductData ((firstParabolic d i).pCoreIn 2)) :
 ∃ x : G, x ∈ X d i g ∧ x ∉ (firstParabolic d i).pCoreIn 2 ∧ x ≠ 1 ∧ x^2=1 ∧
   x ∈ TL d i ∧
   zpowers x ⊔ ⁅(firstParabolic d i).pCoreIn 2,zpowers x⁆ =
     Stellmacher.elementaryAbelianMaxJ (TL d i) ∧
   ∃ hn : x ∈ normalizer ((firstParabolic d i).pCoreIn 2 : Set G),
     dq.IsA2Action (((firstParabolic d i).pCoreIn 2).normalizerMonoidHom ⟨x,hn⟩) := by
 have hg' : d.blockEquiv g ∈ linePreimage := by
  change projection (d.blockEquiv g) ∈ lineParabolicSL
  rw [d.blockEquiv_projection]
  exact hg
 have hp' : d.blockEquiv g ∉ pointPreimage := by
  change projection (d.blockEquiv g) ∉ pointParabolicSL
  rw [d.blockEquiv_projection]
  exact hp
 have he := SelectedAssembly.exists_selected_geometry (blockEmbedding d i)
  (blockEmbedding_injective d i hi) (d.blockEquiv g) hg' hp'
 rw [block_core d i hi,block_X d i hi,block_sylow] at he
 exact he dq

include hi in
/-- The marking is the actual nonidentity central element of T_L. -/
theorem central_point_unique (z : G) (hz : z ∈ TL d i) (hne : z ≠ 1)
 (hc : ∀ t ∈ TL d i, z*t=t*z) : z = (point d i hi : G) := by
 rw [← embedding_range] at hz
 obtain ⟨x,rfl⟩ := hz
 have hx : x ∈ center Unitriangular.T := by
  apply mem_center_iff.mpr
  intro y
  apply embedding_injective d i hi
  rw [map_mul,map_mul]
  exact (hc _ (by rw [← embedding_range]; exact ⟨y,rfl⟩)).symm
 have hxn : x ≠ 1 := by
  intro he
  exact hne (by rw [he,map_one])
 rw [SelectedAssembly.central_nonidentity x hx hxn]
 rfl

/-- Application with any source-selected nontrivial central involution z. -/
noncomputable def generatorsAt (z : Stellmacher.elementaryAbelianMaxJ (TL d i))
 (hz : (z : G) ∈ TL d i) (hne : (z : G) ≠ 1)
 (hc : ∀ t ∈ TL d i, (z : G)*t=t*(z : G)) :
 ParabolicGenerators (Stellmacher.elementaryAbelianMaxJ (TL d i))
  (secondParabolic d i) (TL d i) z :=
 transferGenerators rfl z (point d i hi) (central_point_unique d i hi z hz hne hc) (generators d i hi)

theorem point_square : point d i hi ^ 2 = 1 := by
 apply Subtype.ext
 change (embedding d i Unitriangular.z)^2=1
 rw [← map_pow,show Unitriangular.z^2=1 from by decide +kernel,map_one]

include hi in
theorem central_mem_thompson (z : G) (hz : z ∈ TL d i) (hne : z ≠ 1)
 (hc : ∀ t ∈ TL d i, z*t=t*z) : z ∈ Stellmacher.elementaryAbelianMaxJ (TL d i) := by
 rw [central_point_unique d i hi z hz hne hc]
 exact (point d i hi).property

/-- Embed the original source involution into the constructed Thompson sixteen. -/
@[expose] noncomputable def sourcePoint (z : G) (hz : z ∈ TL d i) (hne : z ≠ 1)
 (hc : ∀ t ∈ TL d i, z*t=t*z) : Stellmacher.elementaryAbelianMaxJ (TL d i) :=
 ⟨z,central_mem_thompson d i hi z hz hne hc⟩

/-- Parabolic generators with the original source point, without assuming z ∈ J(T_L). -/
noncomputable def sourceGenerators (z : G) (hz : z ∈ TL d i) (hne : z ≠ 1)
 (hc : ∀ t ∈ TL d i, z*t=t*z) :
 ParabolicGenerators (Stellmacher.elementaryAbelianMaxJ (TL d i))
  (secondParabolic d i) (TL d i) (sourcePoint d i hi z hz hne hc) :=
 generatorsAt d i hi (sourcePoint d i hi z hz hne hc) hz hne hc

open scoped Pointwise

include hi in
theorem sylow_normalizes_core : TL d i ≤ normalizer ((firstParabolic d i).pCoreIn 2 : Set G) := by
 rw [← embedding_range,← core_image d i hi]
 rintro _ ⟨x,rfl⟩
 exact le_normalizer_map (embedding d i)
  ⟨x,by rw [Unitriangular.U.normalizer_eq_top]; trivial,rfl⟩

include hi in
/-- The source product is the literal set product, using only relative normality. -/
theorem sylow_product (g : L) (hg : g ∈ d.markedPreimage lineParabolicSL)
 (hp : g ∉ d.markedPreimage pointParabolicSL) :
 (TL d i : Set G) = ((firstParabolic d i).pCoreIn 2 : Set G) * (X d i g : Set G) := by
 have hx : X d i g ≤ TL d i := by
  rw [← core_sup_X d i hi g hg hp]
  exact le_sup_right
 calc
  (TL d i : Set G) = ((firstParabolic d i).pCoreIn 2 ⊔ X d i g : Subgroup G) :=
   congrArg (fun P : Subgroup G => (P : Set G)) (core_sup_X d i hi g hg hp).symm
  _ = _ := coe_mul_of_right_le_normalizer_left _ _ (hx.trans (sylow_normalizes_core d i hi))

end CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.SplitParabolic.Natural
