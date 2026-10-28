module
public import CFSG.Quasithin.ChapterC.Section01.AugmentationSixControl.Model
public import Theory.Representation.BinaryOffender.CubicConjugateBound
public import Stellmacher.ElementaryAbelianMaxGlobal
public import Stellmacher.ElementaryAbelianMaxJMap
public import CFSG.Quasithin.ChapterB.Section02.Baumann.SylowPreimageGenerators
public import Theory.GroupTheory.SylowPreimageNormalizer
/-!
# Baumann decomposition on the original augmentation module with full kernel

The mixed-plane generators are actual Sylow subgroups of their full
preimages. Equal-weight replacement constructs their Thompson images;
even conjugates generate S₆ and have fixed codimensions two plus two,
matching the codimension four of A₆. The Sylow-preimage form of B.2.19
therefore gives the alpha decomposition and centralizer Sylow conclusion.
The full kernel may contain the central three of the covered row.

The original firstFlagCore application discharges the Frattini condition
using the literal central quotient and quasisimplicity. No equality of the
whole action kernel with the two-core is required.
Source: Aschbacher--Smith B.2.19, pp.81--82; C.1.37, pp.142--143;
13.2.2(7), pp.877--878.
-/

noncomputable section
open Subgroup Stellmacher
open scoped IsMulCommutative
open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.AugmentationSixControl
open ChapterB ChapterB.BaumannArgument
open ChapterB.Offenders ChapterB.Offenders.Six
universe u
variable {K : Type u} [Group K]
section Action
variable {K : Type u} [Group K] (V : Subgroup K) [V.Normal]

/-- Coordinates for the literal conjugation action on the augmentation core. -/
structure SylowCoreAction where
  q : K →* Model.S
  onto : Function.Surjective q
  R : Subgroup K
  R_two : IsPGroup 2 R
  R_image : R.map q = Model.E
  module_le_R : V ≤ R
  core : R ⊓ centralizer (V : Set K) = pCore 2 K
  kernel_sylow : ∃ P : Sylow 2 q.ker,
    (P : Subgroup q.ker).map q.ker.subtype = R ⊓ q.ker
  coordinates : V ≃* Multiplicative (BinaryPermutation.core (Fin 6))
  action : ∀ g v, (coordinates (MulAut.conjNormal g v)).toAdd =
    Model.rho (q g) (coordinates v).toAdd

namespace SylowCoreAction
variable {V} (d : SylowCoreAction V)

theorem kernel_centralizer : d.q.ker = centralizer (V : Set K) :=
  ChapterB.Offenders.SixCorePoint.kernel_centralizer V d.q d.coordinates d.action

def addCoordinates : Additive V ≃+ BinaryPermutation.core (Fin 6) where
  toFun v := (d.coordinates v.toMul).toAdd
  invFun v := Additive.ofMul (d.coordinates.symm (Multiplicative.ofAdd v))
  left_inv v := d.coordinates.symm_apply_apply v
  right_inv v := d.coordinates.apply_symm_apply (Multiplicative.ofAdd v)
  map_add' v w := d.coordinates.map_mul v.toMul w.toMul

variable [IsElementaryAbelian 2 V]

noncomputable def linearCoordinates : Additive V ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6) :=
  { d.addCoordinates with map_smul' := ZMod.map_smul d.addCoordinates }

noncomputable def ρ : Representation (ZMod 2) Model.S (Additive V) :=
  Representation.NormalElementaryQuotient.representation V d.q d.onto d.kernel_centralizer

theorem equivariant (g : Model.S) (v : Additive V) :
    d.linearCoordinates (d.ρ g v) = Model.rho g (d.linearCoordinates v) := by
  obtain ⟨a,rfl⟩ := d.onto g
  have he := Representation.NormalElementaryQuotient.representation_apply
    V d.q d.onto d.kernel_centralizer a v
  have hc : (d.ρ (d.q a) v).toMul = MulAut.conjNormal a v.toMul := Subtype.ext he
  change (d.coordinates _).toAdd = _
  rw [hc]
  exact d.action a v.toMul

theorem fixed_finrank (A : Subgroup Model.S) :
    Module.finrank (ZMod 2) (fixedSpace d.ρ A) =
      Module.finrank (ZMod 2) (fixedSpace Model.rho A) := by
  have he := fixedSpace_map_equivariant d.ρ Model.rho
    (MonoidHom.id Model.S) d.linearCoordinates d.equivariant A
  rw [map_id] at he
  exact ((Submodule.equivMapOfInjective d.linearCoordinates.toLinearMap
    d.linearCoordinates.injective _).trans (LinearEquiv.ofEq _ _ he)).finrank_eq

theorem model_fixedCodim (A : Subgroup Model.S) :
    fixedCodim d.ρ A = fixedCodim Model.rho A := by
  simpa only [map_id] using fixedCodim_map_equivariant d.ρ Model.rho
    (MonoidHom.id Model.S) d.linearCoordinates d.equivariant A

theorem bestOffender_iff (A : Subgroup Model.S) :
    IsBestOffender d.ρ A ↔ IsBestOffender Model.rho A := by
  simp only [IsBestOffender, weight, d.fixed_finrank]

include d in
omit [IsElementaryAbelian 2 V] in
theorem module_card : Nat.card V = 32 := by
  rw [Nat.card_congr d.coordinates.toEquiv]
  change Nat.card (BinaryPermutation.core (Fin 6)) = 32
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    BinaryPermutation.finrank_core]
  rfl

omit [IsElementaryAbelian 2 V] in
noncomputable def actionEquiv : (K ⧸ centralizer (V : Set K)) ≃* Model.S :=
  (QuotientGroup.quotientMulEquivOfEq d.kernel_centralizer.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective d.q d.onto)

omit [IsElementaryAbelian 2 V] in
theorem actionEquiv_apply (g : K) : d.actionEquiv (actionMap V g) = d.q g := by rfl

omit [IsElementaryAbelian 2 V] in
theorem image_eq (A : Subgroup K) :
    (A.map (actionMap V)).map d.actionEquiv.toMonoidHom = A.map d.q := by
  rw [map_map]
  rfl

variable [Finite K]

theorem fixed_card (A : Subgroup K) :
    Nat.card (V ⊓ centralizer (A : Set K) : Subgroup K) =
      2 ^ Module.finrank (ZMod 2) (fixedSpace Model.rho (A.map d.q)) := by
  have h := Nat.card_congr (Representation.NormalElementaryQuotient.fixedSpaceEquiv
    V d.q d.onto d.kernel_centralizer A)
  rw [← h]
  change Nat.card (fixedSpace d.ρ (A.map d.q)) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, d.fixed_finrank]

theorem fixedCodim_eq_model (A : Subgroup K) :
    ChapterB.BaumannArgument.fixedCodim V A = Representation.BinaryOffender.fixedCodim Model.rho (A.map d.q) := by
  have hd := fixedCodim_add_finrank Model.rho (A.map d.q)
  rw [BinaryPermutation.finrank_core] at hd
  norm_num at hd
  rw [ChapterB.BaumannArgument.fixedCodim, d.module_card, d.fixed_card, Nat.log_pow Nat.one_lt_two]
  norm_num
  omega

omit [IsElementaryAbelian 2 V] in
theorem residual_image : (pResidual 2 K).map d.q = alternatingGroup (Fin 6) := by
  rw [map_pResidual_of_surjective 2 d.q d.onto, Equiv.Perm.twoResidual_eq_alternating]

omit [IsElementaryAbelian 2 V] in
theorem residual_lift (g : alternatingGroup (Fin 6)) :
    ∃ a ∈ pResidual 2 K, d.q a = g := by
  apply mem_map.mp
  rw [d.residual_image]
  exact g.property

omit [IsElementaryAbelian 2 V] in
def residualHom : pResidual 2 K →* alternatingGroup (Fin 6) :=
  (d.q.comp (pResidual 2 K).subtype).codRestrict _ fun a => by
    rw [← d.residual_image]
    exact mem_map_of_mem d.q a.property

omit [IsElementaryAbelian 2 V] in
theorem residual_surjective : Function.Surjective d.residualHom := by
  intro g
  obtain ⟨a,ha,he⟩ := d.residual_lift g
  exact ⟨⟨a,ha⟩, Subtype.ext he⟩

end SylowCoreAction
end Action
section Family
variable {K : Type u} [Group K] [Finite K]
variable {V : Subgroup K} [V.Normal] [IsElementaryAbelian 2 V]
namespace SylowCoreAction
variable (d : SylowCoreAction V)
private def D0 : Subgroup K := d.R ⊓ plus.comap d.q
private noncomputable def lift : K :=
  (d.residual_lift ⟨Model.conjugator,Model.conjugator_even⟩).choose
omit [IsElementaryAbelian 2 V] in
private theorem lift_mem : d.lift ∈ pResidual 2 K :=
  (d.residual_lift ⟨Model.conjugator,Model.conjugator_even⟩).choose_spec.1
omit [IsElementaryAbelian 2 V] in
private theorem lift_image : d.q d.lift = Model.conjugator :=
  (d.residual_lift ⟨Model.conjugator,Model.conjugator_even⟩).choose_spec.2
/-- Two actual Sylow preimages, the second conjugated by an element of O²(K). -/
noncomputable def D (i : Fin 2) : Subgroup K :=
  Fin.cases d.D0 (fun _ => d.D0.map (MulAut.conj d.lift).toMonoidHom) i

omit [Finite K] [IsElementaryAbelian 2 V] in
private theorem D0_image : d.D0.map d.q = plus := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact hx.2
  · intro x hx
    have hxE : x ∈ Model.E := plus_le_exceptional hx
    obtain ⟨r,hr,he⟩ := d.R_image.symm ▸ hxE
    exact ⟨r,⟨hr,show d.q r ∈ plus from he.symm ▸ hx⟩,he⟩

omit [Finite K] [IsElementaryAbelian 2 V] in
private theorem D0_kernel : d.D0 ⊓ d.q.ker = d.R ⊓ d.q.ker := by
  apply le_antisymm (inf_le_inf_right _ inf_le_left)
  intro x hx
  refine ⟨⟨hx.1,?_⟩,hx.2⟩
  change d.q x ∈ plus
  rw [MonoidHom.mem_ker.mp hx.2]
  exact one_mem _

omit [IsElementaryAbelian 2 V] in
private theorem D0_sylow : IsSylowSubgroupIn d.D0 (plus.comap d.q) := by
  obtain ⟨P,hP⟩ := d.kernel_sylow
  obtain ⟨S,hS⟩ := exists_sylow_preimage_of_kernel_intersection d.D0
    (d.R_two.to_le inf_le_left) d.q P (hP.trans d.D0_kernel.symm)
  have hh : IsSylowSubgroupIn d.D0 ((d.D0.map d.q).comap d.q) :=
    ⟨S,hS ▸ map_subgroupOf_eq_of_le (le_comap_map d.q d.D0)⟩
  rwa [d.D0_image] at hh

omit [Finite K] in
private theorem map_conjugate {H : Type*} [Group H] (q : K →* H)
    (A : Subgroup K) (g : K) :
    (A.map (MulAut.conj g).toMonoidHom).map q =
      (A.map q).map (MulAut.conj (q g)).toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  ext x
  simp

omit [IsElementaryAbelian 2 V] in
theorem D_image (i : Fin 2) : (d.D i).map d.q = Model.root i := by
  fin_cases i
  · exact d.D0_image
  · change (d.D0.map (MulAut.conj d.lift).toMonoidHom).map d.q = Model.secondPlane
    rw [map_conjugate,d.D0_image,d.lift_image]
    rfl

omit [IsElementaryAbelian 2 V] in
theorem D_zero_le_R : d.D 0 ≤ d.R := by
  exact inf_le_left

omit [IsElementaryAbelian 2 V] in
theorem D_conjugate (i : Fin 2) :
    ∃ l ∈ pResidual 2 K, (d.D 0).map (MulAut.conj l).toMonoidHom = d.D i := by
  fin_cases i
  · refine ⟨1,one_mem _,?_⟩
    have hi : (MulAut.conj (1 : K)).toMonoidHom = MonoidHom.id K := by ext x;simp
    rw [hi,map_id]
    rfl
  · exact ⟨d.lift,d.lift_mem,rfl⟩

theorem noStrongOffenders : NoStrongOffenders V d.R := by
  intro A hA he hne
  have hi : (A.map (actionMap V)).map d.actionEquiv.toMonoidHom = A.map d.q := d.image_eq A
  have hcard : Nat.card (A.map (actionMap V)) = Nat.card (A.map d.q) := by
    rw [← hi,card_map_of_injective (f := d.actionEquiv.toMonoidHom) d.actionEquiv.injective]
  have hq : IsElementaryTwo (A.map d.q) := by
    let := he
    exact ⟨hi ▸ (map_eq_bot_iff_of_injective (f := d.actionEquiv.toMonoidHom)
      (A.map (actionMap V)) d.actionEquiv.injective).not.mpr hne,
      hi ▸ IsElementaryAbelian.map d.actionEquiv.toMonoidHom⟩
  rw [hcard,d.fixedCodim_eq_model]
  exact Model.rank_le_fixedCodim ((map_mono hA).trans_eq d.R_image) hq

private theorem rank_mono {A B : Subgroup K} (h : A ≤ B) : twoRank A ≤ twoRank B :=
  Nat.log_mono_right (elementaryAbelianMaxOrder_le_and_j_le_of_eq A B h).1

theorem centralizer_rank : twoRank (pCore 2 K) = twoRank d.R := by
  have hr := (centralizer_rank_and_alpha V d.R d.module_le_R d.noStrongOffenders).1
  rwa [d.core] at hr

theorem D_zero_rank : twoRank (d.D 0) = twoRank d.R := by
  apply le_antisymm (rank_mono d.D_zero_le_R)
  rw [← d.centralizer_rank]
  apply rank_mono
  rw [←d.core]
  intro x hx
  change x ∈ d.R ⊓ plus.comap d.q
  refine ⟨hx.1,?_⟩
  change d.q x ∈ plus
  rw [show d.q x = 1 from MonoidHom.mem_ker.mp (d.kernel_centralizer.symm ▸ hx.2)]
  exact one_mem _


theorem D_rank (i : Fin 2) : twoRank (d.D i) = twoRank d.R := by
  obtain ⟨l,_,hl⟩ := d.D_conjugate i
  rw [←hl,twoRank_map_equiv]
  exact d.D_zero_rank
private theorem max_le_J_of_card (S A : Subgroup K) (hAS : A ≤ S)
    (he : IsElementaryAbelian 2 A) (hc : Nat.card A = elementaryAbelianMaxOrder S) :
    A ≤ elementaryAbelianMaxJ S := by
  apply le_sSup
  refine ⟨hAS,he,?_⟩
  intro E hES hE
  obtain ⟨B,hB⟩ := elementaryAbelianMaxSubgroups_nonempty S
  exact (hB.2.2 E hES hE).trans_eq
    ((card_eq_elementaryAbelianMaxOrder S B hB).trans hc.symm)

/-- A Thompson image larger than the point transposition contains a maximum
mixed-plane image, after a component conjugation. -/
theorem exists_root_maximum
    (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q ≤ last) :
    ∃ C : Subgroup K, C ≤ d.D 0 ∧ IsElementaryAbelian 2 C ∧
      Nat.card C = elementaryAbelianMaxOrder d.R ∧ C.map d.q = plus := by
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups d.R, ¬ A.map d.q ≤ last := by
    by_contra! hz
    apply hne
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro A hA
    exact map_le_iff_le_comap.mp (hz A hA)
  obtain ⟨A,hA,hneA⟩ := hex
  have ha : A.map d.q ≤ Model.E := (map_mono hA.1).trans_eq d.R_image
  have hAn : A.map d.q ≠ ⊥ := by intro hz;exact hneA (hz ▸ bot_le)
  have hb : IsBestOffender Model.rho (A.map d.q) := (d.bestOffender_iff _).mp
    (Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
      V d.q d.onto d.kernel_centralizer d.R A d.module_le_R hA hAn)
  obtain ⟨i,hw⟩ := Model.exists_plane_equalWeight ha hb hneA
  have he : IsElementaryTwo (Model.corePlane i) := (Model.corePlane_best i).1
  have hw' : EqualWeightLE d.ρ (Model.corePlane i) (A.map d.q) := by
    refine ⟨hw.1,?_⟩
    simpa only [weight,d.fixed_finrank] using hw.2
  obtain ⟨hC,hmap⟩ := lemma_B_2_8_construct V d.q d.onto d.kernel_centralizer
    d.R d.module_le_R A hA (Model.corePlane i) he hw'
  let C := (A ⊓ (Model.corePlane i).comap d.q) ⊔
    (V ⊓ centralizer (A ⊓ (Model.corePlane i).comap d.q : Set K))
  have hC' : C ∈ elementaryAbelianMaxSubgroups d.R := hC
  have hmap' : C.map d.q = Model.corePlane i := hmap
  obtain ⟨l,hl,hq⟩ := d.residual_lift
    ⟨(Model.planeConjugator i)⁻¹,inv_mem (Model.planeConjugator_even i)⟩
  let C' := C.map (MulAut.conj l).toMonoidHom
  have hmap0 : C'.map d.q = plus := by
    rw [map_conjugate,hmap',hq,← Model.corePlane_conjugate i,map_map]
    have hh : (MulAut.conj (Model.planeConjugator i)⁻¹).toMonoidHom.comp
      (MulAut.conj (Model.planeConjugator i)).toMonoidHom = MonoidHom.id Model.S := by
      ext x
      simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,MonoidHom.id_apply]
      group
    rw [hh,map_id]
  have hCY : C' ≤ plus.comap d.q := map_le_iff_le_comap.mp hmap0.le
  obtain ⟨S,hS⟩ := d.D0_sylow
  obtain ⟨P,hP⟩ := ((hC'.2.1.map (MulAut.conj l).toMonoidHom).isPGroup.comap_subtype
    (K := plus.comap d.q)).exists_le_sylow
  obtain ⟨y,hy⟩ := MulAction.exists_smul_eq (plus.comap d.q) P S
  let C'' := C'.map (MulAut.conj y.val).toMonoidHom
  have hCD : C'' ≤ d.D0 := by
    rw [←hS]
    rintro _ ⟨c,hc,rfl⟩
    refine ⟨y * ⟨c,hCY hc⟩ * y⁻¹,?_,rfl⟩
    have he : (P : Subgroup (plus.comap d.q)).map (MulAut.conj y).toMonoidHom = S := by
      change ((y • P : Sylow 2 (plus.comap d.q)) : Subgroup (plus.comap d.q)) = S
      rw [hy]
    rw [←he]
    exact mem_map_of_mem _ (hP hc)
  refine ⟨C'',hCD,(hC'.2.1.map _).map _,?_,?_⟩
  · rw [show C'' = C'.map (MulAut.conj y.val).toMonoidHom from rfl,
      card_map_of_injective (MulAut.conj y.val).injective]
    exact (card_map_of_injective (MulAut.conj l).injective).trans
      (card_eq_elementaryAbelianMaxOrder d.R C hC')
  · rw [show C'' = C'.map (MulAut.conj y.val).toMonoidHom from rfl,
      map_conjugate,hmap0]
    exact mem_normalizer_iff_map_conj_eq.mp (plus.le_normalizer y.property)

theorem thompson_D_zero_image
    (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q ≤ last) :
    (elementaryAbelianMaxJ (d.D 0)).map d.q = plus := by
  obtain ⟨C,hC,he,hcard,hmap⟩ := d.exists_root_maximum hne
  have hc : Nat.card C = elementaryAbelianMaxOrder (d.D 0) := by
    rw [hcard,maxOrder_eq_two_pow_rank,maxOrder_eq_two_pow_rank,d.D_zero_rank]
  apply le_antisymm
  · exact (map_mono (sSup_le fun _ hA => hA.1)).trans_eq (d.D_image 0)
  · rw [← hmap]
    exact map_mono (max_le_J_of_card (d.D 0) C hC he hc)

theorem thompson_D_image
    (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q ≤ last) (i : Fin 2) :
    (elementaryAbelianMaxJ (d.D i)).map d.q = Model.root i := by
  obtain ⟨l,_,hD⟩ := d.D_conjugate i
  rw [← hD,elementaryAbelianMaxJ_map_equiv,map_conjugate,d.thompson_D_zero_image hne]
  have hh := congrArg (fun A : Subgroup K => A.map d.q) hD
  rwa [map_conjugate,d.D_image,d.D_image] at hh

omit [IsElementaryAbelian 2 V] in
private theorem D_core (i : Fin 2) : pCore 2 K ≤ d.D i := by
  have hzero : pCore 2 K ≤ d.D 0 := by
    rw [←d.core]
    intro x hx
    change x ∈ d.R ⊓ plus.comap d.q
    refine ⟨hx.1,?_⟩
    change d.q x ∈ plus
    rw [show d.q x = 1 from MonoidHom.mem_ker.mp (d.kernel_centralizer.symm ▸ hx.2)]
    exact one_mem _
  obtain ⟨l,hl,hD⟩ := d.D_conjugate i
  have hm := map_mono (f := (MulAut.conj l).toMonoidHom) hzero
  have hn : (pCore 2 K).map (MulAut.conj l).toMonoidHom = pCore 2 K :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top];exact mem_top _)
  rwa [hn,hD] at hm

omit [Finite K] [IsElementaryAbelian 2 V] in
private theorem preimage_conjugate (A : Subgroup Model.S) (g : K) :
    (A.comap d.q).map (MulAut.conj g).toMonoidHom =
      (A.map (MulAut.conj (d.q g)).toMonoidHom).comap d.q := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨d.q y,hy,by simp⟩
  · rintro ⟨y,hy,he⟩
    refine ⟨g⁻¹*x*g,?_,by dsimp;group⟩
    change d.q (g⁻¹*x*g) ∈ A
    have hx : d.q x = d.q g*y*(d.q g)⁻¹ := he.symm
    rw [map_mul,map_mul,map_inv,hx]
    have hh : (d.q g)⁻¹*(d.q g*y*(d.q g)⁻¹)*d.q g = y := by group
    rw [hh]
    exact hy

omit [IsElementaryAbelian 2 V] in
private theorem D_sylow (i : Fin 2) :
    IsSylowSubgroupIn (d.D i) (((d.D i).map (actionMap V)).comap (actionMap V)) := by
  have hs : IsSylowSubgroupIn (d.D i) (((d.D i).map d.q).comap d.q) := by
    obtain ⟨l,hl,hD⟩ := d.D_conjugate i
    have hh := (Chapter1.IsSylowIn.map_iff (MulAut.conj l).toMonoidHom
      (MulAut.conj l).injective).mpr d.D0_sylow
    change IsSylowSubgroupIn ((d.D 0).map (MulAut.conj l).toMonoidHom)
      ((plus.comap d.q).map (MulAut.conj l).toMonoidHom) at hh
    rw [d.preimage_conjugate,hD] at hh
    have hm := congrArg (map d.q) hD
    rw [map_conjugate,d.D_image] at hm
    rw [←hm]
    exact hh
  have hpre : (((d.D i).map d.q).comap d.q) =
      (((d.D i).map (actionMap V)).comap (actionMap V)) := by
    rw [comap_map_eq,comap_map_eq,actionMap_ker,d.kernel_centralizer]
  rwa [hpre] at hs

private theorem thompson_self (S : Subgroup K) :
    elementaryAbelianMaxJ (elementaryAbelianMaxJ S) = elementaryAbelianMaxJ S := by
  have hle : elementaryAbelianMaxJ S ≤ S := sSup_le fun _ hA => hA.1
  have h := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le S
    (elementaryAbelianMaxJ S) le_rfl
  have he : elementaryAbelianMaxOrder S = elementaryAbelianMaxOrder (elementaryAbelianMaxJ S) :=
    le_antisymm h.1 (elementaryAbelianMaxOrder_le_and_j_le_of_eq _ _ hle).1
  exact le_antisymm (sSup_le fun _ hA => hA.1) (h.2 he)

theorem family_AD (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q ≤ last)
    (hfrat : pResidual 2 K ⊓ centralizer (V : Set K) ≤ coreFrattini (pResidual 2 K)) :
    HypothesesAD V d.R (fun i : Fin 2 => elementaryAbelianMaxJ (d.D i)) := by
  have hcore : (pCore 2 (pResidual 2 K)).map (pResidual 2 K).subtype ≤
      d.R ⊓ centralizer (V : Set K) := by
    rw [d.core]
    exact le_sSup ⟨inferInstance,pCore_isPGroup.map _⟩
  have hnorm : pResidual 2 K ≤ normalizer (d.R ⊓ centralizer (V : Set K) : Set K) := by
    change pResidual 2 K ≤ normalizer ((d.R ⊓ centralizer (V : Set K) : Subgroup K) : Set K)
    rw [d.core,normalizer_eq_top]
    exact le_top
  refine ⟨d.R_two,d.module_le_R,hcore,hnorm,hfrat,d.noStrongOffenders,
    ?_,(fun i => thompson_self (d.D i)),?_,?_,?_⟩
  · intro i
    obtain ⟨l,hl,hD⟩ := d.D_conjugate i
    refine ⟨l⁻¹,inv_mem hl,?_⟩
    apply (map_mono (show elementaryAbelianMaxJ (d.D i) ≤ d.D i from
      sSup_le fun _ hA => hA.1)).trans
    rw [← hD]
    have hc : (MulAut.conj l⁻¹).toMonoidHom.comp (MulAut.conj l).toMonoidHom =
        MonoidHom.id K := by ext x; simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply]; group
    rw [map_map,hc,map_id]
    exact d.D_zero_le_R
  · intro i
    exact (twoRank_eq_of_intermediate (d.D i) _ le_rfl
      (sSup_le fun _ hA => hA.1)).trans (d.D_rank i)
  · apply (map_le_map_iff_of_injective (f := d.actionEquiv.toMonoidHom)
      d.actionEquiv.injective).mp
    rw [Subgroup.map_iSup]
    simp_rw [d.image_eq, d.thompson_D_image hne]
    rw [Model.root_generation]
    exact le_top
  · have hc (i : Fin 2) : ChapterB.BaumannArgument.fixedCodim V
        (elementaryAbelianMaxJ (d.D i)) = 2 := by
      rw [d.fixedCodim_eq_model,d.thompson_D_image hne,Model.root_codim]
    have hr : ChapterB.BaumannArgument.fixedCodim V (pResidual 2 K) = 4 := by
      rw [d.fixedCodim_eq_model,d.residual_image,Model.alternating_codim]
    simp_rw [hc]
    rw [hr]
    decide
omit [Finite K] in
theorem action_representation :
    Representation.NormalElementaryQuotient.representation V (actionMap V)
      (QuotientGroup.mk'_surjective _) (actionMap_ker V) =
      d.ρ.comp d.actionEquiv.toMonoidHom := by
  apply MonoidHom.ext
  intro h
  apply LinearMap.ext
  intro v
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (V : Set K)) h
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((Representation.NormalElementaryQuotient.representation V (actionMap V)
    (QuotientGroup.mk'_surjective _) (actionMap_ker V) (actionMap V g) v).toMul : K) =
    ((d.ρ (d.q g) v).toMul : K)
  exact (Representation.NormalElementaryQuotient.representation_apply V (actionMap V)
    (QuotientGroup.mk'_surjective _) (actionMap_ker V) g v).trans
    (Representation.NormalElementaryQuotient.representation_apply
      V d.q d.onto d.kernel_centralizer g v).symm

omit [Finite K] in
theorem action_weight (E : Subgroup (K ⧸ centralizer (V : Set K))) :
    Representation.BinaryOffender.weight
      (Representation.NormalElementaryQuotient.representation V (actionMap V)
        (QuotientGroup.mk'_surjective _) (actionMap_ker V)) E =
      Representation.BinaryOffender.weight d.ρ (E.map d.actionEquiv.toMonoidHom) := by
  rw [d.action_representation]
  exact Representation.BinaryOffender.weight_comp_map d.ρ d.actionEquiv.toMonoidHom
    d.actionEquiv.injective E

theorem equal_weight_cover (A : Subgroup K)
    (hA : A ∈ elementaryAbelianMaxSubgroups d.R) (hne : A.map (actionMap V) ≠ ⊥) :
    ∃ E : Set (Subgroup (K ⧸ centralizer (V : Set K))),
      sSup E = A.map (actionMap V) ∧
      ∀ B ∈ E, IsElementaryTwo B ∧
        EqualWeightLE
          (Representation.NormalElementaryQuotient.representation V (actionMap V)
            (QuotientGroup.mk'_surjective _) (actionMap_ker V)) B (A.map (actionMap V)) ∧
        ∃ i : Fin 2, ∃ g ∈ pResidual 2 K,
          B ≤ ((d.D i).map (MulAut.conj g).toMonoidHom).map (actionMap V) := by
  have ha : A.map d.q ≤ Model.E := (map_mono hA.1).trans_eq d.R_image
  have han : A.map d.q ≠ ⊥ := by
    rw [← d.image_eq]
    exact (map_eq_bot_iff_of_injective _ d.actionEquiv.injective).not.mpr hne
  have hb : IsBestOffender Model.rho (A.map d.q) := (d.bestOffender_iff _).mp
    (Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
      V d.q d.onto d.kernel_centralizer d.R A d.module_le_R hA han)
  obtain ⟨F,hF,hparts⟩ := Model.equal_weight_cover ha hb
  let E : Set (Subgroup (K ⧸ centralizer (V : Set K))) :=
    (fun C : Subgroup Model.S => C.map d.actionEquiv.symm.toMonoidHom) '' F
  have he (C : Subgroup Model.S) :
      (C.map d.actionEquiv.symm.toMonoidHom).map d.actionEquiv.toMonoidHom = C := by
    rw [map_map]
    have hh : d.actionEquiv.toMonoidHom.comp d.actionEquiv.symm.toMonoidHom =
        MonoidHom.id Model.S := MonoidHom.ext (fun x => d.actionEquiv.apply_symm_apply x)
    rw [hh,map_id]
  refine ⟨E,?_,?_⟩
  · apply (map_injective (f := d.actionEquiv.toMonoidHom) d.actionEquiv.injective)
    rw [d.image_eq,← hF]
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      apply sSup_le
      rintro _ ⟨C,hC,rfl⟩
      apply map_le_iff_le_comap.mp
      rw [he]
      exact le_sSup hC
    · apply sSup_le
      intro C hC
      rw [← he C]
      exact map_mono (le_sSup (show C.map d.actionEquiv.symm.toMonoidHom ∈ E from ⟨C,hC,rfl⟩))
  · rintro B ⟨C,hC,rfl⟩
    obtain ⟨hc,hw,g,hg,hcg⟩ := hparts C hC
    have hBA : C.map d.actionEquiv.symm.toMonoidHom ≤ A.map (actionMap V) := by
      apply (map_le_map_iff_of_injective (f := d.actionEquiv.toMonoidHom) d.actionEquiv.injective).mp
      rw [he,d.image_eq]
      exact hw.1
    have hBe : IsElementaryTwo (C.map d.actionEquiv.symm.toMonoidHom) := by
      let := hc.2
      exact ⟨(map_eq_bot_iff_of_injective C d.actionEquiv.symm.injective).not.mpr hc.1,
        IsElementaryAbelian.map _⟩
    refine ⟨hBe,⟨hBA,?_⟩,?_⟩
    · rw [d.action_weight,d.action_weight,he,d.image_eq]
      simpa only [weight,d.fixed_finrank] using hw.2
    · obtain ⟨l,hl,hq⟩ := d.residual_lift ⟨g,hg⟩
      refine ⟨0,l,hl,?_⟩
      apply (map_le_map_iff_of_injective (f := d.actionEquiv.toMonoidHom) d.actionEquiv.injective).mp
      rw [he,d.image_eq,map_conjugate,d.D_image,hq]
      exact hcg

/-- The alpha decomposition and both Sylow conclusions on the same R,
retaining the full action kernel. -/
theorem baumann_conclusions
    (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q ≤ last)
    (hfrat : pResidual 2 K ⊓ centralizer (V : Set K) ≤ coreFrattini (pResidual 2 K)) :
    (pCore 2 (pResidual 2 K)).map (pResidual 2 K).subtype ≤ baumann d.R ∧
      thompsonAlpha d.R = (thompsonAlpha d.R ⊓ centralizer (pResidual 2 K : Set K)) ⊔
        (V ⊓ centralizer (elementaryAbelianMaxJ d.R : Set K)) ∧
      IsSylowSubgroupIn (baumann d.R ⊓ centralizer (V : Set K))
        ((pResidual 2 K ⊔ baumann d.R) ⊓ centralizer (V : Set K)) ∧
      (IsSylowSubgroupIn ((baumann d.R).map (actionMap V))
          ((pResidual 2 K).map (actionMap V) ⊔ (baumann d.R).map (actionMap V)) →
        IsSylowSubgroupIn (baumann d.R) (pResidual 2 K ⊔ baumann d.R)) := by
  apply baumann_of_sylow_preimage_cover V d.R d.D (d.family_AD hne hfrat)
    d.D_sylow (fun i => d.core ▸ d.D_core i) d.D_rank
    (fun A hA hn => d.equal_weight_cover A hA hn)
  have hs : Chapter1.IsSylowIn 2 (d.R ⊓ centralizer (V : Set K))
      (centralizer (V : Set K)) := d.kernel_centralizer ▸ d.kernel_sylow
  exact hs.restrict (inf_le_inf_right _ le_sup_right) inf_le_right

end SylowCoreAction
end Family

/-- B.2.19 on the five-dimensional core with the full kernel retained.
Only its intersection with R is required to be a Sylow subgroup. -/
public theorem full_point_baumann_of_kernel_sylow
    {H : Type*} [Group H] [Finite H]
    (V R : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
    (q : H →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q)
    (e : V ≃* Multiplicative (BinaryPermutation.core (Fin 6)))
    (he : ∀ g v, (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q g) (e v).toAdd)
    (hp : IsPGroup 2 R) (hVR : V ≤ R)
    (hcore : R ⊓ centralizer (V : Set H) = pCore 2 H)
    (hs : ∃ P : Sylow 2 q.ker, (P : Subgroup q.ker).map q.ker.subtype = R ⊓ q.ker)
    (hR : R.map q = ChapterB.Offenders.exceptional 6 (by decide))
    (hJ : ¬ (elementaryAbelianMaxJ R).map q ≤ ChapterB.Offenders.Six.last)
    (hfrat : pResidual 2 H ⊓ centralizer (V : Set H) ≤ coreFrattini (pResidual 2 H)) :
    (pResidual 2 H).pCoreIn 2 ≤ baumann R ∧
      thompsonAlpha R = (thompsonAlpha R ⊓ centralizer (pResidual 2 H : Set H)) ⊔
        (V ⊓ centralizer (elementaryAbelianMaxJ R : Set H)) ∧
      IsSylowSubgroupIn (baumann R ⊓ centralizer (V : Set H))
        ((pResidual 2 H ⊔ baumann R) ⊓ centralizer (V : Set H)) := by
  let d : SylowCoreAction V := ⟨q,hq,R,hp,hR,hVR,hcore,hs,e,he⟩
  have hh := d.baumann_conclusions hJ hfrat
  exact ⟨hh.1,hh.2.1,hh.2.2.1⟩

/-- Transport the Sylow-preimage Baumann argument along the original even
point conjugator, keeping both the module and the entire kernel. -/
public theorem conjugate_point_baumann_of_kernel_sylow
    {H : Type*} [Group H] [Finite H]
    (V R : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
    (q : H →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q)
    (e : V ≃* Multiplicative (BinaryPermutation.core (Fin 6)))
    (he : ∀ g v, (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q g) (e v).toAdd)
    (hp : IsPGroup 2 R) (hVR : V ≤ R)
    (hcore : R ⊓ centralizer (V : Set H) = pCore 2 H)
    (hs : ∃ P : Sylow 2 q.ker, (P : Subgroup q.ker).map q.ker.subtype = R ⊓ q.ker)
    (a : alternatingGroup (Fin 6))
    (hR : R.map q = Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
      (MulAut.conj a.val).toMonoidHom)
    (hJ : (elementaryAbelianMaxJ R).map q = R.map q)
    (hfrat : pResidual 2 H ⊓ centralizer (V : Set H) ≤ coreFrattini (pResidual 2 H)) :
    (pResidual 2 H).pCoreIn 2 ≤ baumann R ∧
      thompsonAlpha R = (thompsonAlpha R ⊓ centralizer (pResidual 2 H : Set H)) ⊔
        (V ⊓ centralizer (elementaryAbelianMaxJ R : Set H)) ∧
      IsSylowSubgroupIn (baumann R ⊓ centralizer (V : Set H))
        ((pResidual 2 H ⊔ baumann R) ⊓ centralizer (V : Set H)) := by
  let c := (MulAut.conj a.val⁻¹).toMonoidHom
  let q0 := c.comp q
  let e0 := e.trans (LinearMap.GeneralLinearGroup.toLinearEquiv
    (Model.rho.asGroupHom a.val⁻¹)).toAddEquiv.toMultiplicative
  have hq0 : Function.Surjective q0 := (MulAut.conj a.val⁻¹).surjective.comp hq
  have hk0 : q0.ker = q.ker :=
    MonoidHom.ker_comp_of_injective _ _ (MulAut.conj a.val⁻¹).injective
  have he0 (g : H) (v : V) : (e0 (MulAut.conjNormal g v)).toAdd =
      Model.rho (q0 g) (e0 v).toAdd := by
    change Model.rho a.val⁻¹ (e (MulAut.conjNormal g v)).toAdd =
      Model.rho (a.val⁻¹*q g*(a.val⁻¹)⁻¹) (Model.rho a.val⁻¹ (e v).toAdd)
    rw [he,←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul,
      inv_mul_cancel_right]
  have hR0 : R.map q0 = Model.E := by
    rw [show q0 = c.comp q from rfl,←map_map,hR,map_map]
    have hh : c.comp (MulAut.conj a.val).toMonoidHom = MonoidHom.id Model.S := by
      ext x
      simp [c,MulAut.conj_apply,mul_assoc]
    rw [hh,map_id,Model.pointCore_eq_exceptional]
  have hj : ¬ (elementaryAbelianMaxJ R).map q0 ≤ last := by
    rw [show q0 = c.comp q from rfl,←map_map,hJ,map_map]
    change ¬ R.map q0 ≤ last
    rw [hR0]
    intro hh
    have hc := Nat.card_le_card_of_injective (inclusion hh) (inclusion_injective _)
    rw [card_exceptional,card_last] at hc
    omega
  have hs0 : ∃ P : Sylow 2 q0.ker,
      (P : Subgroup q0.ker).map q0.ker.subtype = R ⊓ q0.ker := by
    rw [hk0]
    exact hs
  exact full_point_baumann_of_kernel_sylow V R q0 hq0 e0 he0 hp hVR hcore
    hs0 hR0 hj hfrat
end CFSG.Quasithin.ChapterC.AugmentationSixControl
