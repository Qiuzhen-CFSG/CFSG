module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Action
public import CFSG.Quasithin.ChapterB.Section02.Baumann.PreimageGenerators
public import Stellmacher.ElementaryAbelianMaxGlobal
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The actual mixed-plane family for the S6 point radical

The inverse images of two even-conjugate mixed planes have the full two-rank
of the point radical: the natural module has no strong offenders there.
A maximum elementary image larger than the point transposition contains a
mixed plane of equal weight. B.2.8 replacement lifts it to a maximum subgroup;
component conjugation puts that image in the first displayed plane. The two
Thompson images are consequently the two planes generating S6.

Source: Aschbacher--Smith C.1.37, printed pp.142--143; B.2.8 and B.2.19.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.NaturalSixControl
open Subgroup Stellmacher
open scoped IsMulCommutative
open ChapterB ChapterB.BaumannArgument
open Representation.BinaryOffender
open ChapterB.Offenders.Six
universe u
variable {K : Type u} [Group K] {V : Subgroup K} [V.Normal] [IsElementaryAbelian 2 V]
namespace NaturalAction
variable (d : NaturalAction V)

/-- The full inverse image of the finite point radical. -/
def R : Subgroup K := Model.E.comap d.q

/-- The two mixed-plane inverse images in B.2.19. -/
noncomputable def D (i : Fin 2) : Subgroup K := (Model.root i).comap d.q

omit [IsElementaryAbelian 2 V] in
theorem kernel_le_R : d.q.ker ≤ d.R := MonoidHom.ker_le_comap d.q Model.E

omit [IsElementaryAbelian 2 V] in
theorem D_kernel (i : Fin 2) : d.q.ker ≤ d.D i :=
  MonoidHom.ker_le_comap d.q (Model.root i)

omit [IsElementaryAbelian 2 V] in
theorem R_two : IsPGroup 2 d.R := by
  have he : IsPGroup 2 Model.E :=
    (ChapterB.Offenders.Six.isElementaryTwo_exceptional).2.isPGroup 2 _
  exact he.comap_of_ker_isPGroup d.q (d.kernel.symm ▸ pCore_isPGroup)

omit [IsElementaryAbelian 2 V] in
theorem R_image : d.R.map d.q = Model.E :=
  map_comap_eq_self_of_surjective d.onto _

omit [IsElementaryAbelian 2 V] in
theorem D_image (i : Fin 2) : (d.D i).map d.q = Model.root i :=
  map_comap_eq_self_of_surjective d.onto _

theorem module_le_R : V ≤ d.R :=
  V.le_centralizer.trans (d.kernel_centralizer ▸ d.kernel_le_R)

omit [IsElementaryAbelian 2 V] in
theorem D_zero_le_R : d.D 0 ≤ d.R := comap_mono plus_le_exceptional

variable [Finite K]

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
  exact Model.rank_le_fixedCodim (map_le_iff_le_comap.mpr hA) hq

private theorem rank_mono {A B : Subgroup K} (h : A ≤ B) : twoRank A ≤ twoRank B :=
  Nat.log_mono_right (elementaryAbelianMaxOrder_le_and_j_le_of_eq A B h).1

theorem centralizer_rank : twoRank d.q.ker = twoRank d.R := by
  have hr := (centralizer_rank_and_alpha V d.R d.module_le_R d.noStrongOffenders).1
  rwa [← d.kernel_centralizer,inf_eq_right.mpr d.kernel_le_R] at hr

theorem D_zero_rank : twoRank (d.D 0) = twoRank d.R := by
  apply le_antisymm (rank_mono d.D_zero_le_R)
  rw [← d.centralizer_rank]
  exact rank_mono (d.D_kernel 0)

omit [Finite K] [IsElementaryAbelian 2 V] in
theorem preimage_conjugate (A : Subgroup Model.S) (g : K) :
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
theorem D_conjugate (i : Fin 2) :
    ∃ l ∈ pResidual 2 K, (d.D 0).map (MulAut.conj l).toMonoidHom = d.D i := by
  fin_cases i
  · refine ⟨1,one_mem _,?_⟩
    have hi : (MulAut.conj (1 : K)).toMonoidHom = MonoidHom.id K := by ext x;simp
    rw [hi,map_id]
    rfl
  · obtain ⟨l,hl,hq⟩ := d.residual_lift ⟨Model.conjugator,Model.conjugator_even⟩
    refine ⟨l,hl,?_⟩
    change (plus.comap d.q).map _ = Model.secondPlane.comap d.q
    rw [d.preimage_conjugate,hq]
    rfl

theorem D_rank (i : Fin 2) : twoRank (d.D i) = twoRank d.R := by
  obtain ⟨l,_,hl⟩ := d.D_conjugate i
  rw [← hl,twoRank_map_equiv]
  exact d.D_zero_rank

omit [Finite K] in
private theorem map_conjugate {H : Type*} [Group H] (q : K →* H)
    (A : Subgroup K) (g : K) :
    (A.map (MulAut.conj g).toMonoidHom).map q =
      (A.map q).map (MulAut.conj (q g)).toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  ext x
  simp

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
  have ha : A.map d.q ≤ Model.E := map_le_iff_le_comap.mpr hA.1
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
  refine ⟨C',map_le_iff_le_comap.mp hmap0.le,hC'.2.1.map _,?_,hmap0⟩
  exact (card_map_of_injective (MulAut.conj l).injective).trans
    (card_eq_elementaryAbelianMaxOrder d.R C hC')

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

end NaturalAction

namespace SourceData
variable {L : Subgroup K} [L.Normal] {T : Sylow 2 K} (d : SourceData L V T) [Finite K]

/-- The original point-parabolic two-core has no strong offenders. -/
theorem radical_noStrongOffenders : NoStrongOffenders V d.R := by
  have he : d.canonicalAction.R = d.R := d.R_eq_comap.symm
  rw [← he]
  exact d.canonicalAction.noStrongOffenders

end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl
