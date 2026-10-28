module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRemainingRadicals
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRemainingRadicals
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicThompsonSelectors
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixCorePlane
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits

/-!
# The quadratic Thompson family in the remaining cubic branches

For the Borel image, the unique maximum-order small mover is the preimage
of the plane radical inside the original edge subgroup. A subgroup of the
six-letter Borel of order at least eight with fixed codimension at most two
must be that plane radical: its fixed space supplies a nonzero duad other
than the Borel's distinguished duad, and a sixteen-element stabilizer table
forces the plane. Maximality then recovers the entire preimage, using
ker(projection) intersect R = Q; the full projection kernel remains E.

The same plane is quadratic on both the natural module and the entire
augmentation cover. The quadratic certificate is checked on the six coordinate
vectors, and linearity supplies all vectors. Faithful edge charts transport
the unique family, relative indices eight and two, fixed index four and
quadratic commutator identity to every original Borel edge. In the plane
branch the previously identified maximum mover is the whole edge, also
quadratic. Thus both remaining branches supply the singleton alternative
of MS93 (5.4)(a), including its order-eight image and relative normality.

The whole-core and literal C.1.32 applications retain both covers, the
original cubic projection and the two remaining radical images. The plane
and Borel critical-path contradictions, exceptional exhaustion, natural
exhaustion and both final reconstruction outcomes remain with this owner.
The private imports reuse the existing edge charts and cubic movement
bounds; no natural replacement graph is identified with the cubic graph.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), Section 5.0 and (5.4), printed pp.912,915; Aschbacher--Smith
C.1.31--32, printed pp.135--136, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits
open CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
namespace BorelCalculation
local notation "Borel" => Theory.SpecificGroups.SymmetricSix.borel
private def words (i : Fin 16) : S := MulAut.conj flagRelabel (sylowWords i)
private theorem words_in_borel : ∀ i, words i ∈ Borel := by decide
private theorem words_injective : Function.Injective words := by decide
private theorem words_complete (g : S) (hg : g ∈ Borel) : ∃ i, words i = g := by
  let f : Fin 16 → Borel := fun i => ⟨words i,words_in_borel i⟩
  have hi : Function.Injective f := fun i j he => words_injective (congrArg Subtype.val he)
  have hc : Nat.card (Fin 16) = Nat.card Borel := by rw [Nat.card_fin,borel_order]
  obtain ⟨i,hi⟩ := (Nat.bijective_iff_injective_and_card f).mpr ⟨hi,hc⟩ |>.2 ⟨g,hg⟩
  exact ⟨i,congrArg Subtype.val hi⟩
private def fixedWords (d : Duad) : Finset (Fin 16) :=
  Finset.univ.filter fun i => (duadSet d).image (words i) = duadSet d
private theorem fixed_words_cert : ∀ d : Duad, d ≠ 0 →
    8 ≤ (fixedWords d).card → ∀ i ∈ fixedWords d,
      ∃ j : Fin 8, dWords j = words i := by decide

private theorem large_duad_fixer_le_plane (A : Subgroup S) (hA : A ≤ Borel)
    (hc : 8 ≤ Nat.card A) (d : Duad) (hd : d ≠ 0)
    (hf : ∀ a ∈ A, a • d = d) : A ≤ D := by
  have hm (a : A) : ∃ i : ↥(fixedWords d), words i = a := by
    obtain ⟨i,hi⟩ := words_complete a (hA a.property)
    refine ⟨⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩,hi⟩
    rw [hi,←duadSet_smul,hf a a.property]
  let f : A → ↥(fixedWords d) := fun a => Classical.choose (hm a)
  have he (a : A) : words (f a) = a := Classical.choose_spec (hm a)
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    rw [←he a,←he b,hab]
  have hcount : 8 ≤ (fixedWords d).card := by
    have hh := hc.trans (Nat.card_le_card_of_injective f hinj)
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hh
  intro a ha
  obtain ⟨j,hj⟩ := fixed_words_cert d hd hcount (f ⟨a,ha⟩) (f ⟨a,ha⟩).property
  rw [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq]
  exact (mem_disjointTranspositions_iff (3 : Fin 4) a).mpr ⟨j,hj.trans (he ⟨a,ha⟩)⟩

private theorem large_small_codim_eq_plane (A : Subgroup S) (hA : A ≤ Borel)
    (hc : 8 ≤ Nat.card A) (hf : fixedCodim (naturalRepresentation (Fin 6)) A ≤ 2) :
    A = D := by
  classical
  let F := fixedSpace (naturalRepresentation (Fin 6)) A
  have hd : 2 ≤ Module.finrank (ZMod 2) F := by
    have hh := fixedCodim_add_finrank (naturalRepresentation (Fin 6)) A
    rw [finrank_natural_even (Fin 6) (by decide)] at hh
    change fixedCodim (naturalRepresentation (Fin 6)) A + Module.finrank (ZMod 2) F = 4 at hh
    omega
  have hcard : 4 ≤ Nat.card F := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hd
  have hex : ∃ v : F, (v : natural (Fin 6)) ≠ 0 ∧ (v : natural (Fin 6)) ≠ naturalDuad 0 := by
    by_contra! hn
    let f : F → Bool := fun v => if (v : natural (Fin 6)) = 0 then false else true
    have hi : Function.Injective f := by
      intro v w he
      by_cases hv : (v : natural (Fin 6)) = 0 <;>
        by_cases hw : (w : natural (Fin 6)) = 0
      · exact Subtype.ext (hv.trans hw.symm)
      · simp only [f,hv,hw,ite_true,ite_false] at he
        cases he
      · simp only [f,hv,hw,ite_true,ite_false] at he
        cases he
      · exact Subtype.ext ((hn v hv).trans (hn w hw).symm)
    have hh := Nat.card_le_card_of_injective f hi
    have hb : Nat.card Bool = 2 := by simp
    omega
  obtain ⟨v,hv,hv0⟩ := hex
  obtain ⟨d,hde⟩ := natural_cases v hv
  have hdn : d ≠ 0 := by rintro rfl; exact hv0 hde.symm
  have hfix (a : S) (ha : a ∈ A) : a • d = d := by
    apply naturalDuad_injective
    rw [←naturalDuad_map,hde]
    exact v.property ⟨a,ha⟩
  exact eq_of_le_of_card_ge (large_duad_fixer_le_plane A hA hc d hdn hfix) (D_card ▸ hc)
private theorem plane_le_borel : D ≤ Borel := by
  rw [D,closure_le]
  rintro a (rfl | rfl | rfl)
  · exact (show swap01 ∈ Borel by decide)
  · exact (show swap23 ∈ Borel by decide)
  · exact (show swap45 ∈ Borel by decide)

private theorem large_small_codim_eq_conjugate_plane (A : Subgroup S) (u : S)
    (hA : A ≤ (Borel).map (MulAut.conj u).toMonoidHom)
    (hc : 8 ≤ Nat.card A) (hf : fixedCodim (naturalRepresentation (Fin 6)) A ≤ 2) :
    A = D.map (MulAut.conj u).toMonoidHom := by
  have hback (H : Subgroup S) :
      (H.map (MulAut.conj u).toMonoidHom).map (MulAut.conj u⁻¹).toMonoidHom = H :=
    conjBy_inv H u
  have hb : A.map (MulAut.conj u⁻¹).toMonoidHom ≤ Borel :=
    (map_mono hA).trans_eq (hback Borel)
  have he := large_small_codim_eq_plane _ hb
    (by rwa [card_map_of_injective (MulAut.conj u⁻¹).injective])
    (by rwa [fixedCodim_map_conj])
  have hh := congrArg (Subgroup.map (MulAut.conj u).toMonoidHom) he
  exact (conjBy_inv' A u).symm.trans hh

private theorem core_plane_quadratic : IsQuadratic (coreRepresentation (Fin 6)) D := by
  have hcert : ∀ i j : Fin 8, ∀ k : Fin 6, ∀ c : ZMod 2,
      representation (Fin 6) (dWords i)
          (representation (Fin 6) (dWords j) (Pi.single k c)-Pi.single k c) =
        representation (Fin 6) (dWords j) (Pi.single k c)-Pi.single k c := by decide
  intro a ha b hb v
  rw [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq] at ha hb
  obtain ⟨i,rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) a).mp ha
  obtain ⟨j,rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) b).mp hb
  have he : (representation (Fin 6) (dWords i)).comp
      (representation (Fin 6) (dWords j)-LinearMap.id) =
        representation (Fin 6) (dWords j)-LinearMap.id := by
    apply LinearMap.pi_ext
    intro k c
    exact hcert i j k c
  exact Subtype.ext (LinearMap.congr_fun he v.val)

private theorem natural_plane_quadratic : IsQuadratic (naturalRepresentation (Fin 6)) D :=
  quadratic_of_equivariant_surjection (coreRepresentation (Fin 6))
    (naturalRepresentation (Fin 6)) (coreToNatural (Fin 6)) coreToNatural_surjective
    coreToNatural_equivariant D core_plane_quadratic

private theorem quadratic_conjugate {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) S Y) (A : Subgroup S) (hq : IsQuadratic ρ A) (u : S) :
    IsQuadratic ρ (A.map (MulAut.conj u).toMonoidHom) := by
  have hinv (v : Y) : ρ u⁻¹ (ρ u v) = v := by
    rw [← Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  have hright (v : Y) : ρ u (ρ u⁻¹ v) = v := by
    rw [← Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
  change ρ (u*a*u⁻¹) (ρ (u*b*u⁻¹) v-v) = ρ (u*b*u⁻¹) v-v
  have hh := congrArg (ρ u) (hq a ha b hb (ρ u⁻¹ v))
  simpa only [map_mul,Module.End.mul_apply,map_sub,hinv,hright] using hh

private theorem cover_plane_quadratic {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) S Y)
    (hρ : SixCover.IsNaturalOrCore ρ (MonoidHom.id S)) (u : S) :
    IsQuadratic ρ (D.map (MulAut.conj u).toMonoidHom) := by
  apply quadratic_conjugate ρ D _ u
  rcases hρ with ⟨E,hE⟩ | ⟨E,hE⟩
  · intro a ha b hb v
    apply E.injective
    simpa only [hE,map_sub,MonoidHom.id_apply] using natural_plane_quadratic a ha b hb (E v)
  · intro a ha b hb v
    apply E.injective
    simpa only [hE,map_sub,MonoidHom.id_apply] using core_plane_quadratic a ha b hb (E v)

end BorelCalculation

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk

/-- The plane preimage inside the original radical, retaining its intersection
with the cubic projection kernel. -/
@[expose] def borelPlane (u : S) : Subgroup M :=
  Rg ⊓ (D.map (MulAut.conj u).toMonoidHom).comap π

include h e hz hk in
theorem borelPlane_image (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    (borelPlane h e hz hk u).map π = D.map (MulAut.conj u).toMonoidHom := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    exact hx.2
  · intro y hy
    have hT : y ∈ (Rg).map π := hR.symm ▸ map_mono BorelCalculation.plane_le_borel hy
    obtain ⟨x,hx,rfl⟩ := hT
    exact mem_map_of_mem π ⟨hx,hy⟩

include h e hz hk in
theorem borelPlane_core_le (u : S) : pCore 2 M ≤ borelPlane h e hz hk u := by
  rw [borelPlane,←cubic_radical_projection_kernel h e hz hk]
  exact le_inf inf_le_right (inf_le_left.trans (ker_le_comap _ _))

include h e hz hk in
/-- The plane preimage has relative orders eight and two, and fixes index
four on either full moving cover. -/
theorem borelPlane_indices (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    (pCore 2 M).relIndex (borelPlane h e hz hk u) = 8 ∧
      (borelPlane h e hz hk u).relIndex Rg = 2 ∧
      (centralizer (borelPlane h e hz hk u : Set M)).relIndex W = 4 ∧
      Nat.card (borelPlane h e hz hk u) = Nat.card (pCore 2 M) * 8 := by
  let F := borelPlane h e hz hk u
  have hi : (pCore 2 M).relIndex F = 8 := by
    rw [←CubicAction.permutation_image_card_of_two h e hz hk F
      (h.relative_radical.isPGroup.to_le inf_le_left),borelPlane_image h e hz hk u hR,
      card_map_of_injective (MulAut.conj u).injective,D_card]
  have hT : (pCore 2 M).relIndex Rg = 16 := by
    rw [←CubicAction.permutation_image_card_of_two h e hz hk Rg
      h.relative_radical.isPGroup,hR,card_map_of_injective (MulAut.conj u).injective,borel_order]
  have hrel : F.relIndex Rg = 2 := by
    have hh := relIndex_mul_relIndex (pCore 2 M) F Rg
      (borelPlane_core_le h e hz hk u) inf_le_left
    rw [hi,hT] at hh
    omega
  have hfix : (centralizer (F : Set M)).relIndex W = 4 := by
    have hh := cubic_cover_movement_bounds h e hz hk F
    rw [borelPlane_image h e hz hk u hR,fixedCodim_map_conj,fixedCodim_map_conj,
      CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq,fixedCodim_D.2.2.2,fixedCodim_D.2.2.1] at hh
    omega
  refine ⟨hi,hrel,hfix,?_⟩
  have hh := relIndex_mul_relIndex (⊥ : Subgroup M) (pCore 2 M) F bot_le
    (borelPlane_core_le h e hz hk u)
  simpa only [relIndex_bot_left,hi] using hh.symm

include h e hz hk in
/-- Every actor mapping into the literal plane radical is quadratic on the
entire moving cover, including its possible central line. -/
theorem plane_image_quadratic (A : Subgroup M) (u : S)
    (hA : A.map π ≤ D.map (MulAut.conj u).toMonoidHom) :
    ⁅⁅W,A⁆,A⁆ = ⊥ := by
  let := h.relative_normal
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)
  let ρ := NormalElementaryQuotient.representation W π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)
  have hact (g : M) (v : Additive W) : ((ρ (π g) v).toMul : M) = g*v.toMul*g⁻¹ :=
    NormalElementaryQuotient.representation_apply W π
      (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk) g v
  have hquad := BorelCalculation.cover_plane_quadratic ρ (moved_subgroup_cover_model h e hz hk) u
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rw [commutator_comm W A]
  apply commutator_le.mpr
  intro a ha w hw
  let v : Additive W := Additive.ofMul ⟨w,hw⟩
  let z := ρ (π a) v-v
  have hzval : (z.toMul : M) = ⁅a,w⁆ := by
    dsimp only [z]
    rw [toMul_sub,Subgroup.coe_div,div_eq_mul_inv,hact]
    rfl
  intro b hb
  have he := congrArg (fun y : Additive W => (y.toMul : M))
    (hquad (π b) (hA (mem_map_of_mem π hb)) (π a) (hA (mem_map_of_mem π ha)) v)
  change ((ρ (π b) z).toMul : M) = z.toMul at he
  rw [hact,hzval] at he
  exact mul_inv_eq_iff_eq_mul.mp he

include h e hz hk in
private theorem borel_maximal_mover (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup M) (hAT : A ≤ Rg)
    (hsmall : (centralizer (A : Set M)).relIndex W ≤ 4)
    (hmax : Nat.card (borelPlane h e hz hk u) ≤ Nat.card A) :
    A = borelPlane h e hz hk u := by
  let Q₀ := pCore 2 M
  have hcard : Nat.card A = Nat.card (Q₀ ⊓ A : Subgroup M) * Nat.card (A.map π) := by
    rw [CubicAction.permutation_image_card_of_two h e hz hk A
      (h.relative_radical.isPGroup.to_le hAT)]
    simpa only [relIndex_bot_left,inf_relIndex_right] using
      (relIndex_mul_relIndex (⊥ : Subgroup M) (Q₀ ⊓ A) A bot_le inf_le_right).symm
  have hlarge : 8 ≤ Nat.card (A.map π) := by
    have hh : Nat.card Q₀ * 8 ≤ Nat.card Q₀ * Nat.card (A.map π) := by
      calc
        _ = Nat.card (borelPlane h e hz hk u) := (borelPlane_indices h e hz hk u hR).2.2.2.symm
        _ ≤ Nat.card A := hmax
        _ = _ := hcard
        _ ≤ _ := Nat.mul_le_mul_right _ (card_le_of_le inf_le_left)
    exact Nat.le_of_mul_le_mul_left hh (Nat.card_pos (α := Q₀))
  have hcodim : fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    exact (cubic_cover_movement_bounds h e hz hk A).1.trans hsmall
  have him := BorelCalculation.large_small_codim_eq_conjugate_plane (A.map π) u
    ((map_mono hAT).trans_eq hR) hlarge hcodim
  have hAF : A ≤ borelPlane h e hz hk u :=
    le_inf hAT (map_le_iff_le_comap.mp him.le)
  exact eq_of_le_of_card_ge hAF hmax

include h e hz hk in
/-- On a Borel edge the source family is a singleton. Its join is the
literal index-two plane preimage, with fixed index four on both covers. -/
theorem borel_edge_maximal_offenders (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hc : color Rg c = false) (hct : Adjacent Rg c t) :
    ∃ J : Subgroup (FreeAmalgam Rg),
      edgeMaximalOffenders c t = {J} ∧ edgeOffenderJoin c t = J ∧
      Q Rg c ≤ J ∧ J ≤ Q Rg t ∧ J.relIndex (Q Rg t) = 2 ∧
      (Q Rg c).relIndex J = 8 ∧
      (centralizer (J : Set (FreeAmalgam Rg))).relIndex (U Rg c) = 4 ∧
      ⁅⁅U Rg c,J⁆,J⁆ = ⊥ := by
  obtain ⟨i,hi,hir,hiR,hiQ,hiW⟩ := remaining_edge_coordinates h e hz hc hct
  let F := borelPlane h e hz hk u
  let J := F.map i
  have hJQ : J ≤ Q Rg t := hiR ▸ map_mono (show F ≤ Rg from inf_le_left)
  have hQJ : Q Rg c ≤ J := hiQ ▸ map_mono (borelPlane_core_le h e hz hk u)
  have hnum := borelPlane_indices h e hz hk u hR
  have hidx : (Q Rg c).relIndex J = 8 := by
    rw [←hiQ,relIndex_map_map_of_injective _ _ hi]
    exact hnum.1
  have hfix : (centralizer (J : Set (FreeAmalgam Rg))).relIndex (U Rg c) = 4 := by
    rw [←hiW,←inf_relIndex_right,inf_comm,map_inf_centralizer_of_injective i hi,
      relIndex_map_map_of_injective _ _ hi,inf_relIndex_left]
    exact hnum.2.2.1
  have hsmall : edgeSmallMover c t J := ⟨hJQ,by rw [hfix,hidx]; decide,by rw [hfix]⟩
  have hle (A : Subgroup (FreeAmalgam Rg)) (hA : edgeSmallMover c t A)
      (hcard : Nat.card J ≤ Nat.card A) : A = J := by
    have hAi : A ≤ i.range := hA.1.trans (hiR ▸ map_le_range i Rg)
    have hAm : (A.comap i).map i = A := map_comap_eq_self hAi
    have hAT : A.comap i ≤ Rg := by
      apply (map_le_map_iff_of_injective hi).mp
      rw [hAm,hiR]
      exact hA.1
    have hfixA : (centralizer (A.comap i : Set M)).relIndex W ≤ 4 := by
      have hh := hA.2.2
      rw [←hAm,←hiW,←inf_relIndex_right,inf_comm,map_inf_centralizer_of_injective i hi,
        relIndex_map_map_of_injective _ _ hi,inf_relIndex_left] at hh
      exact hh
    have hcA : Nat.card F ≤ Nat.card (A.comap i) := by
      change Nat.card (F.map i) ≤ Nat.card A at hcard
      rw [←hAm] at hcard
      simpa only [card_map_of_injective hi] using hcard
    have he := borel_maximal_mover h e hz hk u hR (A.comap i) hAT hfixA hcA
    rw [←hAm,he]
  have hmax : edgeMaximalOffenders c t = {J} := by
    ext A
    constructor
    · intro hA
      exact Set.mem_singleton_iff.mpr (hle A hA.1 (hA.2 J hsmall))
    · rintro rfl
      refine ⟨hsmall,fun A hA => ?_⟩
      by_cases hh : Nat.card J ≤ Nat.card A
      · rw [hle A hA hh]
      · omega
  refine ⟨J,hmax,?_,hQJ,hJQ,?_,hidx,hfix,?_⟩
  · rw [edgeOffenderJoin,hmax,sSup_singleton]
  · rw [←hiR,relIndex_map_map_of_injective _ _ hi]
    exact hnum.2.1
  · rw [←hiW,show J = F.map i from rfl,←map_commutator,←map_commutator,
      plane_image_quadratic h e hz hk F u (borelPlane_image h e hz hk u hR).le,Subgroup.map_bot]

include h e hz hk in
/-- Both remaining radical images have a unique maximum-order small mover
on every actual edge. Its order-eight image is quadratic on the full cover. -/
theorem remaining_edge_thompson (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hc : color Rg c = false) (hct : Adjacent Rg c t) :
    let J := edgeOffenderJoin c t
    edgeMaximalOffenders c t = {J} ∧ Q Rg c ≤ J ∧ J ≤ Q Rg t ∧
      (J.relIndex (Q Rg t) = 1 ∨ J.relIndex (Q Rg t) = 2) ∧
      Q Rg t ≤ normalizer (J : Set (FreeAmalgam Rg)) ∧
      (Q Rg c).relIndex J = 8 ∧
      (centralizer (J : Set (FreeAmalgam Rg))).relIndex (U Rg c) = 4 ∧
      ⁅⁅U Rg c,J⁆,J⁆ = ⊥ := by
  dsimp only
  rcases hR with hplane | hborel
  · have hh := plane_edge_maximal_offenders h e hz hk u hplane hc hct
    rw [plane_edgeOffenderJoin_eq h e hz hk u hplane hc hct]
    have ht : color Rg t = true := by
      have hn := adjacent_color_ne Rg hct
      rw [hc] at hn
      cases he : color Rg t <;> simp_all
    refine ⟨hh.1,Q_le_adjacent_h Rg ht hct,le_rfl,Or.inl (relIndex_self _),
      (Q Rg t).le_normalizer,hh.2.2,hh.2.1,?_⟩
    obtain ⟨i,hi,hir,hiR,hiQ,hiW⟩ := remaining_edge_coordinates h e hz hc hct
    rw [←hiW,←hiR,←map_commutator,←map_commutator,
      plane_image_quadratic h e hz hk Rg u hplane.le,Subgroup.map_bot]
  · obtain ⟨J,hmax,hJ,hQJ,hJT,hi,hQi,hfix,hquad⟩ :=
      borel_edge_maximal_offenders h e hz hk u hborel hc hct
    rw [hJ]
    exact ⟨hmax,hQJ,hJT,Or.inr hi,
      (normal_subgroupOf_iff_le_normalizer hJT).mp (normal_of_index_eq_two hi),hQi,hfix,hquad⟩

omit hk in
include h e hz in
/-- Whole-core assembly supplies the actual unique, quadratic Thompson
family in both remaining branches of source (5.4)(a). The original cubic
projection, both covers, and the later distance contradiction are retained. -/
theorem coreExhaustion_or_cubic_quadratic_thompson :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) = D.map (MulAut.conj u).toMonoidHom ∨
          (Rg).map (CubicAction.projection h e hz hk) = borel.map (MulAut.conj u).toMonoidHom) ∧
        ∀ c t : Vertex Rg, color Rg c = false → Adjacent Rg c t →
          let J := edgeOffenderJoin c t
          edgeMaximalOffenders c t = {J} ∧ Q Rg c ≤ J ∧ J ≤ Q Rg t ∧
            (J.relIndex (Q Rg t) = 1 ∨ J.relIndex (Q Rg t) = 2) ∧
            Q Rg t ≤ normalizer (J : Set (FreeAmalgam Rg)) ∧
            (Q Rg c).relIndex J = 8 ∧
            (centralizer (J : Set (FreeAmalgam Rg))).relIndex (U Rg c) = 4 ∧
            ⁅⁅U Rg c,J⁆,J⁆ = ⊥ := by
  rcases coreExhaustion_or_cubic_plane_or_borel h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hR⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,hR,
      fun c t hc hct => remaining_edge_thompson h e hz hk u hR hc hct⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the remaining source Thompson-family
calculation, without assuming that either image is already excluded. -/
theorem rankTwo_or_cubic_quadratic_thompson :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) = D.map (MulAut.conj u).toMonoidHom ∨
          (Rg).map (CubicAction.projection h e hz hk) = borel.map (MulAut.conj u).toMonoidHom) ∧
        ∀ c t : Vertex Rg, color Rg c = false → Adjacent Rg c t →
          let J := edgeOffenderJoin c t
          edgeMaximalOffenders c t = {J} ∧ Q Rg c ≤ J ∧ J ≤ Q Rg t ∧
            (J.relIndex (Q Rg t) = 1 ∨ J.relIndex (Q Rg t) = 2) ∧
            Q Rg t ≤ normalizer (J : Set (FreeAmalgam Rg)) ∧
            (Q Rg c).relIndex J = 8 ∧
            (centralizer (J : Set (FreeAmalgam Rg))).relIndex (U Rg c) = 4 ∧
            ⁅⁅U Rg c,J⁆,J⁆ = ⊥ :=
  (coreExhaustion_or_cubic_quadratic_thompson h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
