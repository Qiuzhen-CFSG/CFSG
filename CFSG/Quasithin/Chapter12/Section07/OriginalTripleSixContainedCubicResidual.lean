module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixScalarResidual
public import Theory.Representation.HexacodeAction.WeightFourVectorResidual
public import Theory.Representation.BinaryConjugationSection.Generation
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# The original cubic residual at the Sylow-fixed weight-four point

The pointwise stabilizer C_K(z) fixes the whole scalar point V1 and maps
onto its actual S4 vector stabilizer, with kernel in the original O2(K).
Its literal embedded two-residual is the non-scalar cubic piece L1.
It is normalized by the original T, fixes V1, has cubic quotient by its
own two-core, and generates the whole original U modulo V1 by commutators.

Source: Aschbacher--Smith12.7.2(5),12.7.15(4), printed pp.839,843.
No equality of conjugate closures in different local overgroups is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The literal non-scalar residual at the specified original element. -/
@[expose] def tripleSixWeightFourResidual (K : Subgroup G) (z : G) : Subgroup G :=
  (pResidual 2 (K ⊓ centralizer ({z} : Set G) : Subgroup G)).map
    (K ⊓ centralizer ({z} : Set G)).subtype

/-- The original chart maps L1 onto the literal model vector-stabilizer
two-residual, retaining its actor automorphism. -/
theorem tripleSixWeightFourResidual_image (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (z : U) :
    ((tripleSixWeightFourResidual K z).subgroupOf
      (K ⊓ centralizer ({(z:G)} : Set G))).map (tripleSixPointCentralizerProjection D a z)=
      pResidual 2 (Hexacode.fullWeightVectorStabilizer (tripleSixPointCoordinates D a z).toAdd) := by
  rw [show (tripleSixWeightFourResidual K z).subgroupOf
      (K ⊓ centralizer ({(z:G)} : Set G)) =
      pResidual 2 (K ⊓ centralizer ({(z:G)} : Set G) : Subgroup G) from
    comap_map_eq_self_of_injective (K ⊓ centralizer ({(z:G)} : Set G)).subtype_injective _,
    map_pResidual_of_surjective 2 _ (tripleSixPointCentralizerProjection_surjective D a z)]

/-- The unchanged original Sylow-fixed vector has weight four in the actual chart. -/
theorem tripleSix_sylow_fixed_weightFour (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G)) :
    hammingNorm (tripleSixPointCoordinates D a z).toAdd.val=4 := by
  let f := tripleSixPointCoordinates D a
  have h0 : (f z).toAdd ≠ 0 := by
    intro he
    exact hz (f.injective (show f z=f 1 from he.trans f.map_one.symm))
  have hodd : ¬ 2 ∣ (centralizer ({(z : G)} : Set G)).relIndex K := by
    obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K D.sylow_normalizes_component
    intro hi
    apply P.not_dvd_index
    apply hi.trans
    apply index_dvd_of_le
    rw [hP]
    exact fun k hk => hzT hk
  have hc := Hexacode.evenAction_orbit_card (f z).toAdd h0
  rw [tripleSixPoint_orbit_card D a z] at hc
  by_contra hn
  rw [if_neg hn] at hc
  exact hodd (hc ▸ (by norm_num : 2 ∣ 18))

private theorem residual_quotient_card {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (f : A →* B) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) :
    Nat.card (pResidual 2 A ⧸ pCore 2 (pResidual 2 A))=
      Nat.card (pResidual 2 B ⧸ pCore 2 (pResidual 2 B)) := by
  let R := pResidual 2 A
  let S := R.map f
  let g : R →* S := f.subgroupMap R
  have hg : Function.Surjective g := f.subgroupMap_surjective R
  have hgk : IsPGroup 2 g.ker := by
    rw [Subgroup.ker_subgroupMap]
    exact hk.comap_subtype
  let q := (QuotientGroup.mk' (pCore 2 S)).comp g
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hg
  have hqk : q.ker=pCore 2 R := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact g.comap_pCore_of_ker_isPGroup hg hgk
  let e : (R ⧸ pCore 2 R) ≃* (S ⧸ pCore 2 S) :=
    (QuotientGroup.quotientMulEquivOfEq hqk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have hS : S=pResidual 2 B := map_pResidual_of_surjective 2 f hf
  exact (Nat.card_congr e.toEquiv).trans (by rw [hS])

private def chartSection (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) :
    BinaryConjugationSection K U ⊥
      (Hexacode.evenAction.comp (a.groupEquiv.toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 K)))) where
  section_le := D.le_component
  kernel_le := bot_le
  normalized := D.normalizes
  coordinates := (tripleSixPointCoordinates D a).toMonoidHom
  onto := (tripleSixPointCoordinates D a).surjective
  kernel_eq := by
    rw [bot_subgroupOf]
    exact ((tripleSixPointCoordinates D a).toMonoidHom.ker_eq_bot_iff).mpr
      (tripleSixPointCoordinates D a).injective
  equivariant k u := by
    have h := tripleSixPointCoordinates_conjugate D a k u
    have hs : (tripleSixPointCoordinates D a).symm (Multiplicative.ofAdd
        (Hexacode.evenAction (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k))
          (tripleSixPointCoordinates D a u).toAdd)) =
        ⟨(k : G)*u*(k : G)⁻¹,
          (mem_normalizer_iff.mp (D.normalizes k.property) u).mp u.property⟩ := Subtype.ext h
    have he := congrArg (tripleSixPointCoordinates D a) hs
    rw [MulEquiv.apply_symm_apply] at he
    exact (congrArg Multiplicative.toAdd he).symm

private theorem residual_commutator (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G)) :
    U=⁅U,tripleSixWeightFourResidual K z⁆ ⊔ tripleSixPoint D a z := by
  let s := chartSection D a
  let C := K ⊓ centralizer ({(z : G)} : Set G)
  let L := tripleSixWeightFourResidual K z
  let V := tripleSixPoint D a z
  let q := tripleSixPointCentralizerProjection D a z
  let v := (tripleSixPointCoordinates D a z).toAdd
  let R := (pResidual 2 (Hexacode.fullWeightVectorStabilizer v)).map
    (Hexacode.fullWeightVectorStabilizer v).subtype
  have hLK : L≤K := (map_subtype_le _).trans inf_le_left
  have himage : (L.subgroupOf C).map q=pResidual 2 (Hexacode.fullWeightVectorStabilizer v) :=
    tripleSixWeightFourResidual_image D a z
  have hspan : subspaceCommutator Hexacode.evenAction ⊤ R ≤ s.image ⁅U,L⁆ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,w,_,rfl⟩
    obtain ⟨r,hr,rfl⟩ := hg
    obtain ⟨c,hc,hcr⟩ := show r ∈ (L.subgroupOf C).map q by rw [himage]; exact hr
    have hm := s.coinvariants_le_image_commutator L hLK
      (Coinvariants.sub_mem_ker
        (ρ := (Hexacode.evenAction.comp (a.groupEquiv.toMonoidHom.comp
          (QuotientGroup.mk' (pCore 2 K)))).comp (inclusion hLK)) (⟨c.val,hc⟩ : L) w)
    change Hexacode.evenAction
      (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) ⟨c.val,hLK hc⟩)) w-w ∈ _ at hm
    have he : a.groupEquiv (QuotientGroup.mk' (pCore 2 K) ⟨c.val,hLK hc⟩)=r.val :=
      congrArg Subtype.val hcr
    rwa [he] at hm
  have hpoint : (Submodule.span Hexacode.F {v}).restrictScalars (ZMod 2) ≤ s.image V := by
    intro w hw
    let u := (tripleSixPointCoordinates D a).symm (Multiplicative.ofAdd w)
    refine ⟨u,?_,?_⟩
    · exact ⟨u,by
        change (tripleSixPointCoordinates D a u).toAdd ∈ Submodule.span Hexacode.F {v}
        simpa [u] using hw,rfl⟩
    · exact congrArg Multiplicative.toAdd ((tripleSixPointCoordinates D a).apply_symm_apply _)
  have hfull : s.image (⁅U,L⁆ ⊔ V)=⊤ := by
    apply top_unique
    rw [←Hexacode.weightFourVectorResidual_commutator_sup_point v (tripleSix_sylow_fixed_weightFour D a z hz hzT)]
    exact sup_le (hspan.trans (s.image_mono le_sup_left)) (hpoint.trans (s.image_mono le_sup_right))
  apply le_antisymm
  · simpa using s.le_sup_kernel_of_image_top (⁅U,L⁆ ⊔ V) hfull
  · exact sup_le (le_normalizer_iff_commutator_le_left.mp (hLK.trans D.normalizes))
      (tripleSixPoint_properties D a z hz).2.1

/-- The genuine original L1 is T-invariant, two-perfect, pointwise fixes V1,
has cubic two-core quotient, and moves the whole original module modulo V1.
It is distinct from the scalar residual X. -/
theorem original_tripleSix_weightFour_cubic_residual (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G)) :
    let L1 := tripleSixWeightFourResidual K z
    let V1 := tripleSixPoint D a z
    L1 ≤ K ⊓ centralizer (V1 : Set G) ∧
    (T : Subgroup G) ≤ normalizer (L1 : Set G) ∧
    IsPPerfect 2 L1 ∧ Nat.card (L1 ⧸ pCore 2 L1)=3 ∧
    U=⁅U,L1⁆ ⊔ V1 ∧ L1≠tripleSixScalarResidual K := by
  let C := K ⊓ centralizer ({(z : G)} : Set G)
  let L1 := tripleSixWeightFourResidual K z
  let V1 := tripleSixPoint D a z
  let q := tripleSixPointCentralizerProjection D a z
  let v := (tripleSixPointCoordinates D a z).toAdd
  have hp := tripleSixPoint_properties D a z hz
  have hLC : L1≤C := map_subtype_le _
  have hfix : L1≤centralizer (V1 : Set G) := hLC.trans hp.2.2.2.2
  have hnormC : (T : Subgroup G)≤normalizer (C : Set G) :=
    (le_inf D.sylow_normalizes_component (hzT.trans (centralizer ({(z:G)} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hnorm : (T : Subgroup G)≤normalizer (L1 : Set G) :=
    hnormC.trans (normalizer_le_normalizer_characteristic_image C (pResidual 2 C))
  have hcard : Nat.card (L1 ⧸ pCore 2 L1)=3 := by
    let e := (pResidual 2 C).equivMapOfInjective C.subtype C.subtype_injective
    have hk : IsPGroup 2 q.ker := by
      rw [tripleSixPointCentralizerProjection_ker]
      exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
    have hc := residual_quotient_card q (tripleSixPointCentralizerProjection_surjective D a z) hk
    rw [Hexacode.weightFourVectorResidual_quotient_card v (tripleSix_sylow_fixed_weightFour D a z hz hzT)] at hc
    exact (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).symm.trans hc
  refine ⟨le_inf (hLC.trans inf_le_left) hfix,hnorm,isPPerfect_embedded_pResidual 2 C,
    hcard,residual_commutator D a z hz hzT,?_⟩
  intro he
  have hzX : (z:G) ∈ U ⊓ centralizer (tripleSixScalarResidual K : Set G) := by
    refine ⟨z.property,?_⟩
    rw [←he]
    exact (le_centralizer_iff.mp hfix) hp.1
  rw [tripleSixScalarResidual_fixed_eq_bot D a] at hzX
  exact hz (Subtype.ext hzX)

/-- The original cubic residual's own two-core quotient is the cyclic group
of order three. -/
def tripleSixWeightFourResidualQuotientEquiv (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G)) :
    (tripleSixWeightFourResidual K z ⧸ pCore 2 (tripleSixWeightFourResidual K z)) ≃*
      Multiplicative (ZMod 3) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact mulEquivOfPrimeCardEq
    (original_tripleSix_weightFour_cubic_residual D a z hz hzT).2.2.2.1 (by simp)

end CFSG.Quasithin.Chapter12.Section07
