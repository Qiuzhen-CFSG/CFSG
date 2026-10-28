module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.PlaneMovement
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.CompatibleFlags.Geometry
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CorePlaneGeometry
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreCrossing
public import Theory.GroupAction.FourPerfectOrbit
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.RankFiveNaturalSixModel

/-!
# The original rank-five natural-six source flag

The first intersection residual is two-perfect and generates the source
four-group by commutators. Its three nonidentity elements consequently form
one orbit, so their full-core coordinates have equal weights. After aligning
an actual component Sylow subgroup, the six-letter flag geometry forces all
three weights to be four and determines the plane and its central point.

One relabelling changes both the full-core coordinates and the normalizer
actor. The original conjugation action and exact alternating component image
are retained. The final application derives movement, Sylow placement,
invariance and both dimensions from the original Chapter 14 source data.
Only the actual alternating-block and order-32 branch identifications remain.

Source: Aschbacher–Smith, 14.6.10(5), printed pp.1029–1030, and B.3.
-/

@[expose] public noncomputable section
open Subgroup BinaryPermutation Module Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry
open Chapter13.Section08.TransvectionParabolic.Marking.CompatibleFlags
open Chapter13.Section08.TransvectionParabolic
variable {G : Type*} [Group G] [Finite G]
abbrev C := core (Fin 6)
def sourceImage (W : Subgroup G) (E : W ≃* Multiplicative C) (B : Subgroup G) :
    Submodule (ZMod 2) C :=
  AddSubgroup.toZModSubmodule 2 ((B.subgroupOf W).map E.toMonoidHom).toAddSubgroup'

omit [Finite G] in
private theorem sourceImage_card (W : Subgroup G) (E : W ≃* Multiplicative C)
    (B : Subgroup G) (hB : B ≤ W) : Nat.card (sourceImage W E B) = Nat.card B := by
  let D := (B.subgroupOf W).map E.toMonoidHom
  have he : Nat.card (sourceImage W E B) = Nat.card D :=
    Nat.card_congr {
      toFun v := ⟨Multiplicative.ofAdd v.val,v.property⟩
      invFun v := ⟨v.val.toAdd,v.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  exact he.trans ((card_map_of_injective E.injective).trans
    (Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv))

omit [Finite G] in
private theorem sourceImage_finrank (W : Subgroup G) (E : W ≃* Multiplicative C)
    (B : Subgroup G) (hB : B ≤ W) (n : ℕ) (hc : Nat.card B = 2 ^ n) :
    finrank (ZMod 2) (sourceImage W E B) = n := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := sourceImage W E B)
  rw [Nat.card_zmod] at he
  exact he.symm.trans ((sourceImage_card W E B hB).trans hc)

variable (K W : Subgroup G) (E : W ≃* Multiplicative C)
    (f : K →* Equiv.Perm (Fin 6))
    (hKW : K ≤ normalizer (W : Set G))
    (he : ∀ k : K, ∀ v : W,
      (E ⟨k.val * v.val * k.val⁻¹,
        le_normalizer_iff.mp hKW k k.property v v.property⟩).toAdd =
          coreRepresentation (Fin 6) (f k) (E v).toAdd)
include he
omit [Finite G] in
private theorem sourceImage_invariant (A B : Subgroup G)
    (_hAK : A ≤ K) (hAB : A ≤ normalizer (B : Set G)) :
    ∀ x ∈ (A.subgroupOf K).map f, ∀ v ∈ sourceImage W E B,
      coreRepresentation (Fin 6) x v ∈ sourceImage W E B := by
  rintro _ ⟨a,ha,rfl⟩ v ⟨v',hv',hh⟩
  refine ⟨⟨a.val * v'.val * a.val⁻¹,
    le_normalizer_iff.mp hKW a a.property v' v'.property⟩,
    le_normalizer_iff.mp hAB a ha v' hv',?_⟩
  apply Multiplicative.toAdd.injective
  change _ = coreRepresentation (Fin 6) (f a) v
  exact (he a v').trans (congrArg (coreRepresentation (Fin 6) (f a)) (congrArg Multiplicative.toAdd hh))

omit [Finite G] in
private theorem sourceImage_weights (A B : Subgroup G)
    (hAK : A ≤ K) (hAB : A ≤ normalizer (B : Set G))
    (hBW : B ≤ W) (hBc : Nat.card B = 4)
    (hA : IsPPerfect 2 A) (hm : ⁅B,A⁆ = B) :
    ∀ u ∈ sourceImage W E B, u ≠ 0 → ∀ v ∈ sourceImage W E B, v ≠ 0 →
      OrbitModels.weight u = OrbitModels.weight v := by
  let P := sourceImage W E B
  let τ := (coreRepresentation (Fin 6)).comp (f.comp (inclusion hAK))
  have hi (a : A) : ∀ v ∈ P, τ a v ∈ P :=
    sourceImage_invariant K W E f hKW he A B hAK hAB _ ⟨inclusion hAK a,a.property,rfl⟩
  let σ := Representation.subrepresentation τ P hi
  have hd : finrank (ZMod 2) P = 2 := sourceImage_finrank W E B hBW 2 hBc
  have hnontriv : ∃ a, σ a ≠ 1 := by
    by_contra ht
    push Not at ht
    have hc : A ≤ centralizer (B : Set G) := by
      apply le_centralizer_iff.mpr
      intro b hb a ha
      let bW : W := ⟨b,hBW hb⟩
      have hbP : (E bW).toAdd ∈ P := ⟨bW,hb,rfl⟩
      have hh := congrArg Subtype.val (LinearMap.congr_fun (ht ⟨a,ha⟩) ⟨_,hbP⟩)
      change coreRepresentation (Fin 6) (f ⟨a,hAK ha⟩) (E bW).toAdd = (E bW).toAdd at hh
      rw [←he] at hh
      have hc : a * b * a⁻¹ = b := congrArg Subtype.val
        (E.injective (Multiplicative.toAdd.injective hh))
      exact mul_inv_eq_iff_eq_mul.mp hc
    have hz : B = ⊥ := by
      rw [←hm,commutator_comm,commutator_eq_bot_iff_le_centralizer]
      exact hc
    have := hBc
    rw [hz,card_bot] at this
    omega
  intro u hu hu0 v hv hv0
  obtain ⟨a,ha⟩ := Representation.nonzero_orbit_of_twoPerfect_plane hA hd σ hnontriv
    ⟨u,hu⟩ (fun h => hu0 (congrArg Subtype.val h))
    ⟨v,hv⟩ (fun h => hv0 (congrArg Subtype.val h))
  have hh : coreRepresentation (Fin 6) (f (inclusion hAK a)) u = v := congrArg Subtype.val ha
  exact (cover_weight_map _ _).symm.trans (congrArg OrbitModels.weight hh)

/-- The same six-letter relabelling marks both subgroups, using movement by
an actual two-perfect subgroup to identify the full-core lift. -/
theorem exists_core_flag_marking
    (hfull : alternatingGroup (Fin 6) ≤ f.range)
    (B Z A : Subgroup G) (hBW : B ≤ W) (hZB : Z ≤ B)
    (hBc : Nat.card B = 4) (hZc : Nat.card Z = 2)
    (hAK : A ≤ K) (hAB : A ≤ normalizer (B : Set G))
    (hA : IsPPerfect 2 A) (hm : ⁅B,A⁆ = B)
    (S : Sylow 2 K)
    (hSB : (S : Subgroup K).map K.subtype ≤ normalizer (B : Set G))
    (hSZ : (S : Subgroup K).map K.subtype ≤ normalizer (Z : Set G)) :
    ∃ g : Equiv.Perm (Fin 6), g ∈ f.range ∧
      T0 ≤ (S : Subgroup K).map ((MulAut.conj g⁻¹).toMonoidHom.comp f) ∧
      (sourceImage W E B).map (coreRepresentation (Fin 6) g⁻¹) = CoreCrossing.plane ∧
      (sourceImage W E Z).map (coreRepresentation (Fin 6) g⁻¹) =
        Submodule.span (ZMod 2) {CoreCrossing.z} := by
  let Q := S.mapSurjective f.rangeRestrict_surjective
  obtain ⟨g,hg⟩ := NaturalGeometry.exists_conjugate_T0_le f.range hfull Q
  have halign : T0.map (MulAut.conj g.val).toMonoidHom ≤ (S : Subgroup K).map f := by
    simpa only [Q,Sylow.coe_mapSurjective,Subgroup.map_map,
      MonoidHom.subtype_comp_rangeRestrict] using hg
  let r := coreRepresentation (Fin 6)
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (r.asGroupHom g.val⁻¹)
  let P := sourceImage W E B
  let ZP := sourceImage W E Z
  have hi (X : Subgroup G)
      (hSX : (S : Subgroup K).map K.subtype ≤ normalizer (X : Set G)) :
      ∀ a ∈ T0, ∀ v ∈ (sourceImage W E X).map (r g.val⁻¹),
        r a v ∈ (sourceImage W E X).map (r g.val⁻¹) := by
    apply invariant_after_alignment r _ _ g.val halign
    rintro _ ⟨a,ha,rfl⟩ v hv
    exact sourceImage_invariant K W E f hKW he ((S : Subgroup K).map K.subtype)
      X (map_subtype_le _) hSX _
      ⟨a,mem_map_of_mem _ ha,rfl⟩ v hv
  have hd : finrank (ZMod 2) (P.map (r g.val⁻¹)) = 2 :=
    (e.finrank_map_eq P).trans (sourceImage_finrank W E B hBW 2 hBc)
  have hw : ∀ v ∈ P.map (r g.val⁻¹), v ≠ 0 → OrbitModels.weight v = 4 := by
    apply CorePlaneGeometry.plane_weight_four _ hd (hi B hSB)
    rintro u ⟨u',hu',rfl⟩ hu v ⟨v',hv',rfl⟩ hv
    change OrbitModels.weight (r g.val⁻¹ u') = OrbitModels.weight (r g.val⁻¹ v')
    rw [cover_weight_map,cover_weight_map]
    exact sourceImage_weights K W E f hKW he A B hAK hAB hBW hBc hA hm
      u' hu' (fun h => hu (by rw [h,map_zero]))
      v' hv' (fun h => hv (by rw [h,map_zero]))
  have hgen (U : Submodule (ZMod 2) C) (hU : U ≤ P.map (r g.val⁻¹)) :
      U = Submodule.span (ZMod 2) {v | v ∈ U ∧ OrbitModels.weight v = 4} := by
    apply le_antisymm
    · intro v hv
      by_cases hz : v = 0
      · exact hz ▸ Submodule.zero_mem _
      · exact Submodule.subset_span ⟨hv,hw v (hU hv) hz⟩
    · exact Submodule.span_le.mpr (fun _ h => h.1)
  have hZP : ZP ≤ P := by
    rintro v ⟨w,hw,rfl⟩
    exact ⟨w,hZB hw,rfl⟩
  have hp := cover_plane_unique _ hd (hi B hSB) (hgen _ le_rfl)
  have hz := cover_point_unique (ZP.map (r g.val⁻¹))
    ((e.finrank_map_eq ZP).trans (sourceImage_finrank W E Z (hZB.trans hBW) 1 hZc))
    (hi Z hSZ) (hgen _ (Submodule.map_mono hZP))
  have hzword : OrbitModels.point = CoreCrossing.z := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  have hwword : OrbitModels.seed = CoreCrossing.w := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  refine ⟨g.val,g.property,?_,?_,?_⟩
  · intro t ht
    obtain ⟨a,ha,he⟩ := halign (mem_map_of_mem _ ht)
    refine ⟨a,ha,?_⟩
    change g.val⁻¹ * f a * (g.val⁻¹)⁻¹ = t
    rw [he]
    change g.val⁻¹ * (g.val * t * g.val⁻¹) * (g.val⁻¹)⁻¹ = t
    group
  · simpa only [P,r,CoreCrossing.plane,OrbitModels.plane,hzword,hwword] using hp
  · simpa only [ZP,e,r,OrbitModels.pointSpace,hzword] using hz

end CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix

namespace CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix
open ChapterC Theory.SpecificGroups.SymmetricSix.BinaryFlags
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem sourceImage_relabel (W : Subgroup G)
    (E : W ≃* Multiplicative C) (B : Subgroup G) (g : Equiv.Perm (Fin 6)) :
    sourceImage W (E.trans (LinearEquiv.ofBijective (coreRepresentation (Fin 6) g)
      ((coreRepresentation (Fin 6)).apply_bijective g)).toAddEquiv.toMultiplicative) B =
      (sourceImage W E B).map (coreRepresentation (Fin 6) g) := by
  apply le_antisymm
  · rintro v ⟨w,hw,rfl⟩
    exact ⟨(E w).toAdd,⟨w,hw,rfl⟩,rfl⟩
  · rintro v ⟨w,⟨u,hu,rfl⟩,rfl⟩
    exact ⟨u,hu,rfl⟩

/-- Full block coordinates can be chosen with the original plane and point
canonical, while preserving the action of the whole ambient normalizer. -/
theorem exists_marked_source_coordinates (K B Z A : Subgroup G)
    (hblock : IsAlternatingBlock K 6) (hW : Nat.card (sourceModule K) = 32)
    (hBW : B ≤ sourceModule K) (hZB : Z ≤ B)
    (hBc : Nat.card B = 4) (hZc : Nat.card Z = 2)
    (hAK : A ≤ K) (hAB : A ≤ normalizer (B : Set G))
    (hA : IsPPerfect 2 A) (hm : ⁅B,A⁆ = B)
    (S : Sylow 2 K)
    (hSB : (S : Subgroup K).map K.subtype ≤ normalizer (B : Set G))
    (hSZ : (S : Subgroup K).map K.subtype ≤ normalizer (Z : Set G)) :
    ∃ E : sourceModule K ≃* Multiplicative C,
    ∃ f : normalizer (K : Set G) →* Equiv.Perm (Fin 6),
      (∀ (n : normalizer (K : Set G)) (v : sourceModule K)
        (hv : n.val * v.val * n.val⁻¹ ∈ sourceModule K),
        (E ⟨n.val * v.val * n.val⁻¹,hv⟩).toAdd =
          coreRepresentation (Fin 6) (f n) (E v).toAdd) ∧
      (K.subgroupOf (normalizer (K : Set G))).map f = alternatingGroup (Fin 6) ∧
      NaturalGeometry.T0 ≤ ((S : Subgroup K).map (inclusion K.le_normalizer)).map f ∧
      sourceImage (sourceModule K) E B = CoreCrossing.plane ∧
      sourceImage (sourceModule K) E Z = Submodule.span (ZMod 2) {CoreCrossing.z} := by
  obtain ⟨E,f,he,hfull⟩ := source_core_coordinates K hblock hW
  let fK := f.comp (inclusion K.le_normalizer)
  have hfK : fK.range = alternatingGroup (Fin 6) := by
    change (f.comp (inclusion K.le_normalizer)).range = _
    rw [MonoidHom.range_comp,Subgroup.inclusion_range]
    exact hfull
  have hKW : K ≤ normalizer (sourceModule K : Set G) :=
    K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  have heK (k : K) (v : sourceModule K) :
      (E ⟨k.val * v.val * k.val⁻¹,le_normalizer_iff.mp hKW k k.property v v.property⟩).toAdd =
        coreRepresentation (Fin 6) (fK k) (E v).toAdd := he (inclusion K.le_normalizer k) v _
  obtain ⟨g,hg,hs,hp,hz⟩ := exists_core_flag_marking K (sourceModule K) E fK hKW heK
    hfK.ge B Z A hBW hZB hBc hZc hAK hAB hA hm S hSB hSZ
  let r := coreRepresentation (Fin 6)
  let e := (LinearEquiv.ofBijective (r g⁻¹) (r.apply_bijective g⁻¹)).toAddEquiv.toMultiplicative
  let E' := E.trans e
  let f' := (MulAut.conj g⁻¹).toMonoidHom.comp f
  refine ⟨E',f',?_,?_,?_,?_,?_⟩
  · intro n v hv
    change r g⁻¹ (E ⟨n.val*v.val*n.val⁻¹,hv⟩).toAdd =
      r (g⁻¹ * f n * (g⁻¹)⁻¹) (r g⁻¹ (E v).toAdd)
    rw [he]
    dsimp only [r]
    simp only [← Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]
  · change (K.subgroupOf (normalizer (K : Set G))).map
      ((MulAut.conj g⁻¹).toMonoidHom.comp f) = _
    rw [←map_map,hfull]
    exact conjugate_alternating g⁻¹
  · simpa only [f',fK,map_map,MonoidHom.comp_assoc] using hs
  · exact (sourceImage_relabel (sourceModule K) E B g⁻¹).trans hp
  · exact (sourceImage_relabel (sourceModule K) E Z g⁻¹).trans hz
end CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix

namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))

include hG hempty hM hunique hmany hcard e hab H hH hu hindex hmove hproduct hU3 hlocal


/-- The original rank-five parabolic plane and central point admit full-core
coordinates with no additional flag or orbit hypotheses. -/
theorem source_parabolic_rankFive_coordinates
    (I : Subgroup G)
    (hI : I ∈ outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)
    (hout : ¬ I ⊓ M ≤ Mc)
    (K : Subgroup G) (hKI : K ≤ I) (hKN : (K.subgroupOf I).Normal)
    (hfirst : (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ≤ K)
    (hblock : ChapterC.IsAlternatingBlock K 6)
    (hW : Nat.card (RankFiveNaturalSix.sourceModule K) = 32)
    (hVW : localModule T M ≤ RankFiveNaturalSix.sourceModule K) :
    ∃ E : RankFiveNaturalSix.sourceModule K ≃* Multiplicative (core (Fin 6)),
    ∃ f : normalizer (K : Set G) →* Equiv.Perm (Fin 6),
      (∀ (n : normalizer (K : Set G)) (v : RankFiveNaturalSix.sourceModule K)
        (hv : n.val * v.val * n.val⁻¹ ∈ RankFiveNaturalSix.sourceModule K),
        (E ⟨n.val * v.val * n.val⁻¹,hv⟩).toAdd =
          coreRepresentation (Fin 6) (f n) (E v).toAdd) ∧
      (K.subgroupOf (normalizer (K : Set G))).map f = alternatingGroup (Fin 6) ∧
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.T0 ≤
        (((T : Subgroup G) ⊓ K).subgroupOf (normalizer (K : Set G))).map f ∧
      RankFiveNaturalSix.sourceImage (RankFiveNaturalSix.sourceModule K) E
        (localModule T M) = Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreCrossing.plane ∧
      RankFiveNaturalSix.sourceImage (RankFiveNaturalSix.sourceModule K) E
        (centralInvolutions T) = Submodule.span (ZMod 2)
          {Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreCrossing.z} := by
  have hSyl := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI).1
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl hKI
    hKN.isSubnormal
  have hST : (S : Subgroup K).map K.subtype ≤ (T : Subgroup G) :=
    hS.le.trans (inf_le_left.trans inf_le_left)
  have hTV : (T : Subgroup G) ≤ normalizer (localModule T M : Set G) :=
    hM.1.2.trans (le_normalizer_conjugateSpanBy _ _)
  have hTZ : (T : Subgroup G) ≤ normalizer (centralInvolutions T : Set G) :=
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T)).trans
      (Subgroup.centralizer_le_normalizer _)
  obtain ⟨E,f,he,hfull,halign,hplane,hpoint⟩ :=
    RankFiveNaturalSix.exists_marked_source_coordinates K (localModule T M)
    (centralInvolutions T)
    ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype) hblock hW hVW (le_conjugateSpanBy _ _) hcard
    (plane_centralInvolutions_card T M hM.1.2 hcard e) hfirst
    (((map_subtype_le _).trans inf_le_left).trans
      ((sourceResidual_le M Mc).trans (le_normalizer_conjugateSpanBy _ M)))
    (isPPerfect_embedded_pResidual 2 _)
    (source_parabolic_plane_moved hG T hempty hM hunique hmany hcard e hab H hH
      u hu hindex hmove hproduct hU3 hlocal I hI hout) S
    (hST.trans hTV) (hST.trans hTZ)
  refine ⟨E,f,he,hfull,halign.trans ?_,hplane,hpoint⟩
  apply map_mono
  rintro n ⟨s,hs,rfl⟩
  exact ⟨hST (mem_map_of_mem _ hs),s.property⟩
end CFSG.Quasithin.Chapter14.Section06
